#include "qemu/osdep.h"
#include "qapi/error.h"
#include "hw/pci/pci.h"
#include "hw/pci/msi.h"
#include "hw/pci/msix.h"
#include "hw/pci/pcie.h"
#include "qemu/error-report.h"
#include "qemu/module.h"
#include "hw/core/qdev-properties.h"
#include "bhyve-internal.h"
#include "bhyve-passthru.h"

#include <sys/ioctl.h>
#include <sys/pciio.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>

#ifndef rounddown2
#define rounddown2(x, y) ((x) & ~((y) - 1))
#endif
#ifndef roundup2
#define roundup2(x, y) (((x) + (y) - 1) & ~((y) - 1))
#endif

/*
 * NVIDIA GPU quirk (from Corvin Köhne / Beckhoff):
 * NVIDIA GPUs mirror their PCI config space into MMIO at BAR0 + 0x88000.
 * The guest driver reads config registers from there instead of using
 * PCI config cycles. We must intercept these accesses and return the
 * emulated config values, otherwise the guest sees stale/wrong data.
 */
#define NVIDIA_PCI_VENDOR       0x10DE
#define NVIDIA_CFG_MIRROR_OFF   0x88000
#define NVIDIA_CFG_MIRROR_LEN   0x1000  /* PCIe extended config space: 4KB */

/*
 * Track active MSI vectors for passthrough devices.
 * The IRR scrubber in bhyve-all.c must NOT clear these vectors,
 * otherwise MSI interrupts from physical devices get lost.
 * Up to 16 passthrough devices, each with one MSI vector tracked.
 */
#define BHYVE_PASSTHRU_MSI_MAX  16
volatile uint8_t bhyve_passthru_msi_vectors[BHYVE_PASSTHRU_MSI_MAX] = {0};
static int bhyve_passthru_msi_count = 0;

struct BhyvePassthruBarContext {
    BhyvePassthruState *s;
    int bar_idx;
};

/* Forward declarations — used in NVIDIA quirk BAR read/write */
static bool bhyve_passthru_is_emulated_reg(BhyvePassthruState *s, uint32_t offset);
static bool bhyve_passthru_should_forward_write(BhyvePassthruState *s, uint32_t offset, int len);
static void bhyve_passthru_write_config(PCIDevice *pci_dev, uint32_t address, uint32_t val, int len);

static uint32_t host_read_config(int fd, const struct pcisel *sel, long reg, int width)
{
    struct pci_io pi;
    memset(&pi, 0, sizeof(pi));
    pi.pi_sel = *sel;
    pi.pi_reg = reg;
    pi.pi_width = width;
    if (ioctl(fd, PCIOCREAD, &pi) < 0) {
        return 0;
    }
    return pi.pi_data;
}

static void host_write_config(int fd, const struct pcisel *sel, long reg, int width, uint32_t data)
{
    struct pci_io pi;
    memset(&pi, 0, sizeof(pi));
    pi.pi_sel = *sel;
    pi.pi_reg = reg;
    pi.pi_width = width;
    pi.pi_data = data;
    ioctl(fd, PCIOCWRITE, &pi);
}

static uint64_t bhyve_passthru_bar_read(void *opaque, hwaddr addr, unsigned size)
{
    struct BhyvePassthruBarContext *b = opaque;
    BhyvePassthruState *s = b->s;
    int bar_idx = b->bar_idx;

    /* NVIDIA quirk: intercept PCI config mirror at BAR0+0x88000.
     *
     * Corvin's approach: read LIVE from the physical device (PCIOCREAD),
     * not from cache. The GPU updates its own config registers during
     * driver init — cached values go stale and break NvKmsKapiDevice.
     *
     * Emulated registers (BARs, MSI, COMMAND) come from QEMU's config;
     * everything else comes from the physical device in real time.
     */
    if (s->is_nvidia_gpu && bar_idx == 0 &&
        addr >= NVIDIA_CFG_MIRROR_OFF &&
        addr < NVIDIA_CFG_MIRROR_OFF + NVIDIA_CFG_MIRROR_LEN) {
        uint64_t cfg_off = addr - NVIDIA_CFG_MIRROR_OFF;
        if (cfg_off < 256 && bhyve_passthru_is_emulated_reg(s, cfg_off)) {
            /* Emulated reg — return QEMU's value */
            uint32_t val = 0;
            for (unsigned i = 0; i < size && (cfg_off + i) < 256; i++) {
                val |= (uint32_t)PCI_DEVICE(s)->config[cfg_off + i] << (i * 8);
            }
            return val;
        }
        /* Non-emulated reg — read LIVE from physical device */
        return host_read_config(s->pcifd, &s->sel, cfg_off, size);
    }

    /*
     * BAR read fallback — PCIOCBARIO blocks after PPT assignment.
     * For passthrough, real BAR accesses go directly through EPT
     * (set up by vm_map_pptdev_mmio in update_bars). This callback
     * is only hit for unmapped regions or before EPT mapping is active.
     */
    static int bar_read_count = 0;
    if (bar_read_count < 20) {
        bar_read_count++;
    }
    return 0xFFFFFFFF;
}

static void bhyve_passthru_bar_write(void *opaque, hwaddr addr, uint64_t val, unsigned size)
{
    struct BhyvePassthruBarContext *b = opaque;
    BhyvePassthruState *s = b->s;
    int bar_idx = b->bar_idx;

    /* NVIDIA quirk: intercept PCI config mirror writes at BAR0+0x88000.
     *
     * nvidia.ko and GSP may write config registers (including MSI-X enable,
     * MSI control) through this mirror instead of standard PCI config cycles.
     * We must route these through bhyve_passthru_write_config() so QEMU's
     * MSI-X/MSI state machines are notified and vm_setup_pptdev_msix() is
     * called to set up IOMMU interrupt remapping. Without this, nvidia.ko
     * enables MSI-X in the mirror but QEMU never sees it, no IOMMU remapping
     * is set up, and the GPU test interrupt never arrives → NV_ERR_IRQ_NOT_FIRING.
     *
     * Standard PCI config space (offset < 256): route through the full config
     * write path so QEMU's emulated registers and MSI-X machinery are updated.
     * Extended config space (256–4095): update cache and forward to hardware.
     */
    if (s->is_nvidia_gpu && bar_idx == 0 &&
        addr >= NVIDIA_CFG_MIRROR_OFF &&
        addr < NVIDIA_CFG_MIRROR_OFF + NVIDIA_CFG_MIRROR_LEN) {
        uint64_t cfg_off = addr - NVIDIA_CFG_MIRROR_OFF;
        if (cfg_off < 256) {
            /* Route through standard config write: updates QEMU state, triggers
             * MSI-X notifiers, sets up IOMMU remapping via vm_setup_pptdev_msix. */
            bhyve_passthru_write_config(PCI_DEVICE(s), (uint32_t)cfg_off, (uint32_t)val, (int)size);
        } else {
            /* Extended config space: update cache and forward to hardware */
            for (unsigned i = 0; i < size && (cfg_off + i) < 4096; i++) {
                s->host_config[cfg_off + i] = (val >> (i * 8)) & 0xFF;
            }
            host_write_config(s->pcifd, &s->sel, cfg_off, size, val);
        }
        return;
    }

    /*
     * BAR write fallback — PCIOCBARIO blocks after PPT assignment.
     * Real BAR writes go through EPT (vm_map_pptdev_mmio).
     * This callback is only hit for unmapped regions — safe to ignore.
     */
    (void)val;
}

static const MemoryRegionOps bhyve_passthru_bar_ops = {
    .read = bhyve_passthru_bar_read,
    .write = bhyve_passthru_bar_write,
    .endianness = DEVICE_LITTLE_ENDIAN,
    .valid = {
        .min_access_size = 1,
        .max_access_size = 4,
    },
    .impl = {
        .min_access_size = 1,
        .max_access_size = 4,
    },
};

static int bhyve_passthru_msix_vector_use(PCIDevice *pci_dev, unsigned int vector, MSIMessage msg)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);
    fprintf(stderr, "bhyve-passthru: MSIX vector_use dev=%d/%d/%d vec=%u addr=0x%lx data=0x%x\n",
            s->host_bus, s->host_slot, s->host_func, vector,
            (unsigned long)msg.address, msg.data);
    fflush(stderr);
    int err = vm_setup_pptdev_msix(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func,
                                   vector, msg.address, msg.data, 0);
    if (err) {
        fprintf(stderr, "bhyve-passthru: vm_setup_pptdev_msix vector %u FAILED: err=%d errno=%d (%s)\n",
                vector, err, errno, strerror(errno));
        fflush(stderr);
        /* Return 0 to avoid QEMU abort — MSI-X may not work but we get diagnostics */
        return 0;
    }
    fprintf(stderr, "bhyve-passthru: vm_setup_pptdev_msix vector %u OK\n", vector);
    fflush(stderr);
    return 0;
}

static void bhyve_passthru_msix_vector_release(PCIDevice *pci_dev, unsigned int vector)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);
    int err = vm_setup_pptdev_msix(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func,
                                   vector, 0, 0, 1);
    if (err) {
        error_report("bhyve-passthru: vm_setup_pptdev_msix vector %u release failed: %d", vector, err);
    }
}

/*
 * Map or unmap NVIDIA BAR0 through EPT, leaving "holes" (unmapped) for the
 * sub-regions that QEMU must trap and emulate: the PCI config mirror
 * (0x88000) and — if MSI-X lives on BAR0 — the MSI-X table. Accesses to the
 * holes fall through to bhyve_passthru_bar_read/write; the gaps between holes
 * are mapped straight through. Centralising this avoids the previous triple-
 * duplicated, error-prone inline split logic (a wrong split freezes the host).
 */
static void bhyve_passthru_bar0_remap(BhyvePassthruState *s, uint64_t gpa,
                                      uint64_t hpa, uint64_t size, bool do_map)
{
    struct { uint64_t off, len; } ex[2];
    int n = 0;

    /* config mirror — always excluded for NVIDIA BAR0 */
    ex[n].off = rounddown2((uint64_t)NVIDIA_CFG_MIRROR_OFF, 4096);
    ex[n].len = roundup2((uint64_t)NVIDIA_CFG_MIRROR_LEN, 4096);
    n++;

    /* MSI-X table — only if it lives on BAR0 */
    if (msix_present(PCI_DEVICE(s)) && s->msix_table_bar_nr == 0) {
        uint64_t toff = rounddown2(s->msix_table_offset, 4096);
        uint64_t tlen = roundup2((s->msix_table_offset - toff) +
                                 (uint64_t)s->msix_entries_nr * 16, 4096);
        ex[n].off = toff;
        ex[n].len = tlen;
        n++;
    }

    /* The excluded ranges are constructed in ascending offset order
     * (0x88000 < 0x300000 < MSI-X table). Map/unmap the gaps between them. */
    uint64_t cur = 0;
    for (int k = 0; k < n; k++) {
        if (ex[k].off >= size) {
            break;
        }
        uint64_t exend = ex[k].off + ex[k].len;
        if (exend > size) {
            exend = size;
        }
        if (ex[k].off > cur) {
            uint64_t len = ex[k].off - cur;
            if (do_map) {
                vm_map_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot,
                                   s->host_func, gpa + cur, len, hpa + cur);
            } else {
                vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot,
                                     s->host_func, gpa + cur, len);
            }
        }
        if (exend > cur) {
            cur = exend;
        }
    }
    if (cur < size) {
        uint64_t len = size - cur;
        if (do_map) {
            vm_map_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot,
                               s->host_func, gpa + cur, len, hpa + cur);
        } else {
            vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot,
                                 s->host_func, gpa + cur, len);
        }
    }
}

static void bhyve_passthru_update_bars(BhyvePassthruState *s)
{
    PCIDevice *pci_dev = PCI_DEVICE(s);
    for (int i = 0; i < PCI_NUM_REGIONS; i++) {
        PCIIORegion *r = &pci_dev->io_regions[i];
        uint64_t gpa = r->addr;
        uint64_t size = s->bars[i].size;
        uint64_t hpa = s->bars[i].hpa;

        if (gpa == PCI_BAR_UNMAPPED || size == 0) {
            if (s->bars[i].mapped) {
                uint64_t old_gpa = s->bars[i].gpa;
                if (s->is_nvidia_gpu && i == 0 &&
                    size > NVIDIA_CFG_MIRROR_OFF + NVIDIA_CFG_MIRROR_LEN) {
                    bhyve_passthru_bar0_remap(s, old_gpa, 0, size, false);
                } else if (msix_present(pci_dev) && s->msix_table_bar_nr == i) {
                    uint32_t table_offset = rounddown2(s->msix_table_offset, 4096);
                    uint32_t table_size = s->msix_table_offset - table_offset;
                    table_size += s->msix_entries_nr * 16;
                    table_size = roundup2(table_size, 4096);
                    uint64_t remaining = size - table_offset - table_size;
                    if (table_offset > 0) {
                        vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa, table_offset);
                    }
                    if (remaining > 0) {
                        vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa + table_offset + table_size, remaining);
                    }
                } else {
                    vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa, size);
                }
                s->bars[i].mapped = false;
            }
            continue;
        }

        if (r->type & PCI_BASE_ADDRESS_SPACE_IO) {
            continue;
        }

        bool should_map = (pci_dev->config[PCI_COMMAND] & PCI_COMMAND_MEMORY);

        if (s->bars[i].mapped && (!should_map || s->bars[i].gpa != gpa)) {
            uint64_t old_gpa = s->bars[i].gpa;
            if (s->is_nvidia_gpu && i == 0 &&
                size > NVIDIA_CFG_MIRROR_OFF + NVIDIA_CFG_MIRROR_LEN) {
                bhyve_passthru_bar0_remap(s, old_gpa, 0, size, false);
            } else if (msix_present(pci_dev) && s->msix_table_bar_nr == i) {
                uint32_t table_offset = rounddown2(s->msix_table_offset, 4096);
                uint32_t table_size = s->msix_table_offset - table_offset;
                table_size += s->msix_entries_nr * 16;
                table_size = roundup2(table_size, 4096);
                uint64_t remaining = size - table_offset - table_size;
                if (table_offset > 0) {
                    vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa, table_offset);
                }
                if (remaining > 0) {
                    vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa + table_offset + table_size, remaining);
                }
            } else {
                vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa, size);
            }
            s->bars[i].mapped = false;
        }

        if (should_map && !s->bars[i].mapped) {
            int err = 0;
            if (s->is_nvidia_gpu && i == 0 &&
                size > NVIDIA_CFG_MIRROR_OFF + NVIDIA_CFG_MIRROR_LEN) {
                /* Map BAR0 leaving holes for config mirror + VBIOS PROM + MSI-X */
                bhyve_passthru_bar0_remap(s, gpa, hpa, size, true);
            } else if (msix_present(pci_dev) && s->msix_table_bar_nr == i) {
                uint32_t table_offset = rounddown2(s->msix_table_offset, 4096);
                uint32_t table_size = s->msix_table_offset - table_offset;
                table_size += s->msix_entries_nr * 16;
                table_size = roundup2(table_size, 4096);
                uint64_t remaining = size - table_offset - table_size;
                if (table_offset > 0) {
                    err = vm_map_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func,
                                             gpa, table_offset, hpa);
                    if (err) {
                        error_report("bhyve-passthru: Split map BAR %d part 1 failed: %d", i, err);
                    }
                }
                if (remaining > 0) {
                    err = vm_map_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func,
                                             gpa + table_offset + table_size, remaining,
                                             hpa + table_offset + table_size);
                    if (err) {
                        error_report("bhyve-passthru: Split map BAR %d part 2 failed: %d", i, err);
                    }
                }
            } else {
                err = vm_map_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, gpa, size, hpa);
                if (err) {
                    error_report("bhyve-passthru: Map BAR %d failed: %d", i, err);
                }
            }
            if (!err) {
                s->bars[i].mapped = true;
                s->bars[i].gpa = gpa;
            }
        }
    }
}

/*
 * Registers that QEMU manages — reads return QEMU's config, writes
 * are handled by QEMU's MSI/MSI-X/BAR logic (NOT forwarded to device).
 */
static bool bhyve_passthru_is_emulated_reg(BhyvePassthruState *s, uint32_t offset)
{
    PCIDevice *pci_dev = PCI_DEVICE(s);

    if (offset >= PCI_COMMAND && offset < PCI_COMMAND + 2) {
        return true;
    }
    if (offset >= PCI_BASE_ADDRESS_0 && offset < PCI_BASE_ADDRESS_0 + 24) {
        return true;
    }
    if (offset >= PCI_ROM_ADDRESS && offset < PCI_ROM_ADDRESS + 4) {
        return true;
    }
    if (msi_present(pci_dev) && offset >= pci_dev->msi_cap && offset < pci_dev->msi_cap + s->msi_cap_len) {
        return true;
    }
    if (msix_present(pci_dev) && offset >= pci_dev->msix_cap && offset < pci_dev->msix_cap + 12) {
        return true;
    }
    if (offset >= PCI_INTERRUPT_LINE && offset < PCI_INTERRUPT_LINE + 2) {
        return true;
    }
    /* Cap list pointer — QEMU manages the chain after pci_add_capability */
    if (offset == PCI_CAPABILITY_LIST) {
        return true;
    }
    /*
     * Capability space 0x40-0xFF: only emulate cap ID + next pointer bytes
     * (bytes 0 and 1 of each cap) so QEMU's chain stays consistent.
     * All other cap data (PM, PCIe, etc.) must be read LIVE from the
     * physical device — Corvin does this and nvidia.ko depends on it
     * for PCIe link status, PM power state, etc.
     */
    if (offset >= 0x40 && offset < 0x100) {
        /* Walk QEMU's cap chain — if offset is a cap start, emulate id+next */
        uint8_t ptr = pci_dev->config[PCI_CAPABILITY_LIST];
        while (ptr >= 0x40 && ptr <= 0xFC) {
            if (offset == ptr || offset == ptr + 1) {
                return true;  /* cap ID or next pointer */
            }
            uint8_t next = pci_dev->config[ptr + 1];
            if (next == ptr) break;
            ptr = next;
        }
        return false;  /* cap data bytes — read live from device */
    }
    return false;
}

/*
 * Should this config WRITE be forwarded to the physical device?
 * Corvin's native bhyve forwards all cap writes EXCEPT MSI/MSI-X to the
 * physical device. PM, PCIe, and other caps must reach the GPU for proper
 * power management, link control, etc.
 */
static bool bhyve_passthru_should_forward_write(BhyvePassthruState *s, uint32_t offset, int len)
{
    PCIDevice *pci_dev = PCI_DEVICE(s);

    /* Never forward: BARs, COMMAND, ROM, interrupt line */
    if (offset >= PCI_COMMAND && offset < PCI_COMMAND + 2) return false;
    if (offset >= PCI_BASE_ADDRESS_0 && offset < PCI_BASE_ADDRESS_0 + 24) return false;
    if (offset >= PCI_ROM_ADDRESS && offset < PCI_ROM_ADDRESS + 4) return false;
    if (offset >= PCI_INTERRUPT_LINE && offset < PCI_INTERRUPT_LINE + 2) return false;

    /* Never forward: MSI cap (handled by vm_setup_pptdev_msi) */
    if (msi_present(pci_dev) && offset >= pci_dev->msi_cap &&
        offset < pci_dev->msi_cap + s->msi_cap_len) return false;

    /* Never forward: MSI-X cap (handled by vm_setup_pptdev_msix) */
    if (msix_present(pci_dev) && offset >= pci_dev->msix_cap &&
        offset < pci_dev->msix_cap + 12) return false;

    /* Don't forward vendor/device ID, class code (read-only in header) */
    if (offset < PCI_COMMAND) return false;

    /* Header 0x08-0x3F except COMMAND/BARs: emulate only (Corvin does this) */
    if (offset >= 0x08 && offset < 0x40 &&
        !(offset >= PCI_BASE_ADDRESS_0 && offset < PCI_BASE_ADDRESS_0 + 24)) {
        return false;
    }

    /* Everything else (caps 0x40+, extended config 0x100+): forward to device */
    return true;
}

static uint32_t bhyve_passthru_read_config(PCIDevice *pci_dev, uint32_t address, int len)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);

    /*
     * Emulated registers (BARs, COMMAND, MSI, MSI-X) come from QEMU.
     * Everything else: read LIVE from the physical device via PCIOCREAD.
     * PCIOCREAD works after PPT assignment — it goes through the PCI bus,
     * not through the ppt driver. Corvin's native bhyve does the same.
     */
    if (bhyve_passthru_is_emulated_reg(s, address)) {
        /* Let QEMU's default handler return the emulated value */
        uint32_t val = 0;
        for (int i = 0; i < len; i++) {
            val |= (uint32_t)pci_dev->config[address + i] << (i * 8);
        }
        return val;
    }
    /* Non-emulated: live read from physical device */
    return host_read_config(s->pcifd, &s->sel, address, len);
}

static void bhyve_passthru_write_config(PCIDevice *pci_dev, uint32_t address, uint32_t val, int len)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);
    bool was_msi_enabled = msi_enabled(pci_dev);
    bool was_msix_enabled = msix_enabled(pci_dev);

    /* Diagnostic: log ALL config writes for GPU (2/0/0) only */
    if (s->is_nvidia_gpu && s->host_func == 0) {
        fprintf(stderr, "bhyve-passthru: cfg_write dev=%d/%d/%d off=0x%x val=0x%x len=%d msi=%d msix=%d\n",
                s->host_bus, s->host_slot, s->host_func, address, val, len,
                msi_present(pci_dev) ? msi_enabled(pci_dev) : -1,
                msix_present(pci_dev) ? msix_enabled(pci_dev) : -1);
        fflush(stderr);
    }

    /*
     * Update cached config for non-emulated registers.
     */
    for (int i = 0; i < len; i++) {
        uint32_t offset = address + i;
        if (offset < 4096 && !bhyve_passthru_is_emulated_reg(s, offset)) {
            s->host_config[offset] = (val >> (i * 8)) & 0xFF;
        }
    }
    /*
     * Forward capability writes (PM, PCIe, etc.) to the physical device.
     * Corvin's native bhyve does this — the GPU needs to see PM power state
     * changes, PCIe link control, etc. Only MSI/MSI-X are kept emulated
     * (handled by vm_setup_pptdev_msi/msix).
     */
    if (bhyve_passthru_should_forward_write(s, address, len)) {
        host_write_config(s->pcifd, &s->sel, address, len, val);
    }

    pci_default_write_config(pci_dev, address, val, len);

    if (msi_present(pci_dev)) {
        msi_write_config(pci_dev, address, val, len);
    }
    if (msix_present(pci_dev)) {
        msix_write_config(pci_dev, address, val, len);
    }

    /* MSI diagnostic: log config writes to MSI cap area */
    if (msi_present(pci_dev) &&
        address >= pci_dev->msi_cap && address < pci_dev->msi_cap + s->msi_cap_len) {
        fprintf(stderr, "bhyve-passthru: MSI cap write dev=%d/%d/%d off=0x%x val=0x%x len=%d enabled=%d\n",
                s->host_bus, s->host_slot, s->host_func, address, val, len, msi_enabled(pci_dev));
        fflush(stderr);
    }

    if (msi_enabled(pci_dev)) {
        MSIMessage msg = msi_get_message(pci_dev, 0);
        int num_vectors = msi_nr_vectors_allocated(pci_dev);
        fprintf(stderr, "bhyve-passthru: MSI SETUP dev=%d/%d/%d addr=0x%lx data=0x%x vectors=%d\n",
                s->host_bus, s->host_slot, s->host_func,
                (unsigned long)msg.address, msg.data, num_vectors);
        fflush(stderr);
        int err = vm_setup_pptdev_msi(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func,
                                      msg.address, msg.data, num_vectors);
        if (err) {
            fprintf(stderr, "bhyve-passthru: vm_setup_pptdev_msi FAILED: %d (errno=%d)\n", err, errno);
            fflush(stderr);
        } else {
            fprintf(stderr, "bhyve-passthru: vm_setup_pptdev_msi OK\n");
            fflush(stderr);
            /* Register MSI vector so IRR scrubber won't clear it */
            uint8_t vec = msg.data & 0xFF;
            if (vec >= 32 && s->msi_scrub_idx < 0 &&
                bhyve_passthru_msi_count < BHYVE_PASSTHRU_MSI_MAX) {
                s->msi_scrub_idx = bhyve_passthru_msi_count++;
                bhyve_passthru_msi_vectors[s->msi_scrub_idx] = vec;
            } else if (vec >= 32 && s->msi_scrub_idx >= 0) {
                bhyve_passthru_msi_vectors[s->msi_scrub_idx] = vec;
            }
        }
    } else if (was_msi_enabled) {
        fprintf(stderr, "bhyve-passthru: MSI DISABLED dev=%d/%d/%d\n",
                s->host_bus, s->host_slot, s->host_func);
        fflush(stderr);
        vm_setup_pptdev_msi(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, 0, 0, 0);
        /* Unregister MSI vector from IRR protection */
        if (s->msi_scrub_idx >= 0) {
            bhyve_passthru_msi_vectors[s->msi_scrub_idx] = 0;
            s->msi_scrub_idx = -1;
        }
    }

    if (was_msix_enabled && !msix_enabled(pci_dev)) {
        vm_disable_pptdev_msix(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func);
    }

    bhyve_passthru_update_bars(s);
}

static void bhyve_passthru_realize(PCIDevice *pci_dev, Error **errp)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);
    int bus = 0, slot = 0, func = 0;
    uint16_t vendor = 0, device = 0, subvendor = 0, subdevice = 0;
    uint32_t class_code = 0;
    uint8_t revision = 0;
    Error *local_err = NULL;

    s->msi_scrub_idx = -1;

    /*
     * Cached PCI config and BAR data — read BEFORE vm_assign_pptdev().
     * Full 4KB PCIe extended config space. NVIDIA driver reads extended
     * capabilities (AER, L1 PM, etc.) through BAR0+0x88000 mirror.
     */
    uint8_t cached_config[4096];
    struct {
        bool valid;
        uint64_t base;
        uint64_t length;
    } cached_bars[PCI_NUM_REGIONS];

    if (!s->host_str) {
        error_setg(errp, "bhyve-passthru: host property is required");
        return;
    }

    if (sscanf(s->host_str, "%d/%d/%d", &bus, &slot, &func) != 3 &&
        sscanf(s->host_str, "%d:%d:%d", &bus, &slot, &func) != 3 &&
        sscanf(s->host_str, "pci0:%d:%d:%d", &bus, &slot, &func) != 3) {
        error_setg(errp, "bhyve-passthru: invalid host format. Use bus/slot/func (e.g. 2/0/0)");
        return;
    }

    s->host_bus = bus;
    s->host_slot = slot;
    s->host_func = func;
    s->sel.pc_domain = 0;
    s->sel.pc_bus = bus;
    s->sel.pc_dev = slot;
    s->sel.pc_func = func;

    s->pcifd = open("/dev/pci", O_RDWR);
    if (s->pcifd < 0) {
        error_setg_errno(errp, errno, "bhyve-passthru: failed to open /dev/pci");
        return;
    }

    /*
     * Phase 1: Read ALL PCI config and BAR data BEFORE PPT assignment.
     * PCIOCREAD/PCIOCGETBAR will block after vm_assign_pptdev().
     */

    /* Cache entire 4KB PCIe extended config space */
    memset(cached_config, 0, sizeof(cached_config));
    for (int i = 0; i < 4096; i += 4) {
        uint32_t val = host_read_config(s->pcifd, &s->sel, i, 4);
        cached_config[i]     = val & 0xFF;
        cached_config[i + 1] = (val >> 8) & 0xFF;
        cached_config[i + 2] = (val >> 16) & 0xFF;
        cached_config[i + 3] = (val >> 24) & 0xFF;
    }
    /* Store in struct for runtime config reads */
    memcpy(s->host_config, cached_config, 4096);


    /* Cache BAR info */
    memset(cached_bars, 0, sizeof(cached_bars));
    for (int i = 0; i < PCI_NUM_REGIONS; i++) {
        struct pci_bar_io bar;
        memset(&bar, 0, sizeof(bar));
        bar.pbi_sel = s->sel;
        bar.pbi_reg = (i == PCI_ROM_SLOT) ? PCI_ROM_ADDRESS : PCI_BASE_ADDRESS_0 + (i * 4);
        if (ioctl(s->pcifd, PCIOCGETBAR, &bar) == 0) {
            cached_bars[i].valid = true;
            cached_bars[i].base = bar.pbi_base;
            cached_bars[i].length = bar.pbi_length;
        }
    }

    /*
     * Phase 2: Assign device to PPT.
     */
    if (vm_assign_pptdev(bhyve_mach.vm, bus, slot, func) != 0) {
        error_setg(errp, "bhyve-passthru: failed to assign ppt device %d/%d/%d (check loader.conf and drivers)",
                   bus, slot, func);
        close(s->pcifd);
        return;
    }

    /*
     * Phase 3: Use cached data to set up QEMU PCI device.
     * No more PCIOCREAD/PCIOCGETBAR after this point during realize.
     */
    vendor = cached_config[PCI_VENDOR_ID] | (cached_config[PCI_VENDOR_ID + 1] << 8);
    device = cached_config[PCI_DEVICE_ID] | (cached_config[PCI_DEVICE_ID + 1] << 8);
    subvendor = cached_config[PCI_SUBSYSTEM_VENDOR_ID] | (cached_config[PCI_SUBSYSTEM_VENDOR_ID + 1] << 8);
    subdevice = cached_config[PCI_SUBSYSTEM_ID] | (cached_config[PCI_SUBSYSTEM_ID + 1] << 8);
    class_code = (cached_config[PCI_CLASS_REVISION + 1]) |
                 (cached_config[PCI_CLASS_REVISION + 2] << 8) |
                 (cached_config[PCI_CLASS_REVISION + 3] << 16);
    revision = cached_config[PCI_REVISION_ID];

    /* Detect NVIDIA GPU for BAR0 config mirror quirk */
    s->is_nvidia_gpu = (vendor == NVIDIA_PCI_VENDOR) &&
                       ((class_code >> 16) == PCI_BASE_CLASS_DISPLAY);
    if (s->is_nvidia_gpu) {
        error_report("bhyve-passthru: NVIDIA GPU detected (%04x:%04x), "
                     "enabling BAR0 config mirror quirk", vendor, device);
    }

    pci_config_set_vendor_id(pci_dev->config, vendor);
    pci_config_set_device_id(pci_dev->config, device);
    pci_set_word(pci_dev->config + PCI_SUBSYSTEM_VENDOR_ID, subvendor);
    pci_set_word(pci_dev->config + PCI_SUBSYSTEM_ID, subdevice);
    pci_config_set_class(pci_dev->config, class_code);
    pci_set_byte(pci_dev->config + PCI_REVISION_ID, revision);

    /*
     * Copy standard header (first 0x40 bytes) only, skipping emulated registers.
     * Capability space (0x40+) is managed by pci_add_capability / msi_init / msix_init.
     */
    for (int i = 0; i < 0x40; i += 4) {
        if (i == PCI_COMMAND || i == PCI_BASE_ADDRESS_0 || i == PCI_BASE_ADDRESS_1 ||
            i == PCI_BASE_ADDRESS_2 || i == PCI_BASE_ADDRESS_3 || i == PCI_BASE_ADDRESS_4 ||
            i == PCI_BASE_ADDRESS_5 || i == PCI_ROM_ADDRESS || i == PCI_INTERRUPT_LINE) {
            continue;
        }
        uint32_t val = cached_config[i] | (cached_config[i+1] << 8) |
                       (cached_config[i+2] << 16) | (cached_config[i+3] << 24);
        pci_set_long(pci_dev->config + i, val);
    }

    /*
     * Set interrupt pin from physical device. We skipped 0x3C above
     * (it includes both interrupt_line and interrupt_pin). The pin
     * must be non-zero for MSI to work — drivers check it.
     */
    pci_dev->config[PCI_INTERRUPT_PIN] = cached_config[PCI_INTERRUPT_PIN];
    if (pci_dev->config[PCI_INTERRUPT_PIN] == 0) {
        /* Physical device has no interrupt pin set — force INTA for MSI */
        pci_dev->config[PCI_INTERRUPT_PIN] = 1;
    }


    /* Parse capabilities from cached config */
    uint8_t sts = cached_config[PCI_STATUS] | (cached_config[PCI_STATUS + 1] << 8);
    uint8_t msix_cap_ptr = 0;  /* saved MSI-X cap offset for later */
    if (sts & PCI_STATUS_CAP_LIST) {
        /*
         * Clear QEMU's cap list head before registering caps.
         * The header copy above set this to the host's value (e.g. 0x60).
         * pci_add_capability uses config[PCI_CAPABILITY_LIST] as the "old head"
         * for the new cap's next pointer — if it still holds 0x60, PM's next
         * pointer would point to itself, creating a loop.
         */
        pci_dev->config[PCI_CAPABILITY_LIST] = 0;
        uint8_t ptr = cached_config[PCI_CAPABILITY_LIST] & 0xFC; /* align to dword */
        uint32_t visited = 0; /* cycle guard: max 48 caps in 256 bytes */
        while (ptr >= 0x40 && ptr <= 0xFC && visited < 48) {
            visited++;
            uint8_t cap_id = cached_config[ptr + PCI_CAP_LIST_ID];

            if (cap_id == PCI_CAP_ID_MSI) {
                s->msi_present_phys = true;
                uint16_t msgctrl = cached_config[ptr + 2] | (cached_config[ptr + 3] << 8);
                s->msi_cap_len = 10;
                if (msgctrl & PCI_MSI_FLAGS_64BIT) {
                    s->msi_cap_len += 4;
                }
                int num_vectors = 1 << ((msgctrl >> 1) & 0x7);
                /* msi_init() calls pci_add_capability() internally — do NOT add cap separately */
                int ret = msi_init(pci_dev, ptr, num_vectors, !!(msgctrl & PCI_MSI_FLAGS_64BIT), false, &local_err);
                if (ret < 0) {
                    error_propagate(errp, local_err);
                    close(s->pcifd);
                    return;
                }
            } else if (cap_id == PCI_CAP_ID_MSIX) {
                s->msix_present_phys = true;
                msix_cap_ptr = ptr;  /* save for msix_init later */
                uint16_t msgctrl = cached_config[ptr + 2] | (cached_config[ptr + 3] << 8);
                uint32_t table_info = cached_config[ptr + 4] | (cached_config[ptr + 5] << 8) |
                                      (cached_config[ptr + 6] << 16) | (cached_config[ptr + 7] << 24);
                uint32_t pba_info = cached_config[ptr + 8] | (cached_config[ptr + 9] << 8) |
                                    (cached_config[ptr + 10] << 16) | (cached_config[ptr + 11] << 24);

                s->msix_table_bar_nr = table_info & 0x7;
                s->msix_table_offset = table_info & ~0x7;
                s->msix_pba_bar_nr = pba_info & 0x7;
                s->msix_pba_offset = pba_info & ~0x7;
                s->msix_entries_nr = (msgctrl & 0x7FF) + 1;
            } else if (cap_id == PCI_CAP_ID_EXP) {
                /*
                 * For passthrough, don't call pcie_endpoint_cap_init() —
                 * it asserts pci_is_express() which requires device class setup.
                 * Just reserve the cap space; config reads/writes are forwarded
                 * to the physical device by our config_read/config_write handlers.
                 */
                uint8_t exp_flags = cached_config[ptr + 2];
                int exp_ver = exp_flags & 0xF;
                /* PCIe cap v1 = 0x14 bytes, v2 = 0x3C bytes */
                int exp_len = (exp_ver >= 2) ? 0x3C : 0x14;
                int exp_offset = pci_add_capability(pci_dev, PCI_CAP_ID_EXP, ptr, exp_len, &local_err);
                if (exp_offset < 0) {
                    error_propagate(errp, local_err);
                    close(s->pcifd);
                    return;
                }
                /* Copy PCIe cap data from cached config.
                 * Start at j=2 to preserve cap ID (byte 0) and next pointer
                 * (byte 1) set by pci_add_capability — the QEMU chain order
                 * differs from the host chain, so copying byte 1 would break it.
                 */
                for (int j = 2; j < exp_len && (ptr + j) < 256; j++) {
                    pci_dev->config[exp_offset + j] = cached_config[ptr + j];
                }
                /* Preserve original PCIe Device/Port Type from hardware */
            } else {
                /*
                 * Generic cap (PM, VPD, etc.) — register with pci_add_capability
                 * so QEMU manages the chain consistently. Without this, the
                 * next-pointers in host_config and pci_dev->config diverge,
                 * creating infinite loops when the guest walks the chain.
                 *
                 * Determine cap size by looking at where next cap starts.
                 * Minimum cap size is 2 bytes (id + next). Use 2 if we can't
                 * determine actual size; for well-known caps, use known sizes.
                 */
                int cap_size;
                switch (cap_id) {
                case PCI_CAP_ID_PM:    cap_size = 8;  break; /* PCI PM v1.2 */
                case PCI_CAP_ID_AGP:   cap_size = 8;  break;
                case PCI_CAP_ID_VPD:   cap_size = 8;  break;
                case PCI_CAP_ID_SLOTID: cap_size = 4; break;
                case PCI_CAP_ID_HT:    cap_size = 4;  break; /* min, variable */
                case PCI_CAP_ID_SSVID: cap_size = 8;  break;
                case PCI_CAP_ID_PCIX:  cap_size = 8;  break;
                case PCI_CAP_ID_AF:    cap_size = 6;  break;
                default:               cap_size = 4;  break; /* safe minimum */
                }
                /* Clamp to available space */
                if (ptr + cap_size > 256) {
                    cap_size = 256 - ptr;
                }
                int gen_offset = pci_add_capability(pci_dev, cap_id, ptr, cap_size, &local_err);
                if (gen_offset < 0) {
                    /* Non-fatal: just warn and continue */
                    error_report("bhyve-passthru: failed to register cap 0x%02x at 0x%02x: %s",
                                 cap_id, ptr, error_get_pretty(local_err));
                    error_free(local_err);
                    local_err = NULL;
                } else {
                    /* Copy cap data from cached config.
                     * Start at j=2 to preserve cap ID and next pointer
                     * set by pci_add_capability for QEMU's chain ordering.
                     */
                    for (int j = 2; j < cap_size && (ptr + j) < 256; j++) {
                        pci_dev->config[gen_offset + j] = cached_config[ptr + j];
                    }
                }
            }
            uint8_t next = cached_config[ptr + PCI_CAP_LIST_NEXT];
            if (next == ptr) {
                break; /* self-loop */
            }
            ptr = next & 0xFC; /* align to dword */
        }

        /* Scan for orphan MSI-X cap not linked in the standard chain.
         * Some NVIDIA GPUs place MSI-X (cap ID 0x11) at e.g. 0xC8 with next=0x00,
         * disconnected from the PM→MSI→PCIe chain. nvidia.ko (595.x GSP) requires
         * MSI-X and silently falls back to broken INTx without it. */
        fprintf(stderr, "bhyve-passthru: orphan scan dev=%d/%d/%d msix_present=%d sts=0x%x cfg[0xC8]=0x%02x\n",
                s->host_bus, s->host_slot, s->host_func,
                s->msix_present_phys, sts, cached_config[0xC8]);
        fflush(stderr);
        if (!s->msix_present_phys) {
            for (int scan_ptr = 0x40; scan_ptr <= 0xF0; scan_ptr += 4) {
                if (cached_config[scan_ptr] != PCI_CAP_ID_MSIX) {
                    continue;
                }
                uint16_t msgctrl = (uint16_t)(cached_config[scan_ptr + 2] |
                                              (cached_config[scan_ptr + 3] << 8));
                uint32_t table_info = cached_config[scan_ptr + 4] |
                                      (cached_config[scan_ptr + 5] << 8) |
                                      (cached_config[scan_ptr + 6] << 16) |
                                      (cached_config[scan_ptr + 7] << 24);
                uint8_t bar_idx = table_info & 0x7;
                if (bar_idx >= PCI_NUM_REGIONS || !cached_bars[bar_idx].valid) {
                    continue;
                }
                uint32_t pba_info = cached_config[scan_ptr + 8] |
                                    (cached_config[scan_ptr + 9] << 8) |
                                    (cached_config[scan_ptr + 10] << 16) |
                                    (cached_config[scan_ptr + 11] << 24);
                s->msix_present_phys = true;
                msix_cap_ptr = (uint8_t)scan_ptr;
                s->msix_table_bar_nr = bar_idx;
                s->msix_table_offset = table_info & ~(uint32_t)0x7;
                s->msix_pba_bar_nr = pba_info & 0x7;
                s->msix_pba_offset = pba_info & ~(uint32_t)0x7;
                s->msix_entries_nr = (msgctrl & 0x7FF) + 1;
                error_report("bhyve-passthru: orphan MSI-X cap at 0x%02x: "
                             "%u vectors BIR=%u table_off=0x%x",
                             scan_ptr, s->msix_entries_nr,
                             s->msix_table_bar_nr, s->msix_table_offset);
                break;
            }
        }
    }

    /* Register BARs from cached data */
    for (int i = 0; i < PCI_NUM_REGIONS; i++) {
        if (!cached_bars[i].valid) {
            continue;
        }

        s->bars[i].size = cached_bars[i].length;
        s->bars[i].mapped = false;

        /*
         * pbi_base from PCIOCGETBAR may include BAR type bits in the low nibble
         * (especially for 64-bit prefetchable BARs). Mask them off to get the
         * true host physical address. Memory BARs: mask lower 4 bits.
         * IO BARs: mask lower 2 bits.
         */
        {
            int reg_off = (i == PCI_ROM_SLOT) ? PCI_ROM_ADDRESS : PCI_BASE_ADDRESS_0 + (i * 4);
            uint32_t raw_bar = cached_config[reg_off] |
                               (cached_config[reg_off + 1] << 8) |
                               (cached_config[reg_off + 2] << 16) |
                               (cached_config[reg_off + 3] << 24);
            if (raw_bar & 1) {
                /* IO BAR: mask lower 2 bits */
                s->bars[i].hpa = cached_bars[i].base & ~0x3ULL;
            } else {
                /* Memory BAR: mask lower 4 bits */
                s->bars[i].hpa = cached_bars[i].base & ~0xFULL;
            }
        }

        if (cached_bars[i].length == 0) {
            continue;
        }

        /*
         * Read BAR type from the raw config register, not from pbi_base.
         * pbi_base is the decoded physical address (no type bits).
         * The config register has: bit0=IO, bits2:1=type (00=32bit, 10=64bit),
         * bit3=prefetchable.
         */
        uint32_t bar_reg_val = 0;
        if (i == PCI_ROM_SLOT) {
            bar_reg_val = cached_config[PCI_ROM_ADDRESS] |
                          (cached_config[PCI_ROM_ADDRESS + 1] << 8) |
                          (cached_config[PCI_ROM_ADDRESS + 2] << 16) |
                          (cached_config[PCI_ROM_ADDRESS + 3] << 24);
        } else {
            int reg_off = PCI_BASE_ADDRESS_0 + (i * 4);
            bar_reg_val = cached_config[reg_off] |
                          (cached_config[reg_off + 1] << 8) |
                          (cached_config[reg_off + 2] << 16) |
                          (cached_config[reg_off + 3] << 24);
        }

        bool is_io = (bar_reg_val & 1);
        bool is_64bit = !is_io && ((bar_reg_val & 0x6) == 0x4);
        bool is_prefetch = !is_io && (bar_reg_val & 0x8);

        struct BhyvePassthruBarContext *b = g_new0(struct BhyvePassthruBarContext, 1);
        b->s = s;
        b->bar_idx = i;

        char *mr_name = g_strdup_printf("bhyve-passthru-bar%d", i);
        memory_region_init_io(&s->bars[i].mr, OBJECT(s), &bhyve_passthru_bar_ops, b, mr_name, cached_bars[i].length);
        g_free(mr_name);

        uint8_t attr = 0;
        if (i == PCI_ROM_SLOT) {
            attr = PCI_BASE_ADDRESS_MEM_PREFETCH;
            pci_register_bar(pci_dev, i, attr, &s->bars[i].mr);
        } else if (is_io) {
            s->bars[i].type = 1;
            attr = PCI_BASE_ADDRESS_SPACE_IO;
            pci_register_bar(pci_dev, i, attr, &s->bars[i].mr);
        } else {
            s->bars[i].type = 0;
            attr = PCI_BASE_ADDRESS_SPACE_MEMORY;
            if (is_64bit) {
                attr |= PCI_BASE_ADDRESS_MEM_TYPE_64;
            }
            if (is_prefetch) {
                attr |= PCI_BASE_ADDRESS_MEM_PREFETCH;
            }
            pci_register_bar(pci_dev, i, attr, &s->bars[i].mr);
        }
    }

    if (s->msix_present_phys) {
        /* msix_init() calls pci_add_capability() internally — do NOT add cap separately */
        int err = msix_init(pci_dev, s->msix_entries_nr,
                             &s->bars[s->msix_table_bar_nr].mr, s->msix_table_bar_nr, s->msix_table_offset,
                             &s->bars[s->msix_pba_bar_nr].mr, s->msix_pba_bar_nr, s->msix_pba_offset,
                             msix_cap_ptr, &local_err);
        if (err < 0) {
            error_propagate(errp, local_err);
            close(s->pcifd);
            return;
        }
        msix_set_vector_notifiers(pci_dev, bhyve_passthru_msix_vector_use,
                                  bhyve_passthru_msix_vector_release, NULL);
    }

}

static void bhyve_passthru_exit(PCIDevice *pci_dev)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);

    for (int i = 0; i < PCI_NUM_REGIONS; i++) {
        if (s->bars[i].mapped) {
            uint64_t old_gpa = s->bars[i].gpa;
            uint64_t size = s->bars[i].size;
            if (msix_present(pci_dev) && s->msix_table_bar_nr == i) {
                uint32_t table_offset = rounddown2(s->msix_table_offset, 4096);
                if (table_offset > 0) {
                    vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa, table_offset);
                }
                uint32_t table_size = s->msix_table_offset - table_offset;
                table_size += s->msix_entries_nr * 16;
                table_size = roundup2(table_size, 4096);
                uint64_t remaining = size - table_offset - table_size;
                if (remaining > 0) {
                    vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa + table_offset + table_size, remaining);
                }
            } else {
                vm_unmap_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, old_gpa, size);
            }
            s->bars[i].mapped = false;
        }
    }

    if (msix_present(pci_dev)) {
        msix_unset_vector_notifiers(pci_dev);
        vm_disable_pptdev_msix(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func);
        msix_uninit(pci_dev, &s->bars[s->msix_table_bar_nr].mr, &s->bars[s->msix_pba_bar_nr].mr);
    }
    if (msi_present(pci_dev)) {
        vm_setup_pptdev_msi(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, 0, 0, 0);
        msi_uninit(pci_dev);
    }

    vm_unassign_pptdev(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func);

    if (s->pcifd >= 0) {
        close(s->pcifd);
    }
}

static const Property bhyve_passthru_properties[] = {
    DEFINE_PROP_STRING("host", BhyvePassthruState, host_str),
};

static void bhyve_passthru_class_init(ObjectClass *klass, const void *data)
{
    DeviceClass *dc = DEVICE_CLASS(klass);
    PCIDeviceClass *k = PCI_DEVICE_CLASS(klass);

    k->realize = bhyve_passthru_realize;
    k->exit = bhyve_passthru_exit;
    k->config_read = bhyve_passthru_read_config;
    k->config_write = bhyve_passthru_write_config;

    device_class_set_props(dc, bhyve_passthru_properties);
    dc->desc = "Bhyve PCI Passthrough Device";
    set_bit(DEVICE_CATEGORY_MISC, dc->categories);
}

static const TypeInfo bhyve_passthru_info = {
    .name          = TYPE_BHYVE_PASSTHRU,
    .parent        = TYPE_PCI_DEVICE,
    .instance_size = sizeof(BhyvePassthruState),
    .class_init    = bhyve_passthru_class_init,
    .interfaces = (InterfaceInfo[]) {
        { INTERFACE_PCIE_DEVICE },
        { },
    },
};

static void bhyve_passthru_register_types(void)
{
    type_register_static(&bhyve_passthru_info);
}

type_init(bhyve_passthru_register_types)
