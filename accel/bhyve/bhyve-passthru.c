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
#define NVIDIA_CFG_MIRROR_LEN   0x1000  /* PCIe extended config: 4KB */

struct BhyvePassthruBarContext {
    BhyvePassthruState *s;
    int bar_idx;
};

/* Forward declaration — used in NVIDIA quirk BAR read/write */
static bool bhyve_passthru_is_emulated_reg(BhyvePassthruState *s, uint32_t offset);

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

    /* NVIDIA quirk: intercept PCI config mirror at BAR0+0x88000 */
    if (s->is_nvidia_gpu && bar_idx == 0 &&
        addr >= NVIDIA_CFG_MIRROR_OFF &&
        addr < NVIDIA_CFG_MIRROR_OFF + NVIDIA_CFG_MIRROR_LEN) {
        uint64_t cfg_off = addr - NVIDIA_CFG_MIRROR_OFF;
        /* Return from cached config + QEMU emulated overlay */
        uint32_t val = 0;
        for (unsigned i = 0; i < size && (cfg_off + i) < 256; i++) {
            uint32_t off = cfg_off + i;
            uint8_t byte = bhyve_passthru_is_emulated_reg(s, off)
                         ? PCI_DEVICE(s)->config[off]
                         : s->host_config[off];
            val |= (uint32_t)byte << (i * 8);
        }
        return val;
    }

    /*
     * BAR read fallback — PCIOCBARIO blocks after PPT assignment.
     * For passthrough, real BAR accesses go directly through EPT
     * (set up by vm_map_pptdev_mmio in update_bars). This callback
     * is only hit for unmapped regions or before EPT mapping is active.
     */
    static int bar_read_count = 0;
    if (bar_read_count < 20) {
        fprintf(stderr, "bhyve-passthru: bar_read BAR%d addr=0x%lx size=%u → 0xFFFFFFFF\n",
                bar_idx, (unsigned long)addr, size);
        fflush(stderr);
        bar_read_count++;
    }
    return 0xFFFFFFFF;
}

static void bhyve_passthru_bar_write(void *opaque, hwaddr addr, uint64_t val, unsigned size)
{
    struct BhyvePassthruBarContext *b = opaque;
    BhyvePassthruState *s = b->s;
    int bar_idx = b->bar_idx;

    /* NVIDIA quirk: intercept PCI config mirror writes at BAR0+0x88000 */
    if (s->is_nvidia_gpu && bar_idx == 0 &&
        addr >= NVIDIA_CFG_MIRROR_OFF &&
        addr < NVIDIA_CFG_MIRROR_OFF + NVIDIA_CFG_MIRROR_LEN) {
        uint64_t cfg_off = addr - NVIDIA_CFG_MIRROR_OFF;
        /* Update cached config */
        for (unsigned i = 0; i < size && (cfg_off + i) < 256; i++) {
            s->host_config[cfg_off + i] = (val >> (i * 8)) & 0xFF;
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
    int err = vm_setup_pptdev_msix(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func,
                                   vector, msg.address, msg.data, 0);
    if (err) {
        error_report("bhyve-passthru: vm_setup_pptdev_msix vector %u use failed: %d", vector, err);
        return -errno;
    }
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
            continue;
        }

        if (r->type & PCI_BASE_ADDRESS_SPACE_IO) {
            continue;
        }

        bool should_map = (pci_dev->config[PCI_COMMAND] & PCI_COMMAND_MEMORY);

        if (s->bars[i].mapped && (!should_map || s->bars[i].gpa != gpa)) {
            uint64_t old_gpa = s->bars[i].gpa;
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

        if (should_map && !s->bars[i].mapped) {
            int err = 0;
            fprintf(stderr, "bhyve-passthru: mapping BAR%d GPA=0x%lx HPA=0x%lx size=0x%lx\n",
                    i, (unsigned long)gpa, (unsigned long)hpa, (unsigned long)size);
            fflush(stderr);
            if (msix_present(pci_dev) && s->msix_table_bar_nr == i) {
                uint32_t table_offset = rounddown2(s->msix_table_offset, 4096);
                if (table_offset > 0) {
                    err = vm_map_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, gpa, table_offset, hpa);
                    if (err) {
                        error_report("bhyve-passthru: Split map BAR %d part 1 failed: %d", i, err);
                    }
                }
                uint32_t table_size = s->msix_table_offset - table_offset;
                table_size += s->msix_entries_nr * 16;
                table_size = roundup2(table_size, 4096);
                uint64_t remaining = size - table_offset - table_size;
                if (remaining > 0) {
                    err = vm_map_pptdev_mmio(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, gpa + table_offset + table_size, remaining, hpa + table_offset + table_size);
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
     * All capability space (0x40-0xFF) is emulated — we registered every cap
     * with pci_add_capability, so pci_dev->config owns the entire chain.
     */
    if (offset >= 0x40 && offset < 0x100) {
        return true;
    }
    return false;
}

static uint32_t bhyve_passthru_read_config(PCIDevice *pci_dev, uint32_t address, int len)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);

    /*
     * Use cached config instead of PCIOCREAD — the ioctl blocks
     * after vm_assign_pptdev() has claimed the device.
     * Emulated registers (BARs, COMMAND, MSI, MSI-X) come from
     * QEMU's pci_dev->config; everything else from host_config cache.
     */
    static int cfg_read_count = 0;
    (void)cfg_read_count; /* suppress unused warning */
    uint32_t val = 0;
    for (int i = 0; i < len; i++) {
        uint32_t offset = address + i;
        uint8_t byte;
        if (offset < 256 && bhyve_passthru_is_emulated_reg(s, offset)) {
            byte = pci_dev->config[offset];
        } else if (offset < 256) {
            byte = s->host_config[offset];
        } else {
            byte = 0;
        }
        val |= (uint32_t)byte << (i * 8);
    }
    if (cfg_read_count < 50) {
        fprintf(stderr, "bhyve-passthru: read_config[%d/%d/%d] reg=0x%02x len=%d → 0x%x\n",
                s->host_bus, s->host_slot, s->host_func, address, len, val);
        fflush(stderr);
        cfg_read_count++;
    }
    return val;
}

static void bhyve_passthru_write_config(PCIDevice *pci_dev, uint32_t address, uint32_t val, int len)
{
    BhyvePassthruState *s = BHYVE_PASSTHRU(pci_dev);
    bool was_msi_enabled = msi_enabled(pci_dev);
    bool was_msix_enabled = msix_enabled(pci_dev);

    /* Debug: log writes to COMMAND and BAR registers */
    if (address == PCI_COMMAND ||
        (address >= PCI_BASE_ADDRESS_0 && address < PCI_BASE_ADDRESS_0 + 24)) {
        fprintf(stderr, "bhyve-passthru[%d/%d/%d]: write config 0x%02x = 0x%x (len=%d)\n",
                s->host_bus, s->host_slot, s->host_func, address, val, len);
        fflush(stderr);
    }

    /*
     * Update cached config for non-emulated registers.
     * Do NOT call host_write_config (PCIOCWRITE) — it blocks after PPT assignment.
     * Hardware config writes for MSI/MSI-X are handled via vm_setup_pptdev_msi/msix.
     * BAR mapping is handled via vm_map_pptdev_mmio in update_bars.
     */
    for (int i = 0; i < len; i++) {
        uint32_t offset = address + i;
        if (offset < 256 && !bhyve_passthru_is_emulated_reg(s, offset)) {
            s->host_config[offset] = (val >> (i * 8)) & 0xFF;
        }
    }

    pci_default_write_config(pci_dev, address, val, len);

    if (msi_present(pci_dev)) {
        msi_write_config(pci_dev, address, val, len);
    }
    if (msix_present(pci_dev)) {
        msix_write_config(pci_dev, address, val, len);
    }

    if (msi_enabled(pci_dev)) {
        MSIMessage msg = msi_get_message(pci_dev, 0);
        int num_vectors = msi_nr_vectors_allocated(pci_dev);
        int err = vm_setup_pptdev_msi(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func,
                                      msg.address, msg.data, num_vectors);
        if (err) {
            error_report("bhyve-passthru: vm_setup_pptdev_msi failed: %d", err);
        }
    } else if (was_msi_enabled) {
        vm_setup_pptdev_msi(bhyve_mach.vm, s->host_bus, s->host_slot, s->host_func, 0, 0, 0);
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

    /*
     * Cached PCI config and BAR data — read BEFORE vm_assign_pptdev().
     * After PPT assignment, PCIOCREAD on /dev/pci blocks because the
     * kernel PPT driver has claimed the device.
     */
    uint8_t cached_config[256];
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

    fprintf(stderr, "bhyve-passthru: opening /dev/pci...\n");
    s->pcifd = open("/dev/pci", O_RDWR);
    if (s->pcifd < 0) {
        error_setg_errno(errp, errno, "bhyve-passthru: failed to open /dev/pci");
        return;
    }
    fprintf(stderr, "bhyve-passthru: /dev/pci opened (fd=%d)\n", s->pcifd);

    /*
     * Phase 1: Read ALL PCI config and BAR data BEFORE PPT assignment.
     * PCIOCREAD/PCIOCGETBAR will block after vm_assign_pptdev().
     */
    fprintf(stderr, "bhyve-passthru: pre-reading config for %d/%d/%d...\n", bus, slot, func);
    fflush(stderr);

    /* Cache entire 256-byte config space */
    for (int i = 0; i < 256; i += 4) {
        uint32_t val = host_read_config(s->pcifd, &s->sel, i, 4);
        cached_config[i]     = val & 0xFF;
        cached_config[i + 1] = (val >> 8) & 0xFF;
        cached_config[i + 2] = (val >> 16) & 0xFF;
        cached_config[i + 3] = (val >> 24) & 0xFF;
    }
    /* Store in struct for runtime config reads */
    memcpy(s->host_config, cached_config, 256);

    fprintf(stderr, "bhyve-passthru: config cached (vendor=%04x device=%04x)\n",
            cached_config[0] | (cached_config[1] << 8),
            cached_config[2] | (cached_config[3] << 8));
    fflush(stderr);

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
    fprintf(stderr, "bhyve-passthru: BARs cached\n");
    fflush(stderr);

    /*
     * Phase 2: Assign device to PPT.
     */
    fprintf(stderr, "bhyve-passthru: assigning ppt %d/%d/%d...\n", bus, slot, func);
    fflush(stderr);
    if (vm_assign_pptdev(bhyve_mach.vm, bus, slot, func) != 0) {
        error_setg(errp, "bhyve-passthru: failed to assign ppt device %d/%d/%d (check loader.conf and drivers)",
                   bus, slot, func);
        close(s->pcifd);
        return;
    }
    fprintf(stderr, "bhyve-passthru: ppt assigned\n");
    fflush(stderr);

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

    fprintf(stderr, "bhyve-passthru: nvidia=%d, setting config...\n", s->is_nvidia_gpu);
    fflush(stderr);
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
    fprintf(stderr, "bhyve-passthru: interrupt pin = %d\n",
            pci_dev->config[PCI_INTERRUPT_PIN]);

    fprintf(stderr, "bhyve-passthru: config copied, parsing caps...\n");
    fflush(stderr);

    /* Parse capabilities from cached config */
    uint8_t sts = cached_config[PCI_STATUS] | (cached_config[PCI_STATUS + 1] << 8);
    uint8_t msix_cap_ptr = 0;  /* saved MSI-X cap offset for later */
    if (sts & PCI_STATUS_CAP_LIST) {
        uint8_t ptr = cached_config[PCI_CAPABILITY_LIST] & 0xFC; /* align to dword */
        uint32_t visited = 0; /* cycle guard: max 48 caps in 256 bytes */
        while (ptr >= 0x40 && ptr <= 0xFC && visited < 48) {
            visited++;
            uint8_t cap_id = cached_config[ptr + PCI_CAP_LIST_ID];
            fprintf(stderr, "bhyve-passthru:   cap 0x%02x at offset 0x%02x\n", cap_id, ptr);
            fflush(stderr);

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
                fprintf(stderr, "bhyve-passthru:   MSI-X: %d entries, table BAR%d+0x%x, PBA BAR%d+0x%x\n",
                        s->msix_entries_nr, s->msix_table_bar_nr, s->msix_table_offset,
                        s->msix_pba_bar_nr, s->msix_pba_offset);
                fflush(stderr);
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
                /* Copy PCIe cap data from cached config */
                for (int j = 0; j < exp_len && (ptr + j) < 256; j++) {
                    pci_dev->config[exp_offset + j] = cached_config[ptr + j];
                }
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
                    /* Copy cap data from cached config */
                    for (int j = 0; j < cap_size && (ptr + j) < 256; j++) {
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
    }
    fprintf(stderr, "bhyve-passthru: caps done (msi=%d msix=%d)\n",
            s->msi_present_phys, s->msix_present_phys);
    fflush(stderr);

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
        fprintf(stderr, "bhyve-passthru:   BAR%d: size=0x%lx %s%s%s\n",
                i, (unsigned long)cached_bars[i].length,
                is_io ? "IO" : "MEM",
                is_64bit ? " 64bit" : " 32bit",
                is_prefetch ? " prefetch" : "");
        fflush(stderr);
    }

    fprintf(stderr, "bhyve-passthru: BARs registered, setting up MSI-X...\n");
    fflush(stderr);
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
    fprintf(stderr, "bhyve-passthru: realize complete for %d/%d/%d\n", s->host_bus, s->host_slot, s->host_func);
    fflush(stderr);
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
        { INTERFACE_CONVENTIONAL_PCI_DEVICE },
        { INTERFACE_PCIE_DEVICE },
        { },
    },
};

static void bhyve_passthru_register_types(void)
{
    type_register_static(&bhyve_passthru_info);
}

type_init(bhyve_passthru_register_types)
