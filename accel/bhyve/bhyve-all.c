#include "qemu/osdep.h"
#include "qemu/accel.h"
#include "accel/accel-ops.h"
#include "hw/core/boards.h"
#include "qemu/typedefs.h"
#include "system/runstate.h"
#include "system/bhyve.h"
#include "cpu.h"
#include "system/address-spaces.h"
#include "system/ioport.h"
#include "qemu/main-loop.h"
#include "qemu/timer.h"
#include "qemu/aio.h"
#include "qemu/error-report.h"
#include "qapi/error.h"
#include "system/memory.h"
#include "system/cpu-timers.h"
#include "strings.h"
#include "qapi/qapi-types-common.h"
#include "qapi/qapi-visit-common.h"

#include "bhyve-accel-ops.h"
#include "bhyve-internal.h"
#include "hw/i386/apic_internal.h"
#include "hw/intc/ioapic.h"

#include <signal.h>
#include <unistd.h>
#include <errno.h>
#include <sys/sched.h>

#include <machine/specialreg.h>

#include <string.h>
#include <sys/ioctl.h>
#include <vmmapi.h>
#include <machine/vmm_dev.h>

/*
 * Debug output control.  Define BHYVE_DEBUG=1 to enable verbose
 * hot-path tracing (MMIO, HLT, IRQ injection, heartbeat, etc.).
 * Default: OFF for production use.
 */
#ifndef BHYVE_DEBUG
#define BHYVE_DEBUG 0
#endif
#define BHYVE_DPRINTF(fmt, ...) \
    do { if (BHYVE_DEBUG) fprintf(stderr, fmt, ## __VA_ARGS__); } while (0)

/*
 * Workaround for FreeBSD _IOR ioctl bug:
 *
 * VM_LAPIC_GET_STATE is defined as _IOR(...) which causes the kernel to
 * bzero the ioctl buffer instead of copyin'ing it.  This zeroes the vcpuid
 * that vcpu_ioctl() writes to the first 4 bytes, making GET_STATE always
 * read vcpu 0 (BSP) regardless of which vcpu was requested.
 *
 * This wrapper uses _IOWR to force copyin+copyout, ensuring the vcpuid
 * is passed to the kernel correctly.  The kernel's ioctl dispatch table
 * uses _IOR, so we must use the _IOR cmd number — but we construct the
 * ioctl call manually with explicit copyin by using the underlying
 * struct vcpu's fd.
 *
 * Simpler approach: since we can't change the kernel ioctl cmd,
 * we work around the bzero by writing the vcpuid AFTER the ioctl call
 * is prepared but BEFORE it executes.  Unfortunately, this isn't possible
 * with standard ioctl().
 *
 * Final approach: use the SET_STATE ioctl to write a known state,
 * or avoid GET_STATE entirely where possible.  For the IRR scrub,
 * we write a clean state directly with SET_STATE.
 */

/*
 * Read a uint64_t from guest virtual address by walking x86-64 page tables.
 * Returns the value at the guest virtual address, or 0 on failure.
 * Uses QEMU's cpu_physical_memory_read to access guest physical memory.
 */
static uint64_t read_guest_virt64(uint64_t cr3, uint64_t vaddr) {
    uint64_t pml4e, pdpte, pde, pte;
    uint64_t paddr;

    /* PML4 */
    paddr = (cr3 & ~0xFFFULL) + (((vaddr >> 39) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pml4e, 8);
    if (!(pml4e & 1)) return 0;

    /* PDPT */
    paddr = (pml4e & 0x000FFFFFFFFFF000ULL) + (((vaddr >> 30) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pdpte, 8);
    if (!(pdpte & 1)) return 0;
    if (pdpte & (1ULL << 7)) { /* 1GB page */
        paddr = (pdpte & 0x000FFFFFC0000000ULL) | (vaddr & 0x3FFFFFFFULL);
        uint64_t result = 0;
        cpu_physical_memory_read(paddr, &result, 8);
        return result;
    }

    /* PD */
    paddr = (pdpte & 0x000FFFFFFFFFF000ULL) + (((vaddr >> 21) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pde, 8);
    if (!(pde & 1)) return 0;
    if (pde & (1ULL << 7)) { /* 2MB page */
        paddr = (pde & 0x000FFFFFFFE00000ULL) | (vaddr & 0x1FFFFFULL);
        uint64_t result = 0;
        cpu_physical_memory_read(paddr, &result, 8);
        return result;
    }

    /* PT */
    paddr = (pde & 0x000FFFFFFFFFF000ULL) + (((vaddr >> 12) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pte, 8);
    if (!(pte & 1)) return 0;

    /* Final physical address */
    paddr = (pte & 0x000FFFFFFFFFF000ULL) | (vaddr & 0xFFFULL);
    uint64_t result = 0;
    cpu_physical_memory_read(paddr, &result, 8);
    return result;
}

/*
 * Translate guest virtual address to physical using x86-64 page table walk.
 * Returns physical address, or (uint64_t)-1 on failure.
 */
static uint64_t guest_virt_to_phys(uint64_t cr3, uint64_t vaddr) {
    uint64_t pml4e, pdpte, pde, pte;
    uint64_t paddr;

    paddr = (cr3 & ~0xFFFULL) + (((vaddr >> 39) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pml4e, 8);
    if (!(pml4e & 1)) return (uint64_t)-1;

    paddr = (pml4e & 0x000FFFFFFFFFF000ULL) + (((vaddr >> 30) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pdpte, 8);
    if (!(pdpte & 1)) return (uint64_t)-1;
    if (pdpte & (1ULL << 7))
        return (pdpte & 0x000FFFFFC0000000ULL) | (vaddr & 0x3FFFFFFFULL);

    paddr = (pdpte & 0x000FFFFFFFFFF000ULL) + (((vaddr >> 21) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pde, 8);
    if (!(pde & 1)) return (uint64_t)-1;
    if (pde & (1ULL << 7))
        return (pde & 0x000FFFFFFFE00000ULL) | (vaddr & 0x1FFFFFULL);

    paddr = (pde & 0x000FFFFFFFFFF000ULL) + (((vaddr >> 12) & 0x1FF) * 8);
    cpu_physical_memory_read(paddr, &pte, 8);
    if (!(pte & 1)) return (uint64_t)-1;

    return (pte & 0x000FFFFFFFFFF000ULL) | (vaddr & 0xFFFULL);
}

/*
 * Write a uint64_t to guest virtual address.
 */
static void write_guest_virt64(uint64_t cr3, uint64_t vaddr, uint64_t val) {
    uint64_t paddr = guest_virt_to_phys(cr3, vaddr);
    if (paddr != (uint64_t)-1) {
        cpu_physical_memory_write(paddr, &val, 8);
    }
}

/*
 * Scrub low vectors (0-31) from the in-kernel LAPIC IRR.
 *
 * The UEFI firmware programs the LAPIC timer with a low vector (e.g. 30).
 * When the FreeBSD kernel does STI for the first time, this stale timer
 * interrupt fires as trap 30 (reserved fault), crashing the guest.
 *
 * We cannot intercept in-kernel LAPIC vector injection from userspace,
 * so we periodically read the LAPIC state via ioctl, clear any low
 * vectors from IRR, and also mask the LVT Timer if its vector is < 32.
 *
 * NOTE: vcpu_ioctl() overwrites the first 4 bytes of the ioctl data
 * with the vcpuid, so fields[0].data is clobbered by the vcpuid.
 */
/*
 * Scrub dangerous vectors from in-kernel LAPIC IRR.
 *
 * Always scrubs:
 *   - Vectors 0-31: would cause #GP if delivered
 *   - Vector 32 (0x20): PIC master base — no IDT handler in FreeBSD
 *   - Vector 64 (0x40): UEFI PIC base — no IDT handler in FreeBSD
 *
 * These PIC-base vectors are injected by the bhyve kernel's vatpic
 * or by QEMU's interrupt routing and have no corresponding IDT handler
 * in the FreeBSD guest (the guest uses IOAPIC vectors >= 48).
 */
static void scrub_lapic_bad_vectors(struct vcpu *vcpu, int cpu_index,
                                     long run_total)
{
    struct vm_lapic_state state;

    memset(&state, 0, sizeof(state));

    int err = vcpu_ioctl(vcpu, VM_LAPIC_GET_STATE, &state);
    if (err < 0)
        return;

    int modified = 0;

    /* IRR[0]: vectors 0-31 — always clear ALL */
    if (state.fields[0x20].data != 0) {
        state.fields[0x20].data = 0;
        modified = 1;
    }

    /* IRR[1]: vectors 32-63 — clear stale vectors, but NOT vectors
     * that are actively assigned to IOAPIC pins by the guest OS.
     * Without this check, legitimate ATA interrupts (vec 0x20=32,
     * assigned by Linux to IOAPIC pin 14) get scrubbed, causing
     * "lost interrupt" errors and 30s boot timeouts. */
    uint32_t irr1 = state.fields[0x21].data;
    if (irr1) {
        /* Build mask of vectors 32-63 that are live IOAPIC assignments */
        uint32_t live_mask = 0;
        for (int p = 0; p < 24; p++) {
            uint8_t v = bhyve_ioapic_vectors[p];
            if (v >= 32 && v < 64) {
                live_mask |= (1u << (v - 32));
            }
        }
        /* Only scrub vectors that are NOT live IOAPIC assignments */
        uint32_t scrub_mask = irr1 & ~live_mask;
        if (scrub_mask) {
            state.fields[0x21].data = irr1 & ~scrub_mask;
            modified = 1;
        }
    }

    /* IRR[2]: vectors 64-95 — same approach */
    uint32_t irr2 = state.fields[0x22].data;
    if (irr2) {
        uint32_t live_mask2 = 0;
        for (int p = 0; p < 24; p++) {
            uint8_t v = bhyve_ioapic_vectors[p];
            if (v >= 64 && v < 96) {
                live_mask2 |= (1u << (v - 64));
            }
        }
        uint32_t scrub_mask2 = irr2 & ~live_mask2;
        if (scrub_mask2) {
            state.fields[0x22].data = irr2 & ~scrub_mask2;
            modified = 1;
        }
    }

    /* Check LVT Timer for low vector */
    uint32_t lvt_timer = state.fields[0x32].data;
    if ((lvt_timer & 0xFF) < 32 && !((lvt_timer >> 16) & 1)) {
        state.fields[0x32].data = lvt_timer | (1 << 16);
        modified = 1;
    }

    if (modified) {
        vcpu_ioctl(vcpu, VM_LAPIC_SET_STATE, &state);
    }
}

/* -------------------------------------------------------------------------- */

static volatile long vm_run_total = 0;      /* total vm_run calls */
static volatile long exit_hlt = 0;
static volatile long exit_bogus = 0;
static volatile long exit_inout = 0;
static volatile long exit_debug = 0;
static volatile long exit_other = 0;
static volatile long exit_pause = 0;

/*
 * LAPIC timer — precise deadline timer for HLT exits.
 *
 * When the guest executes HLT, the kernel returns to userspace (retu=true).
 * We read the kernel's vLAPIC timer state (CCR, DCR, ICR) and compute the
 * exact time the next LAPIC timer interrupt will fire.  The host timer is
 * armed for that precise deadline rather than polling at a fixed interval.
 *
 * Additionally, on HLT exit we check the kernel LAPIC's IRR — if a timer
 * interrupt has already fired (set by the kernel callout handler), we skip
 * the halt entirely and re-enter the VM immediately.
 *
 * For device interrupts (PIC/IOAPIC), the set_irq handlers call
 * cpu_interrupt(CPU_INTERRUPT_HARD) which wakes the halted vCPU thread
 * instantly, independent of this timer.
 */
#define VLAPIC_BUS_FREQ (128 * 1024 * 1024)
static void lapic_poll_timer_cb(void *opaque)
{
    CPUState *cpu = (CPUState *)opaque;
    if (cpu) {
        static long poll_fire_count = 0;
        poll_fire_count++;
        if (poll_fire_count <= 5 || (poll_fire_count % 200) == 0) {
            BHYVE_DPRINTF("[POLL-TMR] vcpu%d fire#%ld halted=%d "
                    "ioapic_pend=0x%x\n",
                    cpu->cpu_index, poll_fire_count,
                    cpu->halted,
                    __atomic_load_n(&bhyve_ioapic_pending_irqs,
                                    __ATOMIC_ACQUIRE));
        }
        if (cpu->halted) {
            /*
             * Force-unhalt the CPU. The bhyve kernel's vLAPIC manages
             * real interrupt state — QEMU just needs to re-enter vm_run
             * so the kernel can inject pending interrupts.
             * cpu_interrupt + halted=false ensures the thread loop
             * calls bhyve_vcpu_exec instead of going back to sleep.
             */
            cpu->halted = false;
            cpu_interrupt(cpu, CPU_INTERRUPT_HARD);
        } else {
            /* Non-halted CPU: force vm_run exit so kernel can
             * inject pending LAPIC interrupts (e.g. during AP init) */
            cpu->exit_request = 1;
            qemu_cpu_kick(cpu);
        }
    }
}


#define VM_NAME "vm2"

/* From machine/vmm.h - interrupt injection info */
#ifndef VM_INTINFO_VALID
#define VM_INTINFO_VALID    0x80000000
#define VM_INTINFO_HWINTR   (0 << 8)
#endif

/* From x86/apicreg.h - APIC delivery modes for IPI handling */
#ifndef APIC_DELMODE_FIXED
#define APIC_DELMODE_FIXED      0x00000000
#define APIC_DELMODE_LOWPRIO    0x00000100
#define APIC_DELMODE_NMI        0x00000400
#define APIC_DELMODE_INIT       0x00000500
#define APIC_DELMODE_STARTUP    0x00000600
#endif

struct AccelCPUState {
    struct vcpu *vcpu;
    uint64_t tpr;

    /* QEMU State =/= VMM state */
    bool dirty;

    /* True after INIT, cleared on first SIPI.  Prevents duplicate
     * SIPIs (INIT-SIPI-SIPI protocol) from resetting an already-
     * running AP back to real mode. */
    bool wait_for_sipi;

    /* Per-vCPU LAPIC poll timer for waking halted vCPUs */
    QEMUTimer *lapic_poll_timer;

    /* Per-vCPU SMP state — these were previously function-scoped statics
     * shared across all vCPUs, causing race conditions with SMP. */
    int hwintr_state;       /* 0=off, 1=masked(IF=0), 2=grace(scrubbing), 3=done */
    long hwintr_grace_runs; /* runs remaining in grace period (state 2) */
    long smp_rearm_mask;    /* >0: re-mask HWINTR for this many more runs (SMP safety) */
    bool fsgsbase_forced;   /* CR4.FSGSBASE force-set done for this vCPU */

    /* Per-vCPU exit counters for SMP diagnostics */
    long vcpu_exit_inout;
    long vcpu_exit_hlt;
    long vcpu_exit_pause;
    long vcpu_exit_bogus;
    long vcpu_exit_ipi;
    long vcpu_exit_other;
    long vcpu_vm_run_total;
    int64_t vcpu_last_stats_ns;  /* last time we printed stats */

    /* Per-vCPU INOUT loop detector (was static — race condition with SMP) */
    uint64_t last_inout_rip;
    int inout_repeat_count;
    bool pm_timer_warned;

    /* Anti-freeze: time-window exit storm detector (v2).
     * Counts ALL non-idle exits in a sliding window.  A single
     * different-RIP exit no longer resets the counter. */
};

/* -------------------------------------------------------------------------- */

/*
 * MADT Patching for SMP
 *
 * The BHYVE_UEFI firmware generates its own ACPI tables including a MADT
 * with only 1 CPU entry (APIC ID 0). It doesn't read QEMU's fw_cfg ACPI
 * tables like OVMF does. To support SMP, we directly scan guest memory
 * for the MADT ("APIC" signature) and add missing CPU entries.
 *
 * The firmware places ACPI tables in the high memory region (typically
 * around 0xBFBF0000-0xC0000000 for a 3-4GB guest). We scan this region
 * for the MADT signature when the kernel first enters long mode.
 */
static bool madt_patched = false;

static uint8_t acpi_checksum(const uint8_t *data, int len)
{
    uint8_t sum = 0;
    for (int i = 0; i < len; i++)
        sum += data[i];
    return sum;
}

static void patch_madt_for_smp(struct vmctx *vm, int num_cpus)
{
    /*
     * BHYVE_UEFI places ACPI tables in the firmware area around 0xBFBF0000
     * (inside the PCI hole, above lowmem). This area cannot be accessed via
     * vm_get_guestmem_from_ctx() or vm_map_gpa(). Use QEMU's
     * cpu_physical_memory_read/write which goes through the QEMU memory
     * subsystem and can access any mapped GPA including firmware regions.
     *
     * Scan 0xBFBF0000-0xBFC00000 for the MADT (signature "APIC").
     */
    uint64_t madt_gpa = 0;
    uint8_t buf[4096];  /* read buffer for scanning */

    /* Scan the BHYVE firmware ACPI area in 4K pages */
    uint64_t scan_start = 0xBFBF0000ULL;
    uint64_t scan_end   = 0xBFC00000ULL;


    for (uint64_t page = scan_start; page < scan_end; page += 0x1000) {
        cpu_physical_memory_read(page, buf, 0x1000);

        for (int off = 0; off + 44 <= 0x1000; off += 16) {
            if (buf[off] != 'A' || buf[off+1] != 'P' ||
                buf[off+2] != 'I' || buf[off+3] != 'C')
                continue;

            uint32_t tbl_len = *(uint32_t *)(buf + off + 4);
            if (tbl_len < 44 || tbl_len > 4096)
                continue;

            if (memcmp(buf + off + 10, "BHYVE", 5) != 0)
                continue;

            /* Re-read the full table if it spans beyond current page */
            uint8_t full_tbl[4096];
            uint64_t tbl_gpa = page + off;
            cpu_physical_memory_read(tbl_gpa, full_tbl, tbl_len);

            uint8_t csum = acpi_checksum(full_tbl, tbl_len);

            if (csum == 0 && tbl_len >= 62) {
                madt_gpa = tbl_gpa;
                break;
            }
        }
        if (madt_gpa) break;
    }

    if (!madt_gpa) {
        return;
    }

    /* Read the full MADT */
    uint8_t madt_buf[4096];
    uint32_t madt_len;
    cpu_physical_memory_read(madt_gpa, madt_buf, 44);
    madt_len = *(uint32_t *)(madt_buf + 4);
    cpu_physical_memory_read(madt_gpa, madt_buf, madt_len);

    /* Count existing LAPIC entries (type 0, length 8) */
    int existing_cpus = 0;
    int offset = 44; /* skip ACPI header (36) + local APIC addr (4) + flags (4) */
    while (offset + 2 <= (int)madt_len) {
        uint8_t type = madt_buf[offset];
        uint8_t len = madt_buf[offset + 1];
        if (len == 0) break;
        if (type == 0 && len == 8)
            existing_cpus++;
        offset += len;
    }


    if (existing_cpus >= num_cpus) {
        madt_patched = true;
        return;
    }

    /* Build patched MADT in a temp buffer */
    uint8_t new_madt[2048];
    int new_offset = 0;

    /* Copy header (44 bytes) */
    memcpy(new_madt, madt_buf, 44);
    new_offset = 44;

    /* Walk existing entries, insert new LAPIC entries after last LAPIC */
    offset = 44;
    bool added_new = false;
    while (offset + 2 <= (int)madt_len) {
        uint8_t type = madt_buf[offset];
        uint8_t len = madt_buf[offset + 1];
        if (len == 0) break;

        /* Copy this entry */
        if (new_offset + len <= 2048) {
            memcpy(new_madt + new_offset, madt_buf + offset, len);
            new_offset += len;
        }

        /* After last LAPIC entry, insert new CPU entries */
        if (type == 0 && !added_new) {
            int next_off = offset + len;
            uint8_t next_type = (next_off + 2 <= (int)madt_len) ?
                                madt_buf[next_off] : 0xFF;
            if (next_type != 0) {
                for (int cpu_id = existing_cpus; cpu_id < num_cpus; cpu_id++) {
                    if (new_offset + 8 > 2048) break;
                    new_madt[new_offset + 0] = 0;      /* Type: Local APIC */
                    new_madt[new_offset + 1] = 8;      /* Length */
                    new_madt[new_offset + 2] = cpu_id;  /* ACPI Processor ID */
                    new_madt[new_offset + 3] = cpu_id;  /* APIC ID */
                    new_madt[new_offset + 4] = 1;       /* Flags: enabled */
                    new_madt[new_offset + 5] = 0;
                    new_madt[new_offset + 6] = 0;
                    new_madt[new_offset + 7] = 0;
                    new_offset += 8;
                }
                added_new = true;
            }
        }
        offset += len;
    }

    /* Update length and checksum */
    *(uint32_t *)(new_madt + 4) = new_offset;
    new_madt[9] = 0;
    new_madt[9] = (uint8_t)(0 - acpi_checksum(new_madt, new_offset));

    /* Write patched MADT back to guest memory via QEMU memory subsystem */
    cpu_physical_memory_write(madt_gpa, new_madt, new_offset);


    madt_patched = true;
}

static bool bhyve_allowed;

int
bhyve_enabled(void) {
    return bhyve_allowed;
}

/*
 * Inject a vector into a vCPU's kernel vLAPIC using MSI.
 *
 * Uses vm_lapic_msi() instead of vm_lapic_irq() because:
 * - vm_lapic_irq uses VMMDEV_IOCTL_LOCK_ONE_VCPU which calls
 *   vcpu_lock_one() → blocks waiting for the target vCPU to become
 *   VCPU_IDLE.  When called from pre_run (which holds BQL) or from
 *   PIC/IOAPIC handlers, this can stall or deadlock.
 * - vm_lapic_msi uses no vCPU locking at all.  The kernel's
 *   lapic_intr_msi() → vlapic_deliver_intr() → lapic_set_intr()
 *   sets the IRR bit atomically and calls vcpu_notify_event() to
 *   wake sleeping vCPUs.  Safe from any thread context.
 *
 * MSI address format (x86, physical delivery):
 *   bits[31:20] = 0xFEE (fixed base)
 *   bits[19:12] = destination APIC ID
 *   bit 3 = RH=0 (no redirect hint)
 *   bit 2 = DM=0 (physical destination)
 *
 * MSI data format:
 *   bits[7:0] = vector
 *   bits[10:8] = 000 (fixed delivery mode)
 *   bit 14 = 0 (edge trigger)
 */
void bhyve_inject_lapic_irq(CPUState *cpu, int vector)
{
    if (!cpu || vector < 32) {
        return;
    }

    uint64_t msi_addr = 0xFEE00000ULL | ((uint64_t)cpu->cpu_index << 12);
    uint64_t msi_data = (uint64_t)(vector & 0xFF);

    int err = vm_lapic_msi(bhyve_mach.vm, msi_addr, msi_data);
    if (err) {
        BHYVE_DPRINTF("[LAPIC-MSI] vm_lapic_msi(cpu%d, vec=%d) failed: %d\n",
                      cpu->cpu_index, vector, err);
    }
}

static enum host_vendor get_cpu_vendor(void) {
    unsigned int eax = 0;
    unsigned int regs[4];
    char vendor[13];

    __asm__ __volatile__("cpuid"
                         : "=a"(regs[0]), "=b"(regs[1]), "=c"(regs[2]),
                           "=d"(regs[3])
                         : "a"(eax)
    );

    *(unsigned int *)(vendor + 0) = regs[0]; /* EBX */
    *(unsigned int *)(vendor + 4) = regs[2]; /* EDX */
    *(unsigned int *)(vendor + 8) = regs[1]; /* ECX */
    vendor[12] = '\0';

    if (strstr(vendor, "Intel")) {
        return VENDOR_INTEL;
    } else if (strstr(vendor, "AMD")) {
        return VENDOR_AMD;
    } else {
        return VENDOR_UNKNOWN;
    }
}

/* -------------------------------------------------------------------------- */

struct bhyve_machine bhyve_mach;

/* -------------------------------------------------------------------------- */

struct vcpu *bhyve_get_vcpu(CPUState *cpu) {
    return cpu->accel->vcpu;
}

static struct bhyve_machine *get_bhyve_mach(void) {
    return &bhyve_mach;
}

static void dump_registers(struct vcpu *vcpu) {
    uint64_t val;
    int err;

    printf("\n=== Register Dump ===\n");

    const struct {
        const char *name;
        int reg;
    } regs[] = {
        { "RAX", VM_REG_GUEST_RAX },
        { "RBX", VM_REG_GUEST_RBX },
        { "RCX", VM_REG_GUEST_RCX },
        { "RDX", VM_REG_GUEST_RDX },
        { "RSI", VM_REG_GUEST_RSI },
        { "RDI", VM_REG_GUEST_RDI },
        { "RBP", VM_REG_GUEST_RBP },
        { "RSP", VM_REG_GUEST_RSP },
        { "RIP", VM_REG_GUEST_RIP },
        { "RFLAGS", VM_REG_GUEST_RFLAGS },
    };

    for (int i = 0; i < sizeof(regs)/sizeof(regs[0]); i++) {
        err = vm_get_register(vcpu, regs[i].reg, &val);
        if (err != 0) {
            printf("%s: ERROR (%d)\n", regs[i].name, err);
        } else {
            printf("%-8s = 0x%016" PRIx64 "\n", regs[i].name, val);
        }
    }

    const struct {
        const char *name;
        int reg;
    } segs[] = {
        { "CS", VM_REG_GUEST_CS },
        { "DS", VM_REG_GUEST_DS },
        { "ES", VM_REG_GUEST_ES },
        { "SS", VM_REG_GUEST_SS },
        { "FS", VM_REG_GUEST_FS },
        { "GS", VM_REG_GUEST_GS },
    };

    struct seg_desc desc;
    for (int i = 0; i < sizeof(segs)/sizeof(segs[0]); i++) {
        err = vm_get_seg_desc(vcpu, segs[i].reg, &desc);
        if (err != 0) {
            printf("%s: ERROR (%d)\n", segs[i].name, err);
        } else {
            printf("%s: base=0x%016" PRIx64 " limit=0x%08x access=0x%08x\n",
                segs[i].name, desc.base, desc.limit, desc.access);
        }
    }

    printf("======================\n\n");
}

/* -------------------------------------------------------------------------- */

/*
static int
vmm_set_segment(struct vcpu *vcpu, int reg, const SegmentCache *qseg)
{
    int error;
    error = vm_set_register(vcpu, reg, qseg->selector);
    if (error) {
        return -1;
    }

    error = vm_set_desc(vcpu, reg, qseg->base, qseg->limit, qseg->flags);
    if (error) {
        return -1;
    }
    return 0;
}

static int
vmm_get_segment(struct vcpu *vcpu, int reg, const SegmentCache *qseg)
{
    int error;
    error = vm_get_register(vcpu, reg, (const uint64_t*)&qseg->flags);
    if (error) {
        return error;
    }
    error = vm_get_desc(vcpu, reg, (const unsigned long*)&qseg->base, &qseg->limit, (const unsigned int*)&qseg->flags);
    if (error) {
        return error;
    }
    return 0;
}
*/

static int vmm_set_registers(CPUState *cpu) {
    CPUX86State *env = cpu_env(cpu);
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu* vcpu = qcpu->vcpu;

    /* GPRs */
    int ret;
    int any_fail __attribute__((unused)) = 0;

#define VM_SET_REG_CHECK(name, reg, val) do { \
    ret = vm_set_register(vcpu, (reg), (val)); \
    if (ret != 0) any_fail = ret; \
} while(0)

#define VM_SET_DESC_CHECK(name, reg, base, limit, ar) do { \
    ret = vm_set_desc(vcpu, (reg), (base), (limit), (ar)); \
    if (ret != 0) any_fail = ret; \
} while(0)

    // General-Purpose Registers
    VM_SET_REG_CHECK("RAX", VM_REG_GUEST_RAX, env->regs[R_EAX]);
    VM_SET_REG_CHECK("RBX", VM_REG_GUEST_RBX, env->regs[R_EBX]);
    VM_SET_REG_CHECK("RCX", VM_REG_GUEST_RCX, env->regs[R_ECX]);
    VM_SET_REG_CHECK("RDX", VM_REG_GUEST_RDX, env->regs[R_EDX]);
    VM_SET_REG_CHECK("RSI", VM_REG_GUEST_RSI, env->regs[R_ESI]);
    VM_SET_REG_CHECK("RDI", VM_REG_GUEST_RDI, env->regs[R_EDI]);
    VM_SET_REG_CHECK("RBP", VM_REG_GUEST_RBP, env->regs[R_EBP]);
    VM_SET_REG_CHECK("RSP", VM_REG_GUEST_RSP, env->regs[R_ESP]);
#ifdef TARGET_X86_64
    VM_SET_REG_CHECK("R8", VM_REG_GUEST_R8, env->regs[R_R8]);
    VM_SET_REG_CHECK("R9", VM_REG_GUEST_R9, env->regs[R_R9]);
    VM_SET_REG_CHECK("R10", VM_REG_GUEST_R10, env->regs[R_R10]);
    VM_SET_REG_CHECK("R11", VM_REG_GUEST_R11, env->regs[R_R11]);
    VM_SET_REG_CHECK("R12", VM_REG_GUEST_R12, env->regs[R_R12]);
    VM_SET_REG_CHECK("R13", VM_REG_GUEST_R13, env->regs[R_R13]);
    VM_SET_REG_CHECK("R14", VM_REG_GUEST_R14, env->regs[R_R14]);
    VM_SET_REG_CHECK("R15", VM_REG_GUEST_R15, env->regs[R_R15]);
#endif

    // RIP and RFLAGS
    VM_SET_REG_CHECK("RIP", VM_REG_GUEST_RIP, env->eip);
    VM_SET_REG_CHECK("RFLAGS", VM_REG_GUEST_RFLAGS, env->eflags);

    /*
     * Segment Registers — full descriptors (selector + base + limit + access).
     * VMX requires complete segment state in VMCS, not just selectors.
     *
     * QEMU flags layout (bits of GDT descriptor second dword):
     *   TYPE[11:8] S[12] DPL[14:13] P[15] L[21] DB[22] G[23]
     * VMX access rights layout:
     *   TYPE[3:0] S[4] DPL[6:5] P[7] reserved[11:8] L[13] DB[14] G[15] Unusable[16]
     *
     * Conversion: shift QEMU flags right by 8, mask relevant bits,
     * then handle L/DB/G which are at different positions.
     */
#define QEMU_FLAGS_TO_VMX_AR(flags) ({                               \
    uint32_t _f = (flags);                                           \
    uint32_t _lo = (_f >> 8) & 0xFF;   /* TYPE,S,DPL,P */           \
    uint32_t _l  = (_f >> 21) & 1;     /* L bit */                  \
    uint32_t _db = (_f >> 22) & 1;     /* D/B bit */                \
    uint32_t _g  = (_f >> 23) & 1;     /* G bit */                  \
    uint32_t _ar = _lo | (_l << 13) | (_db << 14) | (_g << 15);    \
    /* If P=0, mark segment unusable */                              \
    if (!(_ar & 0x80)) _ar |= (1 << 16);                            \
    _ar;                                                             \
})

    {
        struct { int reg; int qemu_idx; const char *name; } segs[] = {
            { VM_REG_GUEST_CS, R_CS, "CS" },
            { VM_REG_GUEST_DS, R_DS, "DS" },
            { VM_REG_GUEST_ES, R_ES, "ES" },
            { VM_REG_GUEST_SS, R_SS, "SS" },
            { VM_REG_GUEST_FS, R_FS, "FS" },
            { VM_REG_GUEST_GS, R_GS, "GS" },
        };
        for (int i = 0; i < 6; i++) {
            uint32_t vmx_ar = QEMU_FLAGS_TO_VMX_AR(env->segs[segs[i].qemu_idx].flags);
            VM_SET_REG_CHECK(segs[i].name, segs[i].reg,
                              env->segs[segs[i].qemu_idx].selector);
            VM_SET_DESC_CHECK(segs[i].name, segs[i].reg,
                              env->segs[segs[i].qemu_idx].base,
                              env->segs[segs[i].qemu_idx].limit,
                              vmx_ar);
        }
    }
    // LDTR
    {
        uint32_t vmx_ar = QEMU_FLAGS_TO_VMX_AR(env->ldt.flags);
        VM_SET_REG_CHECK("LDTR", VM_REG_GUEST_LDTR, env->ldt.selector);
        VM_SET_DESC_CHECK("LDTR", VM_REG_GUEST_LDTR,
                          env->ldt.base, env->ldt.limit, vmx_ar);
    }
    // TR — must not be unusable, force P=1
    {
        uint32_t vmx_ar = QEMU_FLAGS_TO_VMX_AR(env->tr.flags);
        vmx_ar &= ~(1 << 16); /* TR must never be unusable */
        if (!(vmx_ar & 0x80)) vmx_ar |= 0x80; /* force P=1 */
        if (!(vmx_ar & 0x0F)) vmx_ar |= 0x0B; /* force type=busy 32-bit TSS */
        VM_SET_REG_CHECK("TR", VM_REG_GUEST_TR, env->tr.selector);
        VM_SET_DESC_CHECK("TR", VM_REG_GUEST_TR,
                          env->tr.base,
                          env->tr.limit >= 0x67 ? env->tr.limit : 0x67,
                          vmx_ar);
    }
#undef QEMU_FLAGS_TO_VMX_AR

    // Descriptor Table Registers
    VM_SET_DESC_CHECK("GDTR", VM_REG_GUEST_GDTR, env->gdt.base, env->gdt.limit, 0);
    VM_SET_DESC_CHECK("IDTR", VM_REG_GUEST_IDTR, env->idt.base, env->idt.limit, 0);

    // Control Registers
    VM_SET_REG_CHECK("CR0", VM_REG_GUEST_CR0, env->cr[0]);
    VM_SET_REG_CHECK("CR2", VM_REG_GUEST_CR2, env->cr[2]);
    VM_SET_REG_CHECK("CR3", VM_REG_GUEST_CR3, env->cr[3]);
    VM_SET_REG_CHECK("CR4", VM_REG_GUEST_CR4, env->cr[4]);
    /*
     * Skip TPR: vmx_setreg has no special case for TPR (unlike vmx_getreg
     * which calls vlapic_get_cr8). The kernel's vlapic manages TPR
     * independently, and vm_set_register(TPR) returns EINVAL.
     */

    // Debug Registers
    VM_SET_REG_CHECK("DR0", VM_REG_GUEST_DR0, env->dr[0]);
    VM_SET_REG_CHECK("DR1", VM_REG_GUEST_DR1, env->dr[1]);
    VM_SET_REG_CHECK("DR2", VM_REG_GUEST_DR2, env->dr[2]);
    VM_SET_REG_CHECK("DR3", VM_REG_GUEST_DR3, env->dr[3]);
    VM_SET_REG_CHECK("DR6", VM_REG_GUEST_DR6, env->dr[6]);
    VM_SET_REG_CHECK("DR7", VM_REG_GUEST_DR7, env->dr[7]);

    // MSRs
    VM_SET_REG_CHECK("EFER", VM_REG_GUEST_EFER, env->efer);
#ifdef TARGET_X86_64
    VM_SET_REG_CHECK("FS_BASE", VM_REG_GUEST_FS_BASE, env->segs[R_FS].base);
    VM_SET_REG_CHECK("GS_BASE", VM_REG_GUEST_GS_BASE, env->segs[R_GS].base);
    VM_SET_REG_CHECK("KGS_BASE", VM_REG_GUEST_KGS_BASE, env->kernelgsbase);
#endif

#undef VM_SET_REG_CHECK
#undef VM_SET_DESC_CHECK
    return 0; /* Continue even if some registers fail (TPR, KGS_BASE etc.
               * are kernel-managed and vmx_setreg doesn't support SET) */
}

static int vmm_get_registers(CPUState *cpu) {
    CPUX86State *env = cpu_env(cpu);
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu *vcpu = qcpu->vcpu;
    uint64_t val;
    int ret;

    // General-Purpose Registers
    ret = vm_get_register(vcpu, VM_REG_GUEST_RAX, &val);
    if (ret != 0) return ret;
    env->regs[R_EAX] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RBX, &val);
    if (ret != 0) return ret;
    env->regs[R_EBX] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RCX, &val);
    if (ret != 0) return ret;
    env->regs[R_ECX] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RDX, &val);
    if (ret != 0) return ret;
    env->regs[R_EDX] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RSI, &val);
    if (ret != 0) return ret;
    env->regs[R_ESI] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RDI, &val);
    if (ret != 0) return ret;
    env->regs[R_EDI] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RBP, &val);
    if (ret != 0) return ret;
    env->regs[R_EBP] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RSP, &val);
    if (ret != 0) return ret;
    env->regs[R_ESP] = val;

#ifdef TARGET_X86_64
    ret = vm_get_register(vcpu, VM_REG_GUEST_R8, &val);
    if (ret != 0) return ret;
    env->regs[R_R8] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_R9, &val);
    if (ret != 0) return ret;
    env->regs[R_R9] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_R10, &val);
    if (ret != 0) return ret;
    env->regs[R_R10] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_R11, &val);
    if (ret != 0) return ret;
    env->regs[R_R11] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_R12, &val);
    if (ret != 0) return ret;
    env->regs[R_R12] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_R13, &val);
    if (ret != 0) return ret;
    env->regs[R_R13] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_R14, &val);
    if (ret != 0) return ret;
    env->regs[R_R14] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_R15, &val);
    if (ret != 0) return ret;
    env->regs[R_R15] = val;
#endif

    // RIP and RFLAGS
    ret = vm_get_register(vcpu, VM_REG_GUEST_RIP, &val);
    if (ret != 0) return ret;
    env->eip = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_RFLAGS, &val);
    if (ret != 0) return ret;
    env->eflags = val;

    /*
     * Segment Registers — full descriptors (selector + base + limit + flags).
     * Convert VMX access rights back to QEMU flags format.
     * VMX AR: TYPE[3:0] S[4] DPL[6:5] P[7] L[13] DB[14] G[15]
     * QEMU flags: TYPE[11:8] S[12] DPL[14:13] P[15] L[21] DB[22] G[23]
     */
#define VMX_AR_TO_QEMU_FLAGS(ar) ({                                  \
    uint32_t _a = (ar);                                              \
    uint32_t _lo = (_a & 0xFF) << 8; /* TYPE,S,DPL,P -> bits 8-15 */\
    uint32_t _l  = ((_a >> 13) & 1) << 21;                          \
    uint32_t _db = ((_a >> 14) & 1) << 22;                          \
    uint32_t _g  = ((_a >> 15) & 1) << 23;                          \
    _lo | _l | _db | _g;                                             \
})
    {
        struct { int reg; int qemu_idx; } segs[] = {
            { VM_REG_GUEST_CS, R_CS },
            { VM_REG_GUEST_DS, R_DS },
            { VM_REG_GUEST_ES, R_ES },
            { VM_REG_GUEST_SS, R_SS },
            { VM_REG_GUEST_FS, R_FS },
            { VM_REG_GUEST_GS, R_GS },
        };
        for (int i = 0; i < 6; i++) {
            uint64_t base;
            uint32_t limit, access;
            ret = vm_get_register(vcpu, segs[i].reg, &val);
            if (ret != 0) return ret;
            env->segs[segs[i].qemu_idx].selector = (uint16_t)val;
            ret = vm_get_desc(vcpu, segs[i].reg, &base, &limit, &access);
            if (ret != 0) return ret;
            env->segs[segs[i].qemu_idx].base = base;
            env->segs[segs[i].qemu_idx].limit = limit;
            env->segs[segs[i].qemu_idx].flags = VMX_AR_TO_QEMU_FLAGS(access);
        }
    }
    // LDTR
    {
        uint64_t base;
        uint32_t limit, access;
        ret = vm_get_register(vcpu, VM_REG_GUEST_LDTR, &val);
        if (ret != 0) return ret;
        env->ldt.selector = (uint16_t)val;
        ret = vm_get_desc(vcpu, VM_REG_GUEST_LDTR, &base, &limit, &access);
        if (ret != 0) return ret;
        env->ldt.base = base;
        env->ldt.limit = limit;
        env->ldt.flags = VMX_AR_TO_QEMU_FLAGS(access);
    }
    // TR
    {
        uint64_t base;
        uint32_t limit, access;
        ret = vm_get_register(vcpu, VM_REG_GUEST_TR, &val);
        if (ret != 0) return ret;
        env->tr.selector = (uint16_t)val;
        ret = vm_get_desc(vcpu, VM_REG_GUEST_TR, &base, &limit, &access);
        if (ret != 0) return ret;
        env->tr.base = base;
        env->tr.limit = limit;
        env->tr.flags = VMX_AR_TO_QEMU_FLAGS(access);
    }
    // GDTR / IDTR (base + limit)
    {
        uint64_t base;
        uint32_t limit, dummy;
        ret = vm_get_desc(vcpu, VM_REG_GUEST_GDTR, &base, &limit, &dummy);
        if (ret != 0) return ret;
        env->gdt.base = base;
        env->gdt.limit = limit;
        ret = vm_get_desc(vcpu, VM_REG_GUEST_IDTR, &base, &limit, &dummy);
        if (ret != 0) return ret;
        env->idt.base = base;
        env->idt.limit = limit;
    }
#undef VMX_AR_TO_QEMU_FLAGS

    // Control Registers
    ret = vm_get_register(vcpu, VM_REG_GUEST_CR0, &val);
    if (ret != 0) return ret;
    env->cr[0] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_CR2, &val);
    if (ret != 0) return ret;
    env->cr[2] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_CR3, &val);
    if (ret != 0) return ret;
    env->cr[3] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_CR4, &val);
    if (ret != 0) return ret;
    env->cr[4] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_TPR, &val);
    if (ret != 0) return ret;
    qcpu->tpr = val;

    // Debug Registers
    ret = vm_get_register(vcpu, VM_REG_GUEST_DR0, &val);
    if (ret != 0) return ret;
    env->dr[0] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_DR1, &val);
    if (ret != 0) return ret;
    env->dr[1] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_DR2, &val);
    if (ret != 0) return ret;
    env->dr[2] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_DR3, &val);
    if (ret != 0) return ret;
    env->dr[3] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_DR6, &val);
    if (ret != 0) return ret;
    env->dr[6] = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_DR7, &val);
    if (ret != 0) return ret;
    env->dr[7] = val;

    // MSRs
    ret = vm_get_register(vcpu, VM_REG_GUEST_EFER, &val);
    if (ret != 0) return ret;
    env->efer = val;

#ifdef TARGET_X86_64
    ret = vm_get_register(vcpu, VM_REG_GUEST_FS_BASE, &val);
    if (ret != 0) return ret;
    env->segs[R_FS].base = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_GS_BASE, &val);
    if (ret != 0) return ret;
    env->segs[R_GS].base = val;

    ret = vm_get_register(vcpu, VM_REG_GUEST_KGS_BASE, &val);
    if (ret != 0) return ret;
    env->kernelgsbase = val;
#endif

    return 0; // Success
}

/* -------------------------------------------------------------------------- */

static int
vmm_io_callback(struct vm_qio *io)
{
    MemTxAttrs attrs = { 0 };
    int ret;

    /*
     * ACPI PM Timer (port 0x408): if address_space_rw returns 0xffffffff
     * it means the PIIX4 PM I/O region isn't mapped yet. Provide the
     * correct PM Timer value directly from the virtual clock.
     * PM Timer ticks at 3.579545 MHz, 24-bit counter.
     */
    ret = address_space_rw(&address_space_io, io->port, attrs, io->data,
        io->size, !io->in);
    if (io->port == 0x408 && io->in && io->size == 4) {
        uint32_t val = *(uint32_t *)io->data;
        if (val == 0xffffffff) {
            /* Region not mapped — compute PM timer value directly */
            int64_t ns = qemu_clock_get_ns(QEMU_CLOCK_VIRTUAL);
            uint32_t ticks = (uint32_t)muldiv64(ns, 3579545, 1000000000LL);
            ticks &= 0xffffff; /* 24-bit counter */
            *(uint32_t *)io->data = ticks;
        }
    }
    {
        static int pm1_diag = 0;
        if (io->port >= 0x400 && io->port <= 0x407 && pm1_diag < 30) {
            pm1_diag++;
            BHYVE_DPRINTF("[PM1-IO] #%d port=0x%x %s size=%zu data=0x%04x ret=%d\n",
                    pm1_diag, io->port, io->in ? "IN" : "OUT",
                    io->size, *(uint16_t *)io->data, ret);
        }
        /*
         * bhyve SCI fix: the BHYVE firmware asserts SCI (IRQ 9) directly
         * through the kernel's vioapic, bypassing QEMU. QEMU never sees
         * the assertion, so it can't deassert it. Force-deassert IRQ 9
         * in both vatpic and vioapic whenever the guest reads PM1_STS=0
         * (meaning no ACPI events are pending from QEMU's perspective).
         * This breaks the infinite SCI handler re-entry loop that freezes
         * SMP4+ boots.
         */
        if (io->port == 0x400 && io->in && *(uint16_t *)io->data == 0) {
            static int sci_deassert_count = 0;
            vm_isa_deassert_irq(bhyve_mach.vm, 9, 9);
            sci_deassert_count++;
            /* Dump LAPIC state at 1000 reads to see stuck IRR/ISR */
            if (sci_deassert_count == 1000) {
                struct vm_lapic_state dbg_lapic;
                AccelCPUState *qcpu = current_cpu->accel;
                memset(&dbg_lapic, 0, sizeof(dbg_lapic));
                if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE,
                               &dbg_lapic) == 0) {
                    /* vm_lapic_state has fields[] array, each with .data
                     * Index = APIC register offset / 0x10 */
                    BHYVE_DPRINTF("[SCI-DUMP] vcpu%d LAPIC after 1000 PM1 reads:\n",
                            current_cpu->cpu_index);
                    /* IRR: registers 0x200-0x270 → indices 0x20-0x27 */
                    BHYVE_DPRINTF("  IRR: %08x %08x %08x %08x %08x %08x %08x %08x\n",
                            dbg_lapic.fields[0x20].data, dbg_lapic.fields[0x21].data,
                            dbg_lapic.fields[0x22].data, dbg_lapic.fields[0x23].data,
                            dbg_lapic.fields[0x24].data, dbg_lapic.fields[0x25].data,
                            dbg_lapic.fields[0x26].data, dbg_lapic.fields[0x27].data);
                    /* ISR: registers 0x100-0x170 → indices 0x10-0x17 */
                    BHYVE_DPRINTF("  ISR: %08x %08x %08x %08x %08x %08x %08x %08x\n",
                            dbg_lapic.fields[0x10].data, dbg_lapic.fields[0x11].data,
                            dbg_lapic.fields[0x12].data, dbg_lapic.fields[0x13].data,
                            dbg_lapic.fields[0x14].data, dbg_lapic.fields[0x15].data,
                            dbg_lapic.fields[0x16].data, dbg_lapic.fields[0x17].data);
                    /* TMR: registers 0x180-0x1F0 → indices 0x18-0x1F */
                    BHYVE_DPRINTF("  TMR: %08x %08x %08x %08x %08x %08x %08x %08x\n",
                            dbg_lapic.fields[0x18].data, dbg_lapic.fields[0x19].data,
                            dbg_lapic.fields[0x1A].data, dbg_lapic.fields[0x1B].data,
                            dbg_lapic.fields[0x1C].data, dbg_lapic.fields[0x1D].data,
                            dbg_lapic.fields[0x1E].data, dbg_lapic.fields[0x1F].data);
                }
            }
        }
    }
    if (ret != MEMTX_OK) {
        error_report("Bhyve: I/O Transaction Failed "
            "[%s, port=%u, size=%zu]", (io->in ? "in" : "out"),
            io->port, io->size);
    }

    current_cpu->accel->dirty = false;
    return 0;
}

static int
vmm_mem_callback(struct vm_qmem *mem)
{

    address_space_rw(&address_space_memory, mem->gpa, MEMTXATTRS_UNSPECIFIED,
                     mem->data, mem->size, mem->write);

    current_cpu->accel->dirty = false;
    return 0;
}

/* Directly copy from Bhyve */
static int bhyve_intel_rdmsr(uint32_t num, uint64_t* val) {
    int error = 0;
    switch (num) {
    case MSR_BIOS_SIGN:
    case MSR_IA32_PLATFORM_ID:
    case MSR_PKG_ENERGY_STATUS:
    case MSR_PP0_ENERGY_STATUS:
    case MSR_PP1_ENERGY_STATUS:
    case MSR_DRAM_ENERGY_STATUS:
    case MSR_MISC_FEATURE_ENABLES:
        *val = 0;
        break;
    case MSR_RAPL_POWER_UNIT:
        /*
            * Use the default value documented in section
            * "RAPL Interfaces" in Intel SDM vol3.
            */
        *val = 0x000a1003;
        break;
    case MSR_IA32_FEATURE_CONTROL:
        /*
            * Windows guests check this MSR.
            * Set the lock bit to avoid writes
            * to this MSR.
            */
        *val = IA32_FEATURE_CONTROL_LOCK;
        break;
    default:
        error = -1;
        break;
    }
    return error;
}

static int bhyve_amd_rdmsr(uint32_t num, uint64_t* val) {
    int error = 0;
    switch (num) {
    case MSR_BIOS_SIGN:
        *val = 0;
        break;
    case MSR_HWCR:
        /*
            * Bios and Kernel Developer's Guides for AMD Families
            * 12H, 14H, 15H and 16H.
            */
        *val = 0x01000010;	/* Reset value */
        *val |= 1 << 9;		/* MONITOR/MWAIT disable */
        break;

    case MSR_NB_CFG1:
    case MSR_LS_CFG:
    case MSR_IC_CFG:
        /*
            * The reset value is processor family dependent so
            * just return 0.
            */
        *val = 0;
        break;

    case MSR_PERFEVSEL0:
    case MSR_PERFEVSEL1:
    case MSR_PERFEVSEL2:
    case MSR_PERFEVSEL3:
        /*
            * PerfEvtSel MSRs are not properly virtualized so just
            * return zero.
            */
        *val = 0;
        break;

    case MSR_K7_PERFCTR0:
    case MSR_K7_PERFCTR1:
    case MSR_K7_PERFCTR2:
    case MSR_K7_PERFCTR3:
        /*
            * PerfCtr MSRs are not properly virtualized so just
            * return zero.
            */
        *val = 0;
        break;

    case MSR_SMM_ADDR:
    case MSR_SMM_MASK:
        /*
            * Return the reset value defined in the AMD Bios and
            * Kernel Developer's Guide.
            */
        *val = 0;
        break;

    case MSR_P_STATE_LIMIT:
    case MSR_P_STATE_CONTROL:
    case MSR_P_STATE_STATUS:
    case MSR_P_STATE_CONFIG(0):	/* P0 configuration */
        *val = 0;
        break;

    /*
        * OpenBSD guests test bit 0 of this MSR to detect if the
        * workaround for erratum 721 is already applied.
        * https://support.amd.com/TechDocs/41322_10h_Rev_Gd.pdf
        */
    case 0xC0011029:
        *val = 1;
        break;

    default:
        error = -1;
        break;
    }
    return error;
}

/* rdmsr & wrmsr */
static int bhyve_rdmsr(struct vcpu* vcpu, struct vm_exit *vme) {
    struct bhyve_machine* mach = get_bhyve_mach();
    int error;
    uint32_t num = vme->u.msr.code;
    uint64_t val = 0;

    switch (mach->cpu_vendor) {
    case VENDOR_INTEL:
        error = bhyve_intel_rdmsr(num, &val);
        break;
    case VENDOR_AMD:
        error = bhyve_amd_rdmsr(num, &val);
        break;
    case VENDOR_UNKNOWN:
        return -1;
    }

    if (error) {
        /* Unknown MSR: return 0 to guest (standard virtualization behavior) */
        val = 0;
    }

    vm_set_register(vcpu, VM_REG_GUEST_RAX, val);
    vm_set_register(vcpu, VM_REG_GUEST_RDX, val >> 32);

    return 0;
}

static int bhyve_intel_wrmsr(uint32_t num) {
    switch (num) {
    case 0xd04:		/* Sandy Bridge uncore PMCs */
    case 0xc24:
        return (0);
    case MSR_BIOS_UPDT_TRIG:
        return (0);
    case MSR_BIOS_SIGN:
        return (0);
    default:
        break;
    }
    return 0;
}

static int bhyve_amd_wrmsr(uint32_t num) {
    switch (num) {
    case MSR_HWCR:
        /*
            * Ignore writes to hardware configuration MSR.
            */
        return (0);

    case MSR_NB_CFG1:
    case MSR_LS_CFG:
    case MSR_IC_CFG:
        return (0);	/* Ignore writes */

    case MSR_PERFEVSEL0:
    case MSR_PERFEVSEL1:
    case MSR_PERFEVSEL2:
    case MSR_PERFEVSEL3:
        /* Ignore writes to the PerfEvtSel MSRs */
        return (0);

    case MSR_K7_PERFCTR0:
    case MSR_K7_PERFCTR1:
    case MSR_K7_PERFCTR2:
    case MSR_K7_PERFCTR3:
        /* Ignore writes to the PerfCtr MSRs */
        return (0);

    case MSR_P_STATE_CONTROL:
        /* Ignore write to change the P-state */
        return (0);

    default:
        break;
    }
    return 0;
}

static int bhyve_wrmsr(struct vm_exit *vme) {
    struct bhyve_machine* mach = get_bhyve_mach();
    int error;
    uint32_t num = vme->u.msr.code;
    switch (mach->cpu_vendor) {
    case VENDOR_INTEL:
        error = bhyve_intel_wrmsr(num);
        return error;
    case VENDOR_AMD:
        error = bhyve_amd_wrmsr(num);
        return error;
    case VENDOR_UNKNOWN:
        return -1;
    }

}

/* -------------------------------------------------------------------------- */

/*
 * BQL helpers for the vm_run loop.
 *
 * Between cpu_exec_start() and cpu_exec_end(), the vCPU is marked as
 * "running".  start_exclusive() (used by process_queued_cpu_work for
 * exclusive work items) waits for all running vCPUs to stop before
 * proceeding.  If a vCPU blocks on bql_lock() while still marked
 * running, and another vCPU holds BQL and calls start_exclusive(),
 * we get a deadlock: the exclusive holder waits for the running vCPU,
 * while the running vCPU waits for BQL.
 *
 * Fix: temporarily mark the vCPU as not-running before blocking on
 * BQL.  This matches the pattern in cpu-common.c:process_queued_cpu_work
 * and prevents the deadlock.
 */
static inline void bhyve_bql_lock_in_loop(CPUState *cpu) {
    cpu_exec_end(cpu);
    bql_lock();
}

static inline void bhyve_bql_unlock_in_loop(CPUState *cpu) {
    bql_unlock();
    cpu_exec_start(cpu);
}

static void bhyve_vcpu_pre_run(CPUState *cpu) {
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu *vcpu = qcpu->vcpu;
    X86CPU *x86_cpu = X86_CPU(cpu);
    uint8_t tpr;
    bool sync_tpr = false;

    /*
     * Fast path: skip BQL entirely when there's nothing to do.
     * Reading interrupt_request and pending IRQ bitmasks is safe without
     * BQL (they're set atomically by other threads via cpu_interrupt()).
     * This prevents BQL starvation when one vCPU is in a tight exit loop
     * (e.g., AP spin-waiting with thousands of PAUSE exits/sec).
     */
    uint32_t ireq = qatomic_read(&cpu->interrupt_request);
    uint32_t pic_pending = qatomic_read(&bhyve_pic_pending_irqs);
    uint32_t ioapic_pending = qatomic_read(&bhyve_ioapic_pending_irqs);
    if (ireq == 0 && pic_pending == 0 && ioapic_pending == 0) {
        /* Still need to sync TPR — but do it without BQL via kernel ioctl */
        return;
    }

    bhyve_bql_lock_in_loop(cpu);

    // TPR is always synced (check bhyve-apic)
    tpr = cpu_get_apic_tpr(x86_cpu->apic_state);
    if (tpr != qcpu->tpr) {
        qcpu->tpr = tpr;
        sync_tpr = true;
    }

    /*
     * Force the VCPU out of its inner loop to process any INIT requests
     * or commit pending TPR access.
     */
    if (cpu->interrupt_request & (CPU_INTERRUPT_INIT | CPU_INTERRUPT_TPR)) {
        cpu->exit_request = 1;
    }

    /* Handle NMIs (vmm takes care of nmi windows and interrupt shadows) */
    if (cpu->interrupt_request & CPU_INTERRUPT_NMI) {
        cpu->interrupt_request &= ~CPU_INTERRUPT_NMI;
        vm_inject_nmi(vcpu);
    }

    /* Don't want SMIs. */
    if (cpu->interrupt_request & CPU_INTERRUPT_SMI) {
        cpu->interrupt_request &= ~CPU_INTERRUPT_SMI;
    }

    /*
     * Handle pending hardware interrupts.
     *
     * With bhyve's in-kernel PIC (vatpic), interrupt injection is done
     * by the kernel's vmx_inject_interrupts() on vm_run entry. The
     * CPU_INTERRUPT_HARD flag here is just used to prevent the vcpu
     * from being halted in the main loop. Clear it and let the kernel
     * handle actual injection — it will check extint_pending and
     * vatpic_pending_intr on the next vmentry.
     */
    if (cpu->interrupt_request & CPU_INTERRUPT_HARD) {
        cpu_reset_interrupt(cpu, CPU_INTERRUPT_HARD);

        /*
         * Inject pending interrupts into the vLAPIC.
         *
         * PIC (8259) interrupts go to BSP only (cpu_index == 0).
         * IOAPIC interrupts can target any vCPU, but the current
         * code uses a global pending bitmask — for now inject on
         * the vCPU that had CPU_INTERRUPT_HARD set.
         *
         * bhyve's kernel vatpic/vioapic do NOT auto-inject into
         * the vLAPIC — vmx_inject_interrupts doesn't pick them up.
         * We must inject from userspace via vm_lapic_msi().
         */
        /*
         * PIC interrupts: only BSP (cpu_index 0) consumes these.
         * APs must not steal PIC IRQs from the pending bitmask.
         */
        uint32_t pending = 0;
        if (cpu->cpu_index == 0) {
            pending = __atomic_exchange_n(
                &bhyve_pic_pending_irqs, 0, __ATOMIC_ACQ_REL);
        }
        /*
         * Process ALL pending PIC interrupts, not just the lowest one.
         * Without this, high-frequency IRQ 0 (PIT timer) starves
         * higher-numbered IRQs like IRQ 14 (ATA), causing lost
         * interrupts and 30s boot timeouts.
         *
         * Uses vm_lapic_msi instead of vm_lapic_irq to avoid the
         * LOCK_ONE_VCPU deadlock when targeting non-self vCPUs.
         */
        while (pending) {
            int irq = __builtin_ctz(pending);
            pending &= ~(1u << irq);

            int pin = (irq == 0) ? 2 : irq;
            int vector = 0;

            if (pin < 24) {
                uint8_t qemu_vec = bhyve_ioapic_vectors[pin];
                if (qemu_vec >= 0x10) {
                    vector = qemu_vec;
                }
            }

            if (vector >= 32) {
                /* Route to correct vCPU based on IOAPIC RTE destination */
                uint8_t dest_id = (pin < 24) ?
                    bhyve_ioapic_destinations[pin] : 0xFF;
                int apic_id = (dest_id != 0xFF) ? dest_id : 0;

                uint64_t msi_addr = 0xFEE00000ULL |
                    ((uint64_t)apic_id << 12);
                uint64_t msi_data = (uint64_t)(vector & 0xFF);
                vm_lapic_msi(bhyve_mach.vm, msi_addr, msi_data);
            }
        }

        /*
         * Inject pending IOAPIC interrupts, routed to the correct vCPU.
         *
         * bhyve_ioapic_set_irq does NOT inject directly (that would
         * populate IRR immediately, causing the HLT handler to never
         * halt → 100% CPU spin loop). Instead, injection happens here
         * in pre_run, timed correctly before vm_run entry.
         */
        uint32_t ioapic_pending = __atomic_exchange_n(
            &bhyve_ioapic_pending_irqs, 0, __ATOMIC_ACQ_REL);
        while (ioapic_pending) {
            int pin = __builtin_ctz(ioapic_pending);
            ioapic_pending &= ~(1u << pin);

            int vector = (pin < 24) ? bhyve_ioapic_vectors[pin] : 0;
            if (vector >= 32) {
                /* Route to correct vCPU using MSI (no vCPU locking) */
                uint8_t dest_id = (pin < 24) ?
                    bhyve_ioapic_destinations[pin] : 0xFF;
                int apic_id = (dest_id != 0xFF) ? dest_id : 0;

                uint64_t msi_addr = 0xFEE00000ULL |
                    ((uint64_t)apic_id << 12);
                uint64_t msi_data = (uint64_t)(vector & 0xFF);
                vm_lapic_msi(bhyve_mach.vm, msi_addr, msi_data);
            }
        }
    }

    if (sync_tpr) {
        vm_set_register(vcpu, VM_REG_GUEST_TPR, qcpu->tpr);
    }

    bhyve_bql_unlock_in_loop(cpu);
}

static void bhyve_vcpu_post_run(CPUState *cpu) {
    CPUX86State *env = cpu_env(cpu);
    X86CPU *x86_cpu = X86_CPU(cpu);
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu *vcpu = qcpu->vcpu;
    uint64_t val;

    /*
     * Sync RIP from VMCS back to QEMU's env->eip.
     *
     * The kernel advances guest RIP by inst_length for exits that go to
     * userspace (INOUT, INST_EMUL, etc.) via vcpu->nextrip.  But QEMU's
     * env->eip is stale — it still holds the RIP from before the exit.
     * If vmm_set_registers() runs before the next vm_run (dirty=true),
     * it overwrites VMCS_GUEST_RIP with the stale env->eip, causing the
     * guest to re-execute the same instruction in an infinite loop.
     *
     * Fix: always read the current guest RIP from the VMCS after vm_run
     * and update env->eip so the two stay in sync.
     */
    vm_get_register(vcpu, VM_REG_GUEST_RIP, &val);
    env->eip = val;

    /*
     * Sync RAX — vm_assist_qio updates RAX in the VMCS for IN instructions
     * (port reads), but QEMU's env->regs[R_EAX] stays stale.
     */
    vm_get_register(vcpu, VM_REG_GUEST_RAX, &val);
    env->regs[R_EAX] = val;

    // Set Eflags
    vm_get_register(vcpu, VM_REG_GUEST_RFLAGS, &env->eflags);

    // TPR
    vm_get_register(vcpu, VM_REG_GUEST_TPR, &val);
    if (qcpu->tpr != val) {
        qcpu->tpr = val;
        bhyve_bql_lock_in_loop(cpu);
        cpu_set_apic_tpr(x86_cpu->apic_state, qcpu->tpr);
        bhyve_bql_unlock_in_loop(cpu);
    }
}

/* vCPU functions */
static int bhyve_vcpu_run(CPUState *cpu) {
    struct bhyve_machine* mach = get_bhyve_mach();
    X86CPU *x86_cpu = X86_CPU(cpu);
    CPUX86State *env = &x86_cpu->env;
    AccelCPUState* qcpu = cpu->accel;

	struct vm_exit vme;
	struct vm_run vmrun;
	int error, rc = 0;
	enum vm_exitcode exitcode;
    enum vm_suspend_how how;
	cpuset_t dmask;

    /* Ensure virtual clock is enabled — needed for PIT timer to fire */
    qemu_clock_enable(QEMU_CLOCK_VIRTUAL, true);

	vmrun.vm_exit = &vme;
	vmrun.cpuset = &dmask;
	vmrun.cpusetsize = sizeof(dmask);

    if (cpu->interrupt_request & CPU_INTERRUPT_INIT) {
        bhyve_cpu_synchronize_state(cpu);
        do_cpu_init(x86_cpu);
        qcpu->wait_for_sipi = true;  /* Accept next SIPI, reject duplicates */
        /* After cpu_reset, QEMU state is definitive. Write it to
         * kernel VMCS so subsequent reads won't get stale data. */
        vmm_set_registers(cpu);
        qcpu->dirty = false;

        /*
         * Reset the kernel vLAPIC state to clear stale IRR/ISR bits.
         * do_cpu_init() only resets QEMU's APIC state — the kernel's
         * vLAPIC retains pending interrupts from before INIT.  If we
         * don't clear them, VMX will see pending IRR bits, try to
         * inject with IF=0 (AP in real mode), set interrupt-window
         * exiting, and loop on BOGUS exits forever.
         *
         * IMPORTANT: We build the LAPIC state from scratch instead of
         * read-modify-write.  vm_lapic_get_state() uses _IOR ioctl,
         * and FreeBSD's _IOR bzeros the kernel buffer — the vcpuid
         * written by vcpu_ioctl() is lost, so GET_STATE always reads
         * vcpu 0 (BSP).  This corrupted the AP's LAPIC by writing
         * BSP data to it.  Using write-only avoids this bug entirely.
         */
        {
            struct vm_lapic_state lapic_state;
            int lapic_err;

            memset(&lapic_state, 0, sizeof(lapic_state));

            /* Set APIC ID to match this CPU's index (xAPIC: bits 31:24) */
            lapic_state.fields[0x2].data = (uint32_t)(cpu->cpu_index << 24);
            /* VERSION register — must match what the kernel vLAPIC reports */
            lapic_state.fields[0x3].data = 0x00050014;  /* version 0x14, max LVT 5 */
            /* DFR: flat model (all 1s) per Intel INIT spec */
            lapic_state.fields[0xe].data = 0xffffffff;
            /* SVR: spurious vector 0xff, APIC software-enabled */
            lapic_state.fields[0xf].data = 0xff;
            /* Mask all LVT entries (bit 16 = masked) */
            lapic_state.fields[0x32].data = 0x00010000; /* LVT_TIMER */
            lapic_state.fields[0x33].data = 0x00010000; /* LVT_THERMAL */
            lapic_state.fields[0x34].data = 0x00010000; /* LVT_PCINT */
            lapic_state.fields[0x35].data = 0x00010000; /* LVT_LINT0 */
            lapic_state.fields[0x36].data = 0x00010000; /* LVT_LINT1 */
            lapic_state.fields[0x37].data = 0x00010000; /* LVT_ERROR */
            lapic_state.fields[0x2f].data = 0x00010000; /* LVT_CMCI */
            /* IRR, ISR, TMR are all zero from memset — clean slate */
            /* TPR, APR, PPR, LDR are all zero from memset */

            lapic_err = vm_lapic_set_state(qcpu->vcpu, &lapic_state);
        }
    }
    if (cpu->interrupt_request & CPU_INTERRUPT_POLL) {
        cpu->interrupt_request &= ~CPU_INTERRUPT_POLL;
        apic_poll_irq(x86_cpu->apic_state);
    }
    if (((cpu->interrupt_request & CPU_INTERRUPT_HARD) &&
         (env->eflags & IF_MASK)) ||
        (cpu->interrupt_request & CPU_INTERRUPT_NMI)) {
        cpu->halted = false;
    }
    /*
     * bhyve wakeup: env->eflags may be stale (not synced from guest VMCS).
     * If the poll timer fired CPU_INTERRUPT_HARD but env->eflags lacks IF,
     * the AP stays halted forever.  Read actual guest RFLAGS from the VMCS
     * and retry the check.
     */
    if (cpu->halted && (cpu->interrupt_request & CPU_INTERRUPT_HARD)) {
        AccelCPUState *qcpu_wake = cpu->accel;
        uint64_t real_rflags = 0;
        vm_get_register(qcpu_wake->vcpu, VM_REG_GUEST_RFLAGS, &real_rflags);
        if (real_rflags & IF_MASK) {
            cpu->halted = false;
        }
    }
    if (cpu->interrupt_request & CPU_INTERRUPT_SIPI) {
        cpu->interrupt_request &= ~CPU_INTERRUPT_SIPI;
        /*
         * SIPI: set CS:RIP directly. The bhyve kernel already handled
         * the APIC-level INIT/SIPI protocol. QEMU's apic_sipi() relies
         * on wait_for_sipi being set, but cpu_reset doesn't always
         * propagate to the APIC device properly with bhyve accel.
         * Handle it directly: load CS to SIPI vector, RIP=0.
         *
         * Per Intel SDM: SIPI is only accepted in "wait-for-SIPI" state.
         * A second SIPI (standard INIT-SIPI-SIPI sequence) arriving after
         * the AP has already started running must be ignored.  Without
         * this guard, the duplicate SIPI resets CS:RIP back to the
         * trampoline while the AP is in 64-bit mode, causing corruption.
         */
        if (!qcpu->wait_for_sipi) {
            goto sipi_done;
        }
        qcpu->wait_for_sipi = false;  /* First SIPI accepted; reject further */
        {
            uint8_t sipi_vec = x86_cpu->apic_state ?
                               x86_cpu->apic_state->sipi_vector : 0;
            cpu_x86_load_seg_cache_sipi(x86_cpu, sipi_vec);
            /*
             * Mark dirty so vmm_set_registers pushes the new CS:RIP
             * to the kernel VMCS. Without this, the INIT handler's
             * vmm_set_registers + dirty=false leaves stale reset-state
             * CS:RIP in the kernel, and the AP enters vm_run at the
             * BIOS reset vector instead of the SIPI trampoline.
             */
            qcpu->dirty = true;
            /*
             * CRITICAL: clear halted so the AP actually enters vm_run.
             * do_cpu_init() sets halted=true for non-BSP CPUs (wait-for-
             * SIPI state).  Now that SIPI has arrived, the AP must run.
             * Without this, bhyve_vcpu_run returns EXCP_HLT immediately
             * and the AP never executes guest code.
             */
            cpu->halted = false;

            /* Start LAPIC poll timer for AP — same as BSP's HLT timer.
             * The AP needs periodic vm_run exits during init so the
             * kernel can inject pending LAPIC interrupts. */
            if (!qcpu->lapic_poll_timer) {
                qcpu->lapic_poll_timer = timer_new_ns(QEMU_CLOCK_REALTIME,
                                                      lapic_poll_timer_cb, cpu);
            }
            timer_mod_ns(qcpu->lapic_poll_timer,
                         qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 10000000);
        }
    sipi_done: ;
    }

    if (cpu->interrupt_request & CPU_INTERRUPT_TPR) {
        cpu->interrupt_request &= ~CPU_INTERRUPT_TPR;
        bhyve_cpu_synchronize_state(cpu);
        apic_handle_tpr_access_report(x86_cpu->apic_state, env->eip,
                                      env->tpr_access_type);
    }

    /*
     * After INIT processing, non-BSP CPUs are halted (wait-for-SIPI).
     * Return to the thread loop where qemu_process_cpu_events blocks
     * on halt_cond until SIPI arrives via cpu_interrupt.
     */
    if (cpu->halted) {
        /*
         * Return with BQL held — the thread loop's qemu_process_cpu_events
         * expects it (calls qemu_cond_wait on halt_cond with &bql).
         * Do NOT unlock BQL here.
         */
        cpu->exception_index = EXCP_HLT;
        return EXCP_HLT;
    }

    bql_unlock();
    cpu_exec_start(cpu);

	while (rc == 0) {
        if (qcpu->dirty) {
            vmm_set_registers(cpu);
            qcpu->dirty = false;
        }

        bhyve_vcpu_pre_run(cpu);

        smp_rmb();

        /*
         * Second dirty check: bhyve_vcpu_pre_run may have processed
         * INIT+SIPI which modifies env (CS:RIP, CR0, etc.) and sets
         * dirty=true.  Without this, vm_run enters with stale VMCS
         * state (e.g. reset-vector RIP instead of SIPI trampoline).
         */
        if (qcpu->dirty) {
            vmm_set_registers(cpu);
            qcpu->dirty = false;
        }

        /*
         * Scrub bad vectors from in-kernel LAPIC IRR, but ONLY when
         * the guest is in kernel space. During UEFI, vectors 32 and 64
         * are legitimate timer interrupts that UEFI needs to make progress.
         * In the FreeBSD kernel, those same vectors have no IDT handler
         * (Xrsvd) and cause trap 30.
         */
        {
            uint64_t scrub_rip = 0;
            vm_get_register(qcpu->vcpu, VM_REG_GUEST_RIP, &scrub_rip);
            if (scrub_rip >= 0xffffffff80000000ULL) {
                scrub_lapic_bad_vectors(qcpu->vcpu, cpu->cpu_index,
                                        qcpu->vcpu_vm_run_total);
            }
        }

        /*
         * MASK_HWINTR safety net: prevent the bhyve kernel from injecting
         * hardware interrupts during early FreeBSD kernel boot.
         *
         * During mi_startup, IF=0 (interrupts disabled). The vLAPIC IRR
         * accumulates pending vectors (e.g., PIT timer via IOAPIC).
         * When intr_init_final executes STI (IF→1), the kernel's
         * vmx_inject_interrupts would deliver those IRR vectors immediately.
         * If the guest IDT still has Xrsvd handlers for those vectors,
         * the guest panics with trap 30.
         *
         * Strategy:
         * - When guest is in kernel long mode with IF=0: set MASK_HWINTR
         * - When guest transitions IF 0→1 (after STI): keep MASK_HWINTR
         *   for a grace period to let more IDT handlers be installed
         * - After grace period: clear MASK_HWINTR, allow interrupts
         */
        {
            uint64_t pre_rip = 0, pre_rflags = 0;
            vm_get_register(qcpu->vcpu, VM_REG_GUEST_RIP, &pre_rip);
            vm_get_register(qcpu->vcpu, VM_REG_GUEST_RFLAGS, &pre_rflags);
            int guest_if = (pre_rflags >> 9) & 1;

            int in_kernel = (pre_rip >= 0xffffffff80000000ULL);

            /*
             * SMP re-arm: when an IPI was sent (INIT/SIPI), keep
             * MASK_HWINTR active on BSP to prevent stale vector
             * injection during SMP init.  Scrub IRR while masked.
             */
            if (qcpu->smp_rearm_mask > 0 && in_kernel) {
                if (qcpu->smp_rearm_mask == 200) {
                    /* First entry: mask and selective scrub */
                    vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 1);
                    struct vm_lapic_state smp_lap;
                    memset(&smp_lap, 0, sizeof(smp_lap));
                    if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE,
                                   &smp_lap) == 0) {
                        int smp_mod = 0;
                        /* Scrub firmware stale vectors 0-63 + vec 64 */
                        if (smp_lap.fields[0x20].data != 0) {
                            smp_lap.fields[0x20].data = 0; /* vec 0-31 */
                            smp_mod = 1;
                        }
                        if (smp_lap.fields[0x21].data != 0) {
                            smp_lap.fields[0x21].data = 0; /* vec 32-63 */
                            smp_mod = 1;
                        }
                        if (smp_lap.fields[0x22].data & (1u << 0)) {
                            smp_lap.fields[0x22].data &= ~(1u << 0); /* vec 64 */
                            smp_mod = 1;
                        }
                        if (smp_mod) {
                            vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE,
                                       &smp_lap);
                        }
                    }
                }
                qcpu->smp_rearm_mask--;
                if (qcpu->smp_rearm_mask == 0) {
                    /* SMP rearm over — selective scrub and unmask */
                    struct vm_lapic_state final_lap;
                    memset(&final_lap, 0, sizeof(final_lap));
                    if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE,
                                   &final_lap) == 0) {
                        int fmod = 0;
                        if (final_lap.fields[0x20].data != 0) {
                            final_lap.fields[0x20].data = 0;
                            fmod = 1;
                        }
                        if (final_lap.fields[0x21].data != 0) {
                            final_lap.fields[0x21].data = 0;
                            fmod = 1;
                        }
                        if (final_lap.fields[0x22].data & (1u << 0)) {
                            final_lap.fields[0x22].data &= ~(1u << 0);
                            fmod = 1;
                        }
                        if (fmod)
                            vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE,
                                       &final_lap);
                    }
                    /*
                     * SMP re-arm expired: unconditionally unmask HWINTR
                     * and set state to 3 (done). The re-arm protected
                     * the INIT-SIPI sequence; now the BSP must be able
                     * to receive timer interrupts to make progress.
                     * Without this, BSP stays masked (hwintr_state=1)
                     * if it's in a spin-wait loop with IF=0 → deadlock.
                     */
                    vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 0);
                    qcpu->hwintr_state = 3;
                    BHYVE_DPRINTF("[SMP] BSP MASK_HWINTR SMP re-arm "
                            "expired at run=%ld hwintr_state=%d\n",
                            qcpu->vcpu_vm_run_total,
                            qcpu->hwintr_state);
                }
            }

            if (qcpu->hwintr_state == 0 && in_kernel && !guest_if) {
                /* Guest entered kernel with IF=0 — mask interrupts */
                vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 1);
                qcpu->hwintr_state = 1;
                BHYVE_DPRINTF("[HWINTR] vcpu%d state 0→1 (IF=0 in kernel) "
                        "run=%ld rip=0x%lx\n",
                        cpu->cpu_index, qcpu->vcpu_vm_run_total,
                        (unsigned long)pre_rip);
            } else if (qcpu->hwintr_state == 1 && guest_if && in_kernel) {
                /*
                 * Guest did STI (IF 0→1).
                 *
                 * By the time the kernel executes STI, all IDT handlers
                 * are installed (lapic_init, intr_init_final, etc. run
                 * before STI in mi_startup).  SMP1 boots fine without
                 * any grace period, proving the BSP's IDT is ready.
                 *
                 * Old approach: 50000-run grace period with full IRR
                 * scrub caused BSP to starve — LAPIC timer (vec 243)
                 * was scrubbed, so boot froze at "Event timer RTC".
                 *
                 * New approach: scrub vectors 0-63 (CPU exceptions +
                 * firmware IOAPIC/PIC stale vectors) and vector 64,
                 * then immediately unmask.
                 *
                 * IRR[1] (vectors 32-63) includes firmware-era
                 * vectors: the BHYVE UEFI firmware programs IOAPIC
                 * with vectors in this range (e.g., pin 9/SCI at
                 * vector 48).  When the guest OS takes over, these
                 * vectors are stale — the guest reprograms IOAPIC
                 * with its own vectors.  Leaving them causes a
                 * spurious interrupt (e.g., SCI handler loop on
                 * SMP4).  One-time scrub is safe; devices re-assert.
                 *
                 * NOTE: The PERIODIC scrub (every 50 runs) must NOT
                 * clear all of IRR[1] — vectors 48/49 are live RTC
                 * interrupts once the guest is running.
                 */
                {
                    struct vm_lapic_state sti_lap;
                    memset(&sti_lap, 0, sizeof(sti_lap));
                    if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE,
                                   &sti_lap) == 0) {
                        int smod = 0;
                        /* Scrub IRR[0] (vectors 0-31: CPU exceptions) */
                        if (sti_lap.fields[0x20].data != 0) {
                            sti_lap.fields[0x20].data = 0;
                            smod = 1;
                        }
                        /* Scrub ALL of IRR[1] (vectors 32-63:
                         * firmware IOAPIC/PIC stale vectors including
                         * SCI vec 48, PIT vec 50, etc.) */
                        if (sti_lap.fields[0x21].data != 0) {
                            sti_lap.fields[0x21].data = 0;
                            smod = 1;
                        }
                        /* Scrub vector 64 (bit 0 in IRR[2]) */
                        if (sti_lap.fields[0x22].data & (1u << 0)) {
                            sti_lap.fields[0x22].data &= ~(1u << 0);
                            smod = 1;
                        }
                        if (smod)
                            vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE,
                                       &sti_lap);
                    }
                }
                /*
                 * Clear stale vatpic (8259) IRQs from firmware.
                 * vmx_inject_interrupts() checks vm_extint_pending()
                 * and injects vatpic vectors >= 32 even in QEMU mode.
                 * Firmware leaves stale IRQs that cause trap 30 when
                 * injected into the guest OS (no matching IDT handler).
                 * Deassert all 16 ISA IRQs in both vatpic and vioapic.
                 */
                {
                    int irq;
                    for (irq = 0; irq < 16; irq++) {
                        int ioapic_pin = (irq == 0) ? 2 : irq;
                        vm_isa_deassert_irq(bhyve_mach.vm, irq, ioapic_pin);
                    }
                    BHYVE_DPRINTF("[HWINTR] vcpu%d: cleared all 16 vatpic IRQs "
                            "at state 1→3\n", cpu->cpu_index);
                }
                vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 0);
                qcpu->hwintr_state = 3;
                BHYVE_DPRINTF("[HWINTR] vcpu%d state 1→3 (STI, scrub+unmask) "
                        "run=%ld rip=0x%lx\n",
                        cpu->cpu_index, qcpu->vcpu_vm_run_total,
                        (unsigned long)pre_rip);
            }
        }


        /*
         * Periodic scrub of known-bad vectors before vm_run.
         * Only scrub specific vectors that lack IDT handlers in
         * FreeBSD APIC mode → hit Xrsvd → trap 30.
         *
         * IMPORTANT: Do NOT scrub wide ranges! Vectors 48/49 are
         * RTC interrupts (IOAPIC IRQ8 → lapic), vector 243 is
         * LAPIC timer. Scrubbing them starves the event timer.
         *
         * Known-bad: vec 50 (PIT via IOAPIC pin 2, no handler),
         *            vec 64 (UEFI PIC stale).
         * Vec 0-31 are CPU exceptions — external delivery should
         * not happen, but clear them as safety net.
         *
         * Every 50 runs to avoid ioctl overhead.
         */
        if (qcpu->hwintr_state >= 3 &&
            (qcpu->vcpu_vm_run_total % 50) == 0) {
            struct vm_lapic_state scrub_lap;
            memset(&scrub_lap, 0, sizeof(scrub_lap));
            if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE,
                           &scrub_lap) == 0) {
                int smod = 0;
                /* Scrub IRR[0] (vectors 0-31: CPU exceptions) */
                if (scrub_lap.fields[0x20].data != 0) {
                    scrub_lap.fields[0x20].data = 0;
                    smod = 1;
                }
                /* Scrub ONLY vector 50 (bit 18 in IRR[1]) — PIT */
                if (scrub_lap.fields[0x21].data & (1u << 18)) {
                    scrub_lap.fields[0x21].data &= ~(1u << 18);
                    smod = 1;
                }
                /* Scrub vector 64 (bit 0 in IRR[2]) */
                if (scrub_lap.fields[0x22].data & (1u << 0)) {
                    scrub_lap.fields[0x22].data &= ~(1u << 0);
                    smod = 1;
                }
                if (smod)
                    vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE,
                               &scrub_lap);
            }
        }

        /*
         * Arm safety timer BEFORE vm_run: if the guest executes HLT,
         * vm_run blocks in the kernel.  The timer fires from another
         * thread's timer dispatch, calls cpu_interrupt → qemu_cpu_kick
         * → pthread_kill(SIG_IPI) → vm_run returns with EINTR/BOGUS.
         * Without this, the BSP blocks forever in vm_run when all
         * other threads are also halted or in their own vm_run.
         */
        if (!qcpu->lapic_poll_timer) {
            qcpu->lapic_poll_timer = timer_new_ns(QEMU_CLOCK_REALTIME,
                                                  lapic_poll_timer_cb, cpu);
        }
        timer_mod_ns(qcpu->lapic_poll_timer,
                     qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 5000000);

		error = vm_run(qcpu->vcpu, &vmrun);
		vm_run_total++;
        qcpu->vcpu_vm_run_total++;

        /* Ensure CR4.FSGSBASE (bit 16) is set once the guest kernel is running.
         *
         * The guest kernel's identify_cpu reads CPUID leaf 7 and sees FSGSBASE,
         * but for unknown reasons does not set CR4.FSGSBASE during initcpu.
         * Without it, wrfsbase causes #UD → SIGILL in every forked child
         * process (sshd, pkg-static, etc.).
         *
         * Force-set the bit once the guest enters kernel long mode.
         * CR4.FSGSBASE is not in the VMX CR4 mask, so it's freely writable.
         */
        {
            uint64_t cr4_now = 0;
            vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR4, &cr4_now);

            if (!qcpu->fsgsbase_forced && !(cr4_now & (1ULL << 16)) &&
                vme.rip >= 0xffffffff80000000ULL) {
                cr4_now |= (1ULL << 16);  /* CR4.FSGSBASE */
                vm_set_register(qcpu->vcpu, VM_REG_GUEST_CR4, cr4_now);
                qcpu->fsgsbase_forced = true;
            }

            /* Patch MADT for SMP: add missing CPU entries.
             * The BHYVE_UEFI firmware generates a MADT with only 1 CPU.
             * We MUST wait until the kernel enters long mode to patch,
             * because UEFI may regenerate/relocate ACPI tables until
             * ExitBootServices(). The kernel reads MADT early in boot
             * but after UEFI has finalized the tables. */
            if (!madt_patched && cpu->cpu_index == 0) {
                bool should_try = (vme.rip >= 0xffffffff80000000ULL);
                if (should_try) {
                    int total_cpus = current_machine->smp.cpus;
                    if (total_cpus > 1) {
                        patch_madt_for_smp(bhyve_mach.vm, total_cpus);
                    }
                }
            }
        }
        if (error != 0) {
            static int vm_run_err_log = 0;
            if (vm_run_err_log < 5) {
                fprintf(stderr, "Error running vm: %s (errno=%d, error=%d)\n",
                        strerror(errno), errno, error);
                vm_run_err_log++;
            }
            rc = 1;
            break;
        }

        bhyve_vcpu_post_run(cpu);

        /*
         * AP curthread fix: FreeBSD sets pc_curthread = 0 during AP
         * init_secondary(), only initializing it later in init_secondary_tail
         * (PCPU_SET(curthread, PCPU_GET(idlethread))). If ANY page fault
         * occurs before that point, trap() dereferences curthread->td_proc
         * (offset 0x8 from NULL) → infinite recursive fault → AP freeze.
         *
         * Fix: while the AP is in the PAUSE loop waiting for aps_ready,
         * pre-initialize pc_curthread = pc_idlethread in guest memory.
         * The idle thread is valid (set by idle_setup at SI_SUB_SCHED_IDLE
         * before release_aps at SI_SUB_SMP). init_secondary_tail will
         * overwrite it with the same value later — this is idempotent.
         */
        if (cpu->cpu_index > 0) {
            static __thread int ap_curthread_fixed = 0;

            if (!ap_curthread_fixed &&
                vme.rip >= 0xffffffff80000000ULL) {
                uint64_t gs_base = 0, cr3_val = 0;
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_GS_BASE, &gs_base);
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR3, &cr3_val);

                if (gs_base != 0 && cr3_val != 0) {
                    uint64_t pcpu_curthread = read_guest_virt64(cr3_val, gs_base + 0);
                    uint64_t pcpu_idlethread = read_guest_virt64(cr3_val, gs_base + 8);

                    if (pcpu_curthread == 0 && pcpu_idlethread != 0) {
                        /* pc_curthread is NULL but pc_idlethread is valid.
                         * Write idlethread → curthread to prevent trap() crash. */
                        write_guest_virt64(cr3_val, gs_base + 0, pcpu_idlethread);

                        fprintf(stderr,
                            "\n*** [AP-FIX] vcpu%d: pre-initialized pc_curthread ***\n"
                            "  GS_BASE=0x%lx pc_idlethread=0x%lx → pc_curthread\n"
                            "  RIP=0x%lx (init_secondary PAUSE loop)\n\n",
                            cpu->cpu_index,
                            (unsigned long)gs_base,
                            (unsigned long)pcpu_idlethread,
                            (unsigned long)vme.rip);

                        ap_curthread_fixed = 1;
                    } else if (pcpu_curthread != 0) {
                        /* curthread already valid — no fix needed */
                        ap_curthread_fixed = 1;
                    }
                }
            }
        }

		exitcode = vme.exitcode;

        /*
         * UNIVERSAL TIMER DISPATCH — runs for EVERY exit type, every 10 exits.
         *
         * Critical for SMP: when both vCPUs are in HLT (idle), the exit-type-
         * specific timer dispatch (INOUT/MMIO/BOGUS handlers) never fires.
         * Without this, lapic_poll_timer (QEMU_CLOCK_REALTIME) never gets
         * dispatched, so halted vCPUs are never woken up → deadlock.
         *
         * This replaces the need for per-handler timer dispatch for basic
         * timer liveness.  Per-handler dispatch is kept for higher frequency
         * during storms.
         */
        {
            static __thread long universal_exit_count = 0;
            universal_exit_count++;

            /*
             * Shared-timestamp timer dispatch: only ONE vCPU acquires BQL
             * for timer dispatch at a time.  All 8 vCPUs check whether
             * timers need dispatching (every 50 exits), but only the
             * winner of the CAS on last_timer_dispatch_ns actually does
             * the work.  This reduces BQL contention from 8x to 1x for
             * timer dispatch while keeping the same liveness guarantee.
             *
             * Interval: 1ms (1,000,000 ns) between dispatches.
             */
            if ((universal_exit_count % 50) == 0) {
                static volatile int64_t last_timer_dispatch_ns = 0;
                int64_t now = qemu_clock_get_ns(QEMU_CLOCK_REALTIME);
                int64_t last = qatomic_read(&last_timer_dispatch_ns);

                if (now - last > 1000000 /* 1ms */) {
                    /* Try to claim the dispatch slot */
                    if (qatomic_cmpxchg(&last_timer_dispatch_ns,
                                        last, now) == last) {
                        bhyve_bql_lock_in_loop(cpu);
                        qemu_clock_run_timers(QEMU_CLOCK_VIRTUAL);
                        qemu_clock_run_timers(QEMU_CLOCK_REALTIME);
                        {
                            AioContext *ctx = qemu_get_aio_context();
                            timerlistgroup_run_timers(&ctx->tlg);
                            aio_poll(ctx, false);
                        }
                        bhyve_bql_unlock_in_loop(cpu);
                        usleep(50);
                    }
                }
            }
            /* Heartbeat BEFORE BQL — fires even if BQL blocks */
            if ((universal_exit_count % 200000) == 0) {
                BHYVE_DPRINTF("[BEAT] vcpu%d exits=%ld runs=%ld "
                        "ec=%d hlt=%ld bogus=%ld\n",
                        cpu->cpu_index, universal_exit_count,
                        qcpu->vcpu_vm_run_total, exitcode,
                        qcpu->vcpu_exit_hlt, qcpu->vcpu_exit_bogus);
            }
        }

        switch (exitcode) {
        case VM_EXITCODE_HLT:
            exit_hlt++;
            qcpu->vcpu_exit_hlt++;
            {
                /*
                 * MASK_HWINTR fix for AP vCPUs:
                 *
                 * The pre-run MASK_HWINTR state machine masks interrupts when
                 * a vCPU enters kernel with IF=0 (state=1), and unmasks when
                 * IF transitions to 1 (state=3). But if the AP does STI+HLT,
                 * the HLT exit handler sets cpu->halted and exits the loop
                 * BEFORE the pre-run code gets a chance to detect IF=1.
                 * With MASK_HWINTR still enabled, vmm.ko won't deliver any
                 * interrupt to wake the AP → permanent deadlock.
                 *
                 * Fix: check and clear MASK_HWINTR here, before halting.
                 */
                if (qcpu->hwintr_state == 1 || qcpu->hwintr_state == 2) {
                    /*
                     * AP is halting with MASK_HWINTR still active.
                     * An AP doing HLT MUST be able to receive interrupts
                     * (timer, IPI) to wake up — unconditionally unmask.
                     * Scrub stale IRR first to prevent trap 30 on wakeup.
                     */
                    struct vm_lapic_state unmask_lapic;
                    memset(&unmask_lapic, 0, sizeof(unmask_lapic));
                    if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE,
                                   &unmask_lapic) == 0) {
                        uint32_t saved_apic_id = unmask_lapic.fields[2].data;
                        for (int i = 0; i < 8; i++) {
                            if (unmask_lapic.fields[0x20 + i].data != 0) {
                                unmask_lapic.fields[0x20 + i].data = 0;
                            }
                        }
                        unmask_lapic.fields[2].data = saved_apic_id;
                        vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE,
                                   &unmask_lapic);
                    }
                    vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 0);
                    qcpu->hwintr_state = 3;
                    BHYVE_DPRINTF("[HWINTR] vcpu%d state 1→3 (HLT unmask) "
                            "run=%ld\n", cpu->cpu_index,
                            qcpu->vcpu_vm_run_total);
                }

                /*
                 * Precise LAPIC timer wakeup for HLT exits.
                 *
                 * 1. Read kernel vLAPIC state
                 * 2. If IRR has pending bits -> skip halt, re-enter immediately
                 * 3. Otherwise compute exact LAPIC timer deadline from CCR/DCR
                 * 4. Arm host timer for that precise moment
                 */
                /* _IOR bug fixed (_IOWR now) — read actual vLAPIC state */
                struct vm_lapic_state hlt_lapic;
                memset(&hlt_lapic, 0, sizeof(hlt_lapic));
                int hlt_lapic_err = vcpu_ioctl(qcpu->vcpu,
                                               VM_LAPIC_GET_STATE,
                                               &hlt_lapic);
                bool irr_pending = false;
                if (hlt_lapic_err == 0) {
                    for (int i = 0; i < 8; i++) {
                        if (hlt_lapic.fields[0x20 + i].data != 0) {
                            irr_pending = true;
                            break;
                        }
                    }
                }

                if (irr_pending) {
                    /* Interrupt already pending -- re-enter VM immediately.
                     * The kernel will inject it on the next VMX entry. */
                    break;
                }

                cpu->halted = true;
                cpu->exception_index = EXCP_HLT;
                rc = EXCP_HLT;

                {
                    static __thread long hlt_count = 0;
                    hlt_count++;
                    if (hlt_count <= 5 || (hlt_count % 200) == 0) {
                        BHYVE_DPRINTF("[HLT-WAIT] vcpu%d hlt#%ld "
                                "run=%ld → halt_cond\n",
                                cpu->cpu_index, hlt_count,
                                qcpu->vcpu_vm_run_total);
                    }
                }

                int64_t deadline_ns = -1;
                if (hlt_lapic_err == 0) {
                    uint32_t lvt_timer = hlt_lapic.fields[0x32].data;
                    uint32_t icr = hlt_lapic.fields[0x38].data;
                    uint32_t ccr = hlt_lapic.fields[0x39].data;
                    uint32_t dcr = hlt_lapic.fields[0x3E].data;
                    int masked = (lvt_timer >> 16) & 1;

                    if (!masked && icr > 0 && ccr > 0) {
                        /* Compute divisor from DCR register (Intel SDM Table 11-10) */
                        uint32_t divisor;
                        switch (dcr & 0xB) {
                        case 0x0B: divisor = 1; break;
                        case 0x00: divisor = 2; break;
                        case 0x01: divisor = 4; break;
                        case 0x02: divisor = 8; break;
                        case 0x03: divisor = 16; break;
                        case 0x08: divisor = 32; break;
                        case 0x09: divisor = 64; break;
                        case 0x0A: divisor = 128; break;
                        default:   divisor = 1; break;
                        }

                        uint64_t ccr64 = ccr;
                        uint64_t div64 = divisor;
                        deadline_ns = (int64_t)((ccr64 * div64 * 1000000000ULL)
                                                / VLAPIC_BUS_FREQ);

                        /* Clamp: minimum 100us to avoid spinning,
                         * maximum 50ms as sanity cap */
                        if (deadline_ns < 100000)
                            deadline_ns = 100000;
                        if (deadline_ns > 50000000)
                            deadline_ns = 50000000;
                    }
                }

                if (!qcpu->lapic_poll_timer) {
                    qcpu->lapic_poll_timer = timer_new_ns(QEMU_CLOCK_REALTIME,
                                                          lapic_poll_timer_cb, cpu);
                }

                if (deadline_ns > 0) {
                    /* Arm for exact LAPIC timer deadline */
                    timer_mod_ns(qcpu->lapic_poll_timer,
                                 qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + deadline_ns);
                } else {
                    /* No active LAPIC timer — 5ms fallback for device interrupts */
                    timer_mod_ns(qcpu->lapic_poll_timer,
                                 qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 5000000);
                }
            }
            break;
        case VM_EXITCODE_DEBUG:
            exit_debug++;
            {
                uint64_t dbg_rip = vme.rip;

                /* If this is our intr_init_final breakpoint, scrub IRR */
                if (dbg_rip >= 0xffffffff810411f0 &&
                    dbg_rip <= 0xffffffff810411f6) {
                    struct vm_lapic_state dbg_lapic;
                    memset(&dbg_lapic, 0, sizeof(dbg_lapic));
                    if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE, &dbg_lapic) == 0) {
                        int scrubbed = 0;
                        for (int i = 0; i < 8; i++) {
                            if (dbg_lapic.fields[0x20 + i].data != 0) {
                                dbg_lapic.fields[0x20 + i].data = 0;
                                scrubbed = 1;
                            }
                        }
                        if (scrubbed) {
                            vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE, &dbg_lapic);
                        }
                    }
                    /* Clear DR0/DR7 — breakpoint no longer needed */
                    vm_set_register(qcpu->vcpu, VM_REG_GUEST_DR0, 0);
                    vm_set_register(qcpu->vcpu, VM_REG_GUEST_DR7, 0);
                }
            }
            /* Clear debug state so next vm_run doesn't exit immediately */
            vm_resume_cpu(qcpu->vcpu);
            break;
        case VM_EXITCODE_INOUT:
        case VM_EXITCODE_INOUT_STR:
            exit_inout++;
            qcpu->vcpu_exit_inout++;

            /* Safety valve: detect infinite INOUT loops.
             * ACPI PM1 ports legitimately loop — guest polls PM1_STS/
             * PM1_EN/PM1_CNT/PM_TMR in SCI handler and firmware.
             * PIIX4 PM base = 0x400, ICH9 PM base = 0x600.
             * For other ports, if same RIP >10000 times → stop vCPU.
             * Uses per-vCPU state (not static) to avoid SMP race. */
            {
                if (vme.rip == qcpu->last_inout_rip) {
                    qcpu->inout_repeat_count++;
                    uint16_t port = vme.u.inout.port;
                    bool is_acpi_pm = (port >= 0x400 && port <= 0x408) ||
                                      (port >= 0x600 && port <= 0x608);
                    if (is_acpi_pm) {
                        /* ACPI PM1 register polling is normal guest behavior */
                        if (!qcpu->pm_timer_warned && qcpu->inout_repeat_count > 1000) {
                            qcpu->pm_timer_warned = true;
                        }
                    } else if (qcpu->inout_repeat_count > 10000) {
                        fprintf(stderr,
                            "\n*** FATAL: vcpu%d INOUT loop at RIP=0x%lx "
                            "port=0x%x (%d times, run #%ld) — stopping vCPU\n",
                            cpu->cpu_index, (unsigned long)vme.rip,
                            vme.u.inout.port, qcpu->inout_repeat_count,
                            qcpu->vcpu_vm_run_total);
                        cpu->halted = true;
                        cpu->exception_index = EXCP_HLT;
                        rc = EXCP_HLT;
                        goto abort_vcpu_loop;
                    }
                } else {
                    qcpu->last_inout_rip = vme.rip;
                    qcpu->inout_repeat_count = 1;
                }
            }

            /*
             * Acquire BQL for I/O emulation — device models (serial, PIC,
             * etc.) expect it when modifying state and raising interrupts.
             * This mirrors KVM's pattern of locking BQL for exit handling.
             */
            bhyve_bql_lock_in_loop(cpu);
            rc = vm_assist_qio(qcpu->vcpu, vmm_io_callback, &vme);
            bhyve_bql_unlock_in_loop(cpu);
            break;
        case VM_EXITCODE_INST_EMUL:
            {
                static __thread long ie_count = 0;
                ie_count++;
                if ((ie_count % 1000) == 0 || ie_count < 5) {
                    BHYVE_DPRINTF("[MMIO-BQL] vcpu%d #%ld gpa=0x%lx "
                            "rip=0x%lx pre-lock\n",
                            cpu->cpu_index, ie_count,
                            (unsigned long)vme.u.inst_emul.gpa,
                            (unsigned long)vme.rip);
                }
            }
            bhyve_bql_lock_in_loop(cpu);
            rc = vm_assist_qmem(qcpu->vcpu, vmm_mem_callback, &vme);
            if (rc != 0) {
                /*
                 * MMIO instruction decode failed in kernel vie.
                 * Perform userspace MMIO emulation: decode the instruction,
                 * do the actual read/write through QEMU's address_space_rw,
                 * and update the guest register accordingly.
                 */
                struct vie *vie = &vme.u.inst_emul.vie;
                uint64_t gpa = vme.u.inst_emul.gpa;
                if (vie->num_valid == 0) {
                    static int nv0_count = 0;
                    if (nv0_count < 10) {
                        nv0_count++;
                        BHYVE_DPRINTF("[MMIO] #%d vie num_valid=0 gpa=0x%lx "
                                "rip=0x%lx — skipping 1 byte\n",
                                nv0_count, (unsigned long)gpa,
                                (unsigned long)vme.rip);
                    }
                    /* Advance RIP by 1 to avoid infinite loop */
                    vm_set_register(qcpu->vcpu, VM_REG_GUEST_RIP,
                                    vme.rip + 1);
                    bhyve_bql_unlock_in_loop(cpu);
                    rc = 0;
                    break;
                }

                uint8_t *p = vie->inst;
                int n = vie->num_valid;
                int idx = 0;
                int is_64bit = (vme.u.inst_emul.paging.cpu_mode == 4);
                int addr32 = is_64bit ? 0 : vme.u.inst_emul.cs_d;
                int op32 = is_64bit ? 1 : vme.u.inst_emul.cs_d;
                int rex = 0; /* REX byte if present */

                /* x86 reg encoding → VM_REG_GUEST_* */
                static const int reg_map[16] = {
                    VM_REG_GUEST_RAX, VM_REG_GUEST_RCX,
                    VM_REG_GUEST_RDX, VM_REG_GUEST_RBX,
                    VM_REG_GUEST_RSP, VM_REG_GUEST_RBP,
                    VM_REG_GUEST_RSI, VM_REG_GUEST_RDI,
                    VM_REG_GUEST_R8,  VM_REG_GUEST_R9,
                    VM_REG_GUEST_R10, VM_REG_GUEST_R11,
                    VM_REG_GUEST_R12, VM_REG_GUEST_R13,
                    VM_REG_GUEST_R14, VM_REG_GUEST_R15,
                };

                /* Parse prefixes */
                while (idx < n) {
                    uint8_t b = p[idx];
                    if (b == 0x66) { op32 = !op32; idx++; }
                    else if (b == 0x67) { addr32 = !addr32; idx++; }
                    else if (b == 0x26 || b == 0x2e || b == 0x36 ||
                             b == 0x3e || b == 0x64 || b == 0x65 ||
                             b == 0xf0 || b == 0xf2 || b == 0xf3) { idx++; }
                    else if ((b & 0xf0) == 0x40 && is_64bit) {
                        rex = b; idx++; /* REX prefix */
                        if (rex & 0x08) op32 = 2; /* REX.W → 64-bit */
                    }
                    else break;
                }

                if (idx >= n) {
                    /* Only prefixes, no opcode — skip all */
                    vm_set_register(qcpu->vcpu, VM_REG_GUEST_RIP,
                                    vme.rip + n);
                    bhyve_bql_unlock_in_loop(cpu);
                    rc = 0;
                    break;
                }

                uint8_t opcode = p[idx++];
                int is_write = -1; /* -1 = unknown */
                int op_size = 0;
                int reg_field = -1;
                int is_high_byte = 0;
                int has_modrm = 0;
                int imm_size = 0;
                /* op32: 0=16-bit, 1=32-bit, 2=64-bit (REX.W) */
                int opsz = (op32 == 2) ? 8 : (op32 ? 4 : 2);
                /* In 64-bit mode, address size is 64 by default */
                int addrsz = is_64bit ? 8 : (addr32 ? 4 : 2);
                /* REX.R extends ModRM reg field to R8-R15 */
                int rex_r = (rex & 0x04) ? 8 : 0;
                /* REX.B extends ModRM r/m or SIB base */
                int rex_b = (rex & 0x01) ? 8 : 0;

                switch (opcode) {
                case 0x8a: /* MOV r8, r/m8 — byte read */
                    if (idx >= n) break;
                    reg_field = ((p[idx] >> 3) & 7) | rex_r;
                    op_size = 1; is_write = 0; has_modrm = 1;
                    /* In 64-bit with REX, no high-byte regs */
                    if (!rex) {
                        is_high_byte = (reg_field >= 4 && reg_field < 8);
                        if (is_high_byte) reg_field -= 4;
                    }
                    break;
                case 0x8b: /* MOV r16/32/64, r/m — read */
                    if (idx >= n) break;
                    reg_field = ((p[idx] >> 3) & 7) | rex_r;
                    op_size = opsz; is_write = 0; has_modrm = 1;
                    break;
                case 0x88: /* MOV r/m8, r8 — byte write */
                    if (idx >= n) break;
                    reg_field = ((p[idx] >> 3) & 7) | rex_r;
                    op_size = 1; is_write = 1; has_modrm = 1;
                    if (!rex) {
                        is_high_byte = (reg_field >= 4 && reg_field < 8);
                        if (is_high_byte) reg_field -= 4;
                    }
                    break;
                case 0x89: /* MOV r/m, r16/32/64 — write */
                    if (idx >= n) break;
                    reg_field = ((p[idx] >> 3) & 7) | rex_r;
                    op_size = opsz; is_write = 1; has_modrm = 1;
                    break;
                case 0xa0: /* MOV AL, moffs8 */
                    reg_field = 0; op_size = 1; is_write = 0;
                    imm_size = addrsz;
                    break;
                case 0xa1: /* MOV AX/EAX/RAX, moffs */
                    reg_field = 0; op_size = opsz; is_write = 0;
                    imm_size = addrsz;
                    break;
                case 0xa2: /* MOV moffs8, AL */
                    reg_field = 0; op_size = 1; is_write = 1;
                    imm_size = addrsz;
                    break;
                case 0xa3: /* MOV moffs, AX/EAX/RAX */
                    reg_field = 0; op_size = opsz; is_write = 1;
                    imm_size = addrsz;
                    break;
                case 0x0f: /* 2-byte opcode */
                    if (idx < n) {
                        uint8_t op2 = p[idx++];
                        if (op2 == 0xb6) {
                            /* MOVZX r16/32/64, r/m8 */
                            if (idx < n) {
                                reg_field = ((p[idx] >> 3) & 7) | rex_r;
                                op_size = 1; is_write = 0; has_modrm = 1;
                            }
                        } else if (op2 == 0xb7) {
                            /* MOVZX r32/64, r/m16 */
                            if (idx < n) {
                                reg_field = ((p[idx] >> 3) & 7) | rex_r;
                                op_size = 2; is_write = 0; has_modrm = 1;
                            }
                        } else {
                            has_modrm = 1; /* most 0F opcodes have ModRM */
                        }
                    }
                    break;
                case 0xc6: /* MOV r/m8, imm8 — immediate byte write */
                    op_size = 1; is_write = 2; /* 2 = imm write */
                    has_modrm = 1; imm_size = 1;
                    break;
                case 0xc7: /* MOV r/m16/32, imm — immediate write */
                    /* Note: REX.W makes this 64-bit dest but imm is still 32 */
                    op_size = opsz; is_write = 2;
                    has_modrm = 1;
                    imm_size = (opsz >= 4) ? 4 : opsz;
                    break;
                default:
                    /* Unsupported opcode for MMIO emulation */
                    break;
                }

                /* Calculate instruction length (skip past ModRM/SIB/disp) */
                int inst_len = idx; /* past prefixes + opcode */
                if (has_modrm && idx < n) {
                    uint8_t modrm = p[idx++];
                    uint8_t mod = modrm >> 6;
                    uint8_t rm = modrm & 7;
                    inst_len = idx;
                    if (mod != 3) {
                        if (is_64bit || addr32) {
                            /* 64-bit and 32-bit use same ModRM encoding */
                            if (rm == 4 && idx < n) { idx++; inst_len = idx; } /* SIB */
                            if (mod == 0 && rm == 5) idx += 4; /* RIP-rel or disp32 */
                            else if (mod == 1) idx += 1;
                            else if (mod == 2) idx += 4;
                        } else {
                            /* 16-bit addressing */
                            if (mod == 0 && rm == 6) idx += 2;
                            else if (mod == 1) idx += 1;
                            else if (mod == 2) idx += 2;
                        }
                        inst_len = idx;
                    }
                }
                int imm_start = idx;
                inst_len = idx + imm_size;
                if (inst_len > n) inst_len = n;
                if (inst_len == 0) inst_len = 3; /* last resort */

                /* Perform the actual MMIO operation */
                if (is_write == 0 && reg_field >= 0 && op_size > 0) {
                    /* MMIO READ: read from device, put into guest register */
                    /* MMIO read */
                    uint8_t data[8] = {0};
                    address_space_rw(&address_space_memory, gpa,
                                     MEMTXATTRS_UNSPECIFIED,
                                     data, op_size, false);
                    uint64_t regval;
                    vm_get_register(qcpu->vcpu, reg_map[reg_field], &regval);
                    if (op_size == 1) {
                        if (is_high_byte)
                            regval = (regval & ~0xFF00ULL) |
                                     ((uint64_t)data[0] << 8);
                        else
                            regval = (regval & ~0xFFULL) | data[0];
                    } else if (op_size == 2) {
                        uint16_t v;
                        memcpy(&v, data, 2);
                        regval = (regval & ~0xFFFFULL) | v;
                    } else if (op_size == 4) {
                        uint32_t v;
                        memcpy(&v, data, 4);
                        regval = v; /* 32-bit zero-extends */
                    } else if (op_size == 8) {
                        uint64_t v;
                        memcpy(&v, data, 8);
                        regval = v;
                    }
                    vm_set_register(qcpu->vcpu, reg_map[reg_field], regval);
                } else if (is_write == 1 && reg_field >= 0 && op_size > 0) {
                    /* MMIO WRITE: read from guest register, write to device */
                    /* MMIO write */
                    uint64_t regval;
                    vm_get_register(qcpu->vcpu, reg_map[reg_field], &regval);
                    uint8_t data[8] = {0};
                    if (is_high_byte)
                        data[0] = (regval >> 8) & 0xFF;
                    else
                        memcpy(data, &regval, op_size);
                    address_space_rw(&address_space_memory, gpa,
                                     MEMTXATTRS_UNSPECIFIED,
                                     data, op_size, true);
                } else if (is_write == 2 && op_size > 0) {
                    /* MMIO WRITE from immediate value */
                    /* MMIO write */
                    uint8_t data[8] = {0};
                    if (imm_start + imm_size <= n)
                        memcpy(data, &p[imm_start], imm_size);
                    address_space_rw(&address_space_memory, gpa,
                                     MEMTXATTRS_UNSPECIFIED,
                                     data, op_size, true);
                } else {
                    /* Can't decode — log and skip */
                    static int undecoded = 0;
                    if (undecoded < 20) {
                        undecoded++;
                        BHYVE_DPRINTF("[MMIO] #%d undecoded gpa=0x%lx "
                                "rip=0x%lx opcode=0x%02x is_write=%d "
                                "reg=%d opsz=%d inst:",
                                undecoded, (unsigned long)gpa,
                                (unsigned long)vme.rip, opcode,
                                is_write, reg_field, op_size);
                        if (BHYVE_DEBUG) {
                            for (int j = 0; j < n && j < 15; j++)
                                fprintf(stderr, " %02x", p[j]);
                            fprintf(stderr, "\n");
                        }
                    }
                }

                vm_set_register(qcpu->vcpu, VM_REG_GUEST_RIP,
                                vme.rip + inst_len);
                rc = 0;
            }
            bhyve_bql_unlock_in_loop(cpu);
            break;
        case VM_EXITCODE_RDMSR:
            rc = bhyve_rdmsr(qcpu->vcpu, &vme);
            break;
        case VM_EXITCODE_WRMSR:
            rc = bhyve_wrmsr(&vme);
            break;
        case VM_EXITCODE_BOGUS:
        case 20: /* VM_EXITCODE_REQIDLE -- scheduler yield, just re-enter */
            exit_bogus++;
            qcpu->vcpu_exit_bogus++;
            /* Run timers periodically on BOGUS/REQIDLE exits too.
             * Use less frequent interval (500) to reduce BQL contention
             * with 4+ vCPUs. */
            if ((exit_bogus % 500) == 0) {
                bhyve_bql_lock_in_loop(cpu);
                qemu_clock_run_timers(QEMU_CLOCK_VIRTUAL);
                qemu_clock_run_timers(QEMU_CLOCK_REALTIME);
                {
                    AioContext *ctx = qemu_get_aio_context();
                    timerlistgroup_run_timers(&ctx->tlg);
                    aio_poll(ctx, false);
                }
                bhyve_bql_unlock_in_loop(cpu);
            }
            /* Re-arm timer on BOGUS exits for APs that may need wakeups */
            if (cpu->cpu_index > 0 && qcpu->lapic_poll_timer) {
                timer_mod_ns(qcpu->lapic_poll_timer,
                             qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 5000000);
            }
            break;
        case VM_EXITCODE_SUSPENDED:
            how = vme.u.suspended.how;
            fprintf(stderr, "VM_EXITCODE_SUSPENDED: how=%d (run #%ld, rip=0x%lx)\n",
                    how, vm_run_total, (unsigned long)vme.rip);

            switch (how) {
            case VM_SUSPEND_RESET:
                exit(0);
            case VM_SUSPEND_POWEROFF:
                qemu_system_reset_request(SHUTDOWN_CAUSE_GUEST_RESET);
                cpu->exception_index = EXCP_INTERRUPT;
                vm_destroy(mach->vm);
                rc = 1;
                break;
            case VM_SUSPEND_HALT:
                /*
                 * Halt-suspend: for APs this means the vCPU is in wait-
                 * for-SIPI state. Put it into halted and exit the run
                 * loop. For BSP, just re-enter.
                 */
                if (cpu->cpu_index > 0) {
                    cpu->halted = true;
                    cpu->exception_index = EXCP_HLT;
                    rc = EXCP_HLT;
                }
                break;
            case VM_SUSPEND_TRIPLEFAULT:
                fprintf(stderr, "VM triple fault at rip=0x%lx\n",
                        (unsigned long)vme.rip);
                rc = 1;
                break;
            default:
                rc = 1;
            }
            break;
        case VM_EXITCODE_VMX: {
            static int vmx_err_log = 0;
            if (vmx_err_log < 5) {
                fprintf(stderr, "VMX_ERROR[%d]: rip=0x%lx status=%d inst_type=%d inst_error=%d exit_reason=%d\n",
                        cpu->cpu_index, (unsigned long)vme.rip,
                        vme.u.vmx.status, vme.u.vmx.inst_type,
                        vme.u.vmx.inst_error, vme.u.vmx.exit_reason);
                vmx_err_log++;
            }
            dump_registers(qcpu->vcpu);
            rc = -1;
            break;
        }
        case VM_EXITCODE_SVM:
            rc = -1;
            break;
        case VM_EXITCODE_PAUSE:
            exit_pause++;
            qcpu->vcpu_exit_pause++;
            /*
             * Guest executed PAUSE — typically in a spin-wait loop.
             * We must periodically run QEMU timers so the PIT can fire
             * IRQ0 (timer interrupt) into the guest. Without this, the
             * guest never receives timer ticks and gets stuck forever
             * in busy-wait loops (e.g., i8042 probing, calibration).
             *
             * SMP fix: yield every 100 PAUSEs and usleep(1) every 1000
             * to prevent host starvation when multiple vCPUs spin-wait.
             */
            if ((qcpu->vcpu_exit_pause % 100) == 0) {
                sched_yield();
            }
            if ((qcpu->vcpu_exit_pause % 500) == 0) {
                bhyve_bql_lock_in_loop(cpu);
                qemu_clock_run_timers(QEMU_CLOCK_VIRTUAL);
                qemu_clock_run_timers(QEMU_CLOCK_REALTIME);
                {
                    AioContext *ctx = qemu_get_aio_context();
                    timerlistgroup_run_timers(&ctx->tlg);
                    aio_poll(ctx, false);
                }
                bhyve_bql_unlock_in_loop(cpu);
                usleep(100);  /* 100μs — let other threads acquire BQL */
            }
            continue;
        case VM_EXITCODE_IPI: {
            /*
             * IPI exit: the guest wrote to ICR to send an inter-processor
             * interrupt. The kernel decoded the destination into dmask
             * (cpuset_t). We translate INIT/SIPI/Fixed into QEMU
             * cpu_interrupt() calls on the target vCPUs.
             */
            uint32_t ipi_mode = vme.u.ipi.mode;
            uint8_t ipi_vector = vme.u.ipi.vector;
            int target_cpu;
            qcpu->vcpu_exit_ipi++;

            bhyve_bql_lock_in_loop(cpu);
            CPU_FOREACH_ISSET(target_cpu, &dmask) {
                CPUState *target_cs = qemu_get_cpu(target_cpu);
                if (!target_cs) {
                    continue;
                }

                switch (ipi_mode) {
                case APIC_DELMODE_INIT:
                    /*
                     * INIT: let QEMU handle via do_cpu_init which
                     * resets the APIC and sets wait_for_sipi=1.
                     * The kernel already called vm_await_start().
                     *
                     * FIX: clear stopped so the AP thread can enter
                     * bhyve_vcpu_exec to process CPU_INTERRUPT_INIT.
                     * Without this, the AP stays in qemu_cond_wait
                     * because cpu_thread_is_idle returns true for
                     * stopped CPUs, and INIT is never processed.
                     */
                    target_cs->stopped = false;
                    cpu_interrupt(target_cs, CPU_INTERRUPT_INIT);
                    qemu_cpu_kick(target_cs);
                    /*
                     * Re-arm MASK_HWINTR on the BSP (this vcpu) during
                     * SMP init window.  The AP launch creates new
                     * interrupt activity that can race with the BSP's
                     * VMX entry and inject a vector whose IDT handler
                     * isn't installed yet → trap 30.
                     */
                    qcpu->smp_rearm_mask = 200;
                    BHYVE_DPRINTF("[SMP] IPI INIT → vcpu%d "
                            "(BSP MASK_HWINTR re-armed for 200 runs)\n",
                            target_cpu);
                    break;
                case APIC_DELMODE_STARTUP: {
                    /*
                     * SIPI: activate AP in kernel, then use QEMU's
                     * standard SIPI path. QEMU handles everything:
                     * do_cpu_init (cpu_reset + apic_init_reset) +
                     * do_cpu_sipi (cpu_x86_load_seg_cache_sipi).
                     *
                     * DO NOT call vcpu_reset -- let QEMU's cpu_reset
                     * set the definitive state, then vmm_set_registers
                     * syncs it to the kernel VMCS.
                     */
                    AccelCPUState *tqcpu = target_cs->accel;
                    X86CPU *target_x86 = X86_CPU(target_cs);

                    /* Activate AP in kernel (idempotent) */
                    vm_activate_cpu(tqcpu->vcpu);
                    /* Suspend: bhyve_vcpu_exec will call vm_resume_cpu */
                    vm_suspend_cpu(tqcpu->vcpu);

                    /* Set SIPI vector in QEMU's APIC state and
                     * signal the AP thread (mirrors apic_startup).
                     *
                     * RACE FIX: clear halted BEFORE cpu_interrupt kicks
                     * the AP thread. Otherwise the AP wakes, sees
                     * halted=true, returns EXCP_HLT, and sleeps forever.
                     */
                    target_x86->apic_state->sipi_vector = ipi_vector;
                    target_cs->halted = false;
                    target_cs->stopped = false;
                    tqcpu->dirty = true;
                    cpu_interrupt(target_cs, CPU_INTERRUPT_SIPI);
                    qemu_cpu_kick(target_cs); /* ensure AP sees halted=false */
                    BHYVE_DPRINTF("[SMP] IPI SIPI → vcpu%d vec=0x%x\n",
                            target_cpu, ipi_vector);
                    break;
                }
                case APIC_DELMODE_FIXED:
                case APIC_DELMODE_LOWPRIO: {
                    /*
                     * Fixed/LowPri IPI: inject the vector into the target's
                     * kernel vLAPIC via MSI (no vCPU locking), then kick
                     * the target vCPU so it re-enters vm_run.
                     */
                    bhyve_inject_lapic_irq(target_cs, ipi_vector);
                    cpu_interrupt(target_cs, CPU_INTERRUPT_HARD);
                    break;
                }
                case APIC_DELMODE_NMI:
                    cpu_interrupt(target_cs, CPU_INTERRUPT_NMI);
                    break;
                default:
                    break;
                }
            }
            bhyve_bql_unlock_in_loop(cpu);
            /*
             * After INIT/SIPI, yield CPU so the AP thread can acquire
             * BQL and process the interrupt. Without this, the BSP's
             * tight MMIO polling loop (checking LAPIC for AP response)
             * keeps re-acquiring BQL before the AP thread gets a chance,
             * and the AP never starts before the BSP times out.
             */
            if (ipi_mode == APIC_DELMODE_INIT ||
                ipi_mode == APIC_DELMODE_STARTUP) {
                usleep(1000); /* 1ms — give AP thread time to wake */
            }
            break;
        }
        case VM_EXITCODE_SPINUP_AP: {
            /*
             * SPINUP_AP: the kernel wants to activate an AP.
             * This is the kernel-side counterpart of SIPI — the kernel
             * already handled INIT/SIPI at the APIC level and is telling
             * userspace to start the AP thread. We activate and resume
             * the target vCPU in the kernel.
             *
             * vme.u.spinup_ap.vcpu is the target AP index,
             * vme.u.spinup_ap.rip is the entry point (SIPI vector << 12).
             */
            int ap_idx = vme.u.spinup_ap.vcpu;
            uint64_t ap_rip = vme.u.spinup_ap.rip;

            bhyve_bql_lock_in_loop(cpu);
            CPUState *ap_cs = qemu_get_cpu(ap_idx);
            if (ap_cs && ap_cs->accel) {
                AccelCPUState *ap_qcpu = ap_cs->accel;
                X86CPU *ap_x86 = X86_CPU(ap_cs);

                vm_activate_cpu(ap_qcpu->vcpu);

                /* Set SIPI vector and signal the AP thread.
                 *
                 * RACE FIX: clear halted BEFORE cpu_interrupt kicks
                 * the AP thread. Otherwise the AP wakes, sees
                 * halted=true, returns EXCP_HLT, and sleeps forever.
                 */
                ap_x86->apic_state->sipi_vector = (uint8_t)(ap_rip >> 12);
                ap_cs->halted = false;
                ap_cs->stopped = false;
                ap_qcpu->dirty = true;
                cpu_interrupt(ap_cs, CPU_INTERRUPT_INIT);
                cpu_interrupt(ap_cs, CPU_INTERRUPT_SIPI);
                qemu_cpu_kick(ap_cs); /* ensure AP sees halted=false */
                BHYVE_DPRINTF("[SMP] SPINUP_AP → vcpu%d rip=0x%lx vec=0x%x\n",
                        ap_idx, (unsigned long)ap_rip,
                        (uint8_t)(ap_rip >> 12));

            } else {
                fprintf(stderr, "*** SPINUP_AP: no CPUState for AP%d!\n", ap_idx);
            }
            bhyve_bql_unlock_in_loop(cpu);
            break;
        }
        case VM_EXITCODE_IOAPIC_EOI: {
            /*
             * IOAPIC_EOI: the guest wrote to the LAPIC EOI register for
             * a level-triggered IOAPIC interrupt. The kernel tells us
             * the vector so we can notify QEMU's IOAPIC model to clear
             * REMOTE_IRR and re-check the pin level. Without this,
             * level-triggered interrupts (ACPI SCI, PCI INTx) either
             * never re-trigger or never deassert — causing infinite
             * handler loops (e.g., SCI stuck high → ACPI polling storm).
             */
            int eoi_vector = vme.u.ioapic_eoi.vector;
            {
                static int eoi_diag = 0;
                if (eoi_diag < 30) {
                    eoi_diag++;
                    BHYVE_DPRINTF("[IOAPIC-EOI] #%d vcpu%d vector=%d\n",
                            eoi_diag, cpu->cpu_index, eoi_vector);
                }
            }
            bhyve_bql_lock_in_loop(cpu);
            ioapic_eoi_broadcast(eoi_vector);
            bhyve_bql_unlock_in_loop(cpu);
            break;
        }
        default:
            exit_other++;
            qcpu->vcpu_exit_other++;
            printf("Unhandled exit (code=%d). Register Dump...\n", exitcode);
            dump_registers(qcpu->vcpu);
            bhyve_bql_lock_in_loop(cpu);
            qemu_system_guest_panicked(cpu_get_crash_info(cpu));
            bhyve_bql_unlock_in_loop(cpu);
            break;
        }

        /*
         * Check for exit_request (set by INIT/SIPI handlers, or by
         * qemu_cpu_kick when main loop wants to stop the vCPU, e.g.
         * for ACPI shutdown/reset).  Without this, the vCPU spins
         * forever after a shutdown request because nothing in the
         * switch above sets rc != 0 for normal INOUT exits.
         */
        if (qatomic_read(&cpu->exit_request)) {
            cpu->exception_index = EXCP_INTERRUPT;
            rc = EXCP_INTERRUPT;
            break;
        }

        /*
         * BQL fairness yield: periodically yield so halted vCPU threads
         * (woken by poll_timer or IOAPIC IRQ) can acquire BQL.
         * Every iteration was too expensive for SMP8 — reduced to
         * every 100 exits.  The universal timer dispatch (every 500
         * exits) already does usleep(100) which provides most of the
         * fairness; this is a lighter-weight supplement.
         */
        {
            static __thread long yield_count = 0;
            if ((++yield_count % 100) == 0) {
                sched_yield();
            }
        }
	}
abort_vcpu_loop:

    cpu_exec_end(cpu);
    bql_lock();

    qatomic_set(&cpu->exit_request, false);

    return rc;
}
/* End vCPU functions */

static void
bhyve_ipi_signal(int sigcpu)
{
    if (current_cpu) {
        AccelCPUState *qcpu = current_cpu->accel;

        vm_suspend_cpu(qcpu->vcpu);
    }
}

static void
bhyve_init_cpu_signals(void)
{
    struct sigaction sigact;
    sigset_t set;

    /* Install the IPI handler. */
    memset(&sigact, 0, sizeof(sigact));
    sigact.sa_handler = bhyve_ipi_signal;
    sigaction(SIG_IPI, &sigact, NULL);

    /* Allow IPIs on the current thread. */
    sigprocmask(SIG_BLOCK, NULL, &set);
    sigdelset(&set, SIG_IPI);
    pthread_sigmask(SIG_SETMASK, &set, NULL);
}

/* vCPU initialization functions */
int bhyve_init_vcpu(CPUState *cpu)
{
    struct bhyve_machine* mach = get_bhyve_mach();

    AccelCPUState *qcpu;
    int err, tmp;

    qcpu = g_new0(AccelCPUState, 1);
    bhyve_init_cpu_signals();

    // Create vCPU
    qcpu->vcpu = vm_vcpu_open(mach->vm, cpu->cpu_index); // cpu_index 0 is BSP

    err = vm_get_capability(qcpu->vcpu, VM_CAP_HALT_EXIT, &tmp);
    if (err < 0) {
		fprintf(stderr, "Could not get capability halt exit (%d)\n", err);
    }
    err = vm_set_capability(qcpu->vcpu, VM_CAP_HALT_EXIT, 1);
    err = vm_set_capability(qcpu->vcpu, VM_CAP_PAUSE_EXIT, 0);
    err = vm_set_x2apic_state(qcpu->vcpu, X2APIC_DISABLED);
	err = vm_set_capability(qcpu->vcpu, VM_CAP_ENABLE_INVPCID, 1);
	err = vm_set_capability(qcpu->vcpu, VM_CAP_IPI_EXIT, 1);
    BHYVE_DPRINTF("[INIT] vcpu%d: VM_CAP_IPI_EXIT set result: %d (0=OK)\n",
            cpu->cpu_index, err);

    // Start vCPU
    if (cpu->cpu_index == 0) { // BSP
        // Can run in real mode
        err = vm_set_capability(qcpu->vcpu,
            VM_CAP_UNRESTRICTED_GUEST, 1);

        err = vcpu_reset(qcpu->vcpu);
        assert(err == 0);

        /*
         * Disable vLAPIC software-enable (SVR bit 8) so that
         * vlapic_trigger_lvt() takes the "LAPIC disabled" bypass
         * path, which calls vm_inject_extint() directly instead
         * of going through vlapic_fire_lvt() → lvt_last[] mask
         * check.  lapic_set_state() updates the LAPIC page but
         * NOT the cached lvt_last[] array, so setting LINT0=ExtINT
         * via set_state never takes effect.  Clearing SVR enable
         * avoids that entire code path.
         */
        {
            struct vm_lapic_state lapic_state;
            int lapic_err;

            lapic_err = vm_lapic_get_state(qcpu->vcpu, &lapic_state);
            if (lapic_err == 0) {
                lapic_state.fields[0xf].data &= ~0x100; /* clear APIC_SVR_ENABLE */
                lapic_err = vm_lapic_set_state(qcpu->vcpu, &lapic_state);
                if (lapic_err != 0) {
                    fprintf(stderr, "bhyve: SVR disable failed: %d\n", lapic_err);
                }
            } else {
                fprintf(stderr, "bhyve: SVR get_state failed: %d\n", lapic_err);
            }
        }
    } else {
        /*
         * AP: set up capabilities. Activate in the kernel so the AP
         * appears in vm_active_cpus() — required for vlapic_calcdest()
         * to include it in INIT/SIPI IPI destinations. Without this,
         * the BSP's INIT+SIPI to wake the AP is silently dropped.
         *
         * We also suspend the AP (adds to debug_cpus, not
         * suspended_cpus) so vm_resume_cpu can be called before the
         * first vm_run.
         */
        err = vm_set_capability(qcpu->vcpu,
            VM_CAP_UNRESTRICTED_GUEST, 1);
        cpu->halted = true;
        cpu->stopped = true;
    }

    {
        /*
         * Activate ALL vCPUs in the kernel so that the LAPIC model
         * can deliver INIT+SIPI IPIs between them. Without this,
         * the kernel's vlapic_calcdest() can't find inactive APs
         * and SPINUP_AP exits are never generated.
         *
         * BSP: activate + suspend so it starts running.
         * APs: activate + suspend so they exist in the kernel LAPIC
         *      model. They stay halted in QEMU (wait-for-SIPI) and
         *      won't enter vm_run until SPINUP_AP arrives.
         */
        err = vm_activate_cpu(qcpu->vcpu);
        if (err) {
            fprintf(stderr, "*** vm_activate_cpu(%d) failed: %d\n",
                    cpu->cpu_index, err);
        }
        err = vm_suspend_cpu(qcpu->vcpu);
        if (err) {
            fprintf(stderr, "*** vm_suspend_cpu(%d) failed: %d\n",
                    cpu->cpu_index, err);
        }
    }

    // Sync registers on exec
    qcpu->dirty = true;
    cpu->accel = qcpu;

    /*
     * Set hardware breakpoint on intr_init_final's STI instruction
     * (FreeBSD 15.0 kernel address 0xffffffff810411f4) so we get a
     * VM_EXITCODE_DEBUG exit right before the guest enables interrupts.
     * This lets us inspect and scrub the vLAPIC IRR to prevent trap 30.
     * Only set on BSP (cpu_index 0).
     */
    /* DR0 breakpoint disabled — guest clears DR7 during early init,
     * and the debug exception fires at wrong UEFI addresses causing
     * an infinite DEBUG exit loop. The targeted IRR scrub in pre_run
     * handles trap 30 prevention instead. */

    return 0; // Return success
}

void bhyve_destroy_vcpu(CPUState *cpu) {
    AccelCPUState *qcpu = cpu->accel;

    if (qcpu->lapic_poll_timer) {
        timer_del(qcpu->lapic_poll_timer);
        timer_free(qcpu->lapic_poll_timer);
        qcpu->lapic_poll_timer = NULL;
    }
    vm_vcpu_close(qcpu->vcpu);
}

int bhyve_vcpu_exec(CPUState *cpu)
{
    int ret;

    while (1) {
        if (cpu->exception_index >= EXCP_INTERRUPT) {
            ret = cpu->exception_index;
            cpu->exception_index = -1;
            break;
        }

        /*
         * Only resume+run APs that have received SIPI (not halted).
         * APs in wait-for-SIPI state must not enter vm_run — the kernel
         * would either return SUSPENDED or execute from an undefined RIP.
         * QEMU's main loop handles the halt_cond wait.
         *
         * RACE FIX: SPINUP_AP/IPI handlers call cpu_interrupt(SIPI)
         * which kicks this thread, but halted=false is set AFTER the
         * kick. This thread may wake and see halted=true before the
         * caller clears it. Check for pending SIPI/INIT before giving
         * up — if one is pending, clear halted and proceed to
         * bhyve_vcpu_run where pre_run will process it.
         */
        if (cpu->halted) {
            if (cpu->interrupt_request &
                (CPU_INTERRUPT_SIPI | CPU_INTERRUPT_INIT)) {
                cpu->halted = false;
                BHYVE_DPRINTF("[SMP] vcpu%d: SIPI/INIT pending while halted "
                        "— clearing halted (race recovery)\n",
                        cpu->cpu_index);
            } else {
                cpu->exception_index = EXCP_HLT;
                ret = EXCP_HLT;
                break;
            }
        }

        vm_resume_cpu(cpu->accel->vcpu);
        ret = bhyve_vcpu_run(cpu);
        if (ret != 0) {
            break;
        }
    }

    return ret;
}

static void
do_bhyve_cpu_synchronize_state(CPUState *cpu, run_on_cpu_data arg)
{
    vmm_get_registers(cpu);
    cpu->accel->dirty = true;
}

static void
do_bhyve_cpu_synchronize_post_reset(CPUState *cpu, run_on_cpu_data arg)
{
    vmm_set_registers(cpu);
    cpu->accel->dirty = false;
}

static void
do_bhyve_cpu_synchronize_pre_loadvm(CPUState *cpu, run_on_cpu_data arg)
{
    cpu->accel->dirty = true;
}

/* State Synchronization */
void bhyve_cpu_synchronize_state(CPUState *cpu)
{
    if (!cpu->accel->dirty) {
        run_on_cpu(cpu, do_bhyve_cpu_synchronize_state, RUN_ON_CPU_NULL);
    }
}

void bhyve_cpu_synchronize_post_reset(CPUState *cpu)
{
    run_on_cpu(cpu, do_bhyve_cpu_synchronize_post_reset, RUN_ON_CPU_NULL);
}

void bhyve_cpu_synchronize_post_init(CPUState *cpu)
{
    run_on_cpu(cpu, do_bhyve_cpu_synchronize_post_reset, RUN_ON_CPU_NULL);
}

void bhyve_cpu_synchronize_pre_loadvm(CPUState *cpu)
{
    run_on_cpu(cpu, do_bhyve_cpu_synchronize_pre_loadvm, RUN_ON_CPU_NULL);
}
/* End State Syncrhonization */

/* Memory Support */
struct bhyve_seg_and_off {
    struct bhyve_host_seg seg;
    size_t offset;
};

static struct bhyve_seg_and_off calc_segoff_from_vmap(GArray *host_vmap, void* host_va) {
    struct bhyve_seg_and_off ret;
    struct bhyve_host_seg seg;
    for (size_t i = 0; i < host_vmap->len; i++) {
        seg = g_array_index(host_vmap, struct bhyve_host_seg, i);
        if (IN_MEMRANGE((char *)seg.seg_start, seg.size, (char *)host_va)) {
            ret.offset = (char*)host_va - (char*)seg.seg_start;
            ret.seg = seg;
            return ret;
        }
    }

    ret.offset = -1;
    return ret;
}

static void bhyve_update_mapping(hwaddr start_pa, ram_addr_t size,
                                 void *host_va, int add, int rom,
                                 const char *name)
{
    struct bhyve_machine *mach = get_bhyve_mach();
    struct bhyve_seg_and_off segoff;
    int prot;
    segoff = calc_segoff_from_vmap(mach->host_vmap, host_va);

    if (add) {
        prot = PROT_READ | PROT_EXEC;
        if (!rom) {
            prot |= PROT_WRITE;
        }
        vm_mmap_memseg(mach->vm, start_pa, segoff.seg.segid, segoff.offset, size, prot);
    } else {
        vm_munmap_memseg(mach->vm, start_pa, size);
    }
}

static void bhyve_process_section(MemoryRegionSection *section, int add)
{
    MemoryRegion *mr = section->mr;
    hwaddr start_pa = section->offset_within_address_space;
    ram_addr_t size = int128_get64(section->size);
    unsigned int delta;
    uint64_t host_va;

    // Even Bios and ROM is backed by ram (except UEFI mode)
    if (!memory_region_is_ram(mr) && strcmp(mr->name, "system.flash0") && strcmp(mr->name, "system.flash1")) {
        return;
    }

    // Ensure MemoryRegion is aligned on page boundary and size is multiple of page size
    delta = qemu_real_host_page_size() - (start_pa & ~qemu_real_host_page_mask());
    delta &= ~qemu_real_host_page_mask();
    if (delta > size) {
        return;
    }
    start_pa += delta;
    size -= delta;
    size &= qemu_real_host_page_mask();
    if (!size || (start_pa & ~qemu_real_host_page_mask())) {
        return;
    }

    host_va = (uintptr_t)memory_region_get_ram_ptr(mr) +
        section->offset_within_region + delta;

    bhyve_update_mapping(start_pa, size, (void*)(uintptr_t)host_va, add,
        memory_region_is_rom(mr), mr->name);
    return;
}

static void bhyve_region_add(MemoryListener *listener,
                             MemoryRegionSection *section)
{
    memory_region_ref(section->mr);
    bhyve_process_section(section, 1);
}

static void bhyve_region_del(MemoryListener *listener,
                             MemoryRegionSection *section)
{
    bhyve_process_section(section, 0);
    memory_region_unref(section->mr);
}

static void bhyve_transaction_begin(MemoryListener *listener)
{
}

static void bhyve_transaction_commit(MemoryListener *listener)
{
}

static void bhyve_log_sync(MemoryListener *listener,
                           MemoryRegionSection *section)
{
    MemoryRegion *mr = section->mr;

    if (!memory_region_is_ram(mr)) {
        return;
    }

    memory_region_set_dirty(mr, 0, int128_get64(section->size));
}

static MemoryListener bhyve_memory_listener = {
    .name = "bhyve",
    .begin = bhyve_transaction_begin,
    .commit = bhyve_transaction_commit,
    .region_add = bhyve_region_add,
    .region_del = bhyve_region_del,
    .log_sync = bhyve_log_sync,
    .priority = MEMORY_LISTENER_PRIORITY_ACCEL,
};

static void bhyve_memory_init(void)
{
    memory_listener_register(&bhyve_memory_listener, &address_space_memory);
}

/* Allocate memory */
static void* bhyve_allocate_pc_memory(size_t mr_size, const char* name, int segid) {
    struct bhyve_machine *mach = get_bhyve_mach();
    char* baseaddr;
    int err;

    err = vm_setup_qmemory(mach->vm, mr_size, segid, VM_MMAP_ALL, name);
    if (err < 0) {
        fprintf(stderr, "Couldn't setup PC Memory\n");
        exit(4);
    }

    err = vm_get_guestmem_from_ctx(mach->vm, &baseaddr, NULL, NULL);
    if (err < 0) {
        fprintf(stderr, "Couldn't access machine baseaddr\n");
        exit(4);
    }
    return baseaddr;
}

static char *bhyve_serialize_name(const char *input, int segid) {
    if (!input) return NULL;

    /*
     * Produce a unique name that fits in VM_MAX_SUFFIXLEN (15) chars.
     * Format: up to 12 alphanumeric chars from input + "_" + segid (decimal).
     * Strip '/', '@', and other non-alnum characters.
     */
    #define MAX_PREFIX 12
    char prefix[MAX_PREFIX + 1];
    size_t len = strlen(input);
    size_t j = 0;

    /* Scan from the end to get the most distinctive part */
    size_t start = 0;
    size_t count = 0;
    for (size_t k = len; k > 0; k--) {
        char c = input[k - 1];
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') || c == '.' || c == '-') {
            count++;
            if (count == MAX_PREFIX) {
                start = k - 1;
                break;
            }
        }
        if (count > 0 && start == 0) start = k - 1;
    }
    if (count < MAX_PREFIX) start = 0;

    for (size_t k = start; k < len && j < MAX_PREFIX; k++) {
        char c = input[k];
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') || c == '.' || c == '-') {
            prefix[j++] = c;
        }
    }
    prefix[j] = '\0';

    /* Build final name: prefix_segid */
    char *output = malloc(16); /* VM_MAX_SUFFIXLEN + 1 */
    if (!output) return NULL;
    snprintf(output, 16, "%s_%d", prefix, segid);
    return output;
    #undef MAX_PREFIX
}


void *bhyve_ram_alloc(size_t mr_size, uint64_t *alignment, int flags, const char* name) {
    struct bhyve_machine *mach = get_bhyve_mach();
    struct bhyve_host_seg ram_memseg;
    ram_memseg.mmap_flags = MAP_SHARED | MAP_NORESERVE | MAP_FIXED;
    ram_memseg.segid = mach->segid_num;
    ram_memseg.size = mr_size;
    ram_memseg.name = bhyve_serialize_name(name, ram_memseg.segid);
    puts(name);

    if (strcmp(name, "pc.ram") == 0) {
        ram_memseg.seg_start = bhyve_allocate_pc_memory(mr_size, ram_memseg.name, mach->segid_num++);
    } else {
        ram_memseg.seg_start = vm_create_devmem(mach->vm, mach->segid_num++, ram_memseg.name, mr_size);
    }
    if (!ram_memseg.seg_start || ram_memseg.seg_start == (void*)SIZE_MAX) {
        fprintf(stderr, "Could not allocate device memory for %s\n", name);
        exit(4);
    }
    *alignment = SUPERPAGE_SIZE;
    g_array_append_val(mach->host_vmap, ram_memseg);
    return ram_memseg.seg_start;

}
/* End Memory Support */

/* Kernel IRQchip Processing */
static void bhyve_set_kernel_irqchip(Object *obj, Visitor *v,
                                   const char *name, void *opaque,
                                   Error **errp)
{
    struct bhyve_machine *mach = &bhyve_mach;
    OnOffSplit mode;

    if (!visit_type_OnOffSplit(v, name, &mode, errp)) {
        return;
    }

    switch (mode) {
    case ON_OFF_SPLIT_ON:
        /* In kernel LAPIC */
        mach->kernel_irqchip_required = true;
        break;

    case ON_OFF_SPLIT_OFF:
        /* QEMU userspace emulated LAPIC */
        mach->kernel_irqchip_required = false;
        break;

    case ON_OFF_SPLIT_SPLIT:
        error_setg(errp, "Bhyve: split irqchip currently not supported");
        error_append_hint(errp,
            "Try without kernel-irqchip or with kernel-irqchip=on|off");
        break;

    default:
        /*
         * The value was checked in visit_type_OnOffSplit() above. If
         * we get here, then something is wrong in QEMU.
         */
        abort();
    }
}

bool bhyve_apic_in_platform(void) {
    return bhyve_mach.kernel_irqchip_required;
}
/* End Kernel IRQchip Processing */

static int do_open(const char *vmname, MachineState* ms) {
    /* Temporary Machine Initialization*/
    struct bhyve_machine* mach = get_bhyve_mach();
    int err;

    // Close last VM if it exists
    if ((mach->vm = vm_open(vmname))) {
        vm_destroy(mach->vm);
        mach->vm = NULL;
    }

    //In the original code segid_num was initialized with 1, keeping this. But the docs say IDs are from 0 to 15...
    mach->segid_num = 1;
    mach->vm = vm_openf(vmname, VMMAPI_OPEN_CREATE);

    if (mach->vm == NULL) {
        fprintf(stderr, "bhyve: vm_openf('%s') failed: %s (errno=%d)\n"
                "  Hint: run as root, or destroy stale VM with: "
                "bhyvectl --vm=%s --destroy\n",
                vmname, strerror(errno), errno, vmname);
        return -1;
    }

    // Set Topology
    err = vm_set_flags(mach->vm, VM_OP_F_QEMU);
    if (err) {
        fprintf(stderr, "bhyve: vm_set_flags failed: %s (errno=%d)\n",
                strerror(errno), errno);
        return -1;
    }
    err = vm_set_topology(mach->vm, ms->smp.sockets, ms->smp.cores, ms->smp.threads, 0);

    vm_set_memflags(mach->vm, 0);

    /* End Memory */
    return err;
}


/*
 * Main-loop diagnostic timer: fires every second to verify
 * the QEMU main event loop is running and processing events.
 */
/*
 * Workaround for broken glib main-loop dispatch with bhyve accelerator.
 *
 * The glib GSource mechanism (used by all QEMU chardev backends to poll
 * stdin/sockets for incoming data) stops dispatching after initialization.
 * QEMU timers (QEMU_CLOCK_REALTIME) still work because they go through
 * qemu_clock_run_all_timers(), not glib dispatch.
 *
 * Fix: poll stdin directly from a QEMU timer callback (which fires with
 * BQL held) and inject characters into the chardev via qemu_chr_be_write().
 */
#include <fcntl.h>
#include "chardev/char.h"
#include "chardev/char-fe.h"

static QEMUTimer *mainloop_diag_timer;
static Chardev *stdin_chardev = NULL;
static bool stdin_nonblock_set = false;

static void mainloop_diag_cb(void *opaque)
{
    /* Lazy lookup of the chardev -- try common names */
    if (!stdin_chardev) {
        stdin_chardev = qemu_chr_find("con0");      /* virtio-console */
        if (!stdin_chardev)
            stdin_chardev = qemu_chr_find("serial0"); /* -serial stdio */
        if (!stdin_chardev)
            stdin_chardev = qemu_chr_find("compat_monitor0");
        /* found it */
    }

    /* Set stdin to non-blocking (once) */
    if (!stdin_nonblock_set) {
        int flags = fcntl(STDIN_FILENO, F_GETFL);
        if (flags >= 0) {
            fcntl(STDIN_FILENO, F_SETFL, flags | O_NONBLOCK);
            stdin_nonblock_set = true;
        }
    }

    /* Poll stdin and inject into chardev */
    if (stdin_chardev && stdin_nonblock_set) {
        uint8_t buf[64];
        int n = read(STDIN_FILENO, buf, sizeof(buf));
        if (n > 0) {
            qemu_chr_be_write(stdin_chardev, buf, n);
        }
    }

    /* Re-arm: 5ms for responsive input */
    timer_mod_ns(mainloop_diag_timer,
                 qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 5000000LL);
}

static int
bhyve_accel_init(AccelState *as, MachineState *ms)
{
    int err;

    /*
     * Make stderr fully unbuffered so diagnostic output survives host
     * freezes (data in the C buffer is lost if the machine hangs before
     * fflush).  With line- or block-buffered stderr redirected to a
     * file, a hard lockup produces a 0-byte log — useless for diagnosis.
     */
    setbuf(stderr, NULL);

    printf("Bhyve Accelerator Machine Initialization\n");

    /* Start main-loop diagnostic timer */
    mainloop_diag_timer = timer_new_ns(QEMU_CLOCK_REALTIME,
                                        mainloop_diag_cb, NULL);
    timer_mod_ns(mainloop_diag_timer,
                 qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 1000000000LL);
    /* Also handle SIGTERM (from timeout) */
    signal(SIGTERM, SIG_DFL); /* Will be overridden below */

    err = do_open(VM_NAME, ms);
    if (err) {
        return -1;
    }

    /* Setup Memory */
    bhyve_memory_init();

    /*
     * Enable CPU ticks so QEMU_CLOCK_VIRTUAL advances with real time.
     * Without this, the ACPI PM Timer (port 0x408) returns a constant
     * value and UEFI firmware spins forever in delay loops.
     */
    cpu_enable_ticks();

    /*
     * Mask all 8259A PIC IRQs so no PIC interrupts fire before the guest
     * has set up its IDT handlers.  UEFI firmware may reprogram the PIC
     * base vector (e.g. to 0x40) and leave IRQ0 (PIT timer) unmasked.
     * If the PIT fires before the guest installs real handlers, the
     * default Xrsvd IDT stub pushes T_RESERVED (30) → kernel panic.
     *
     * The guest OS will unmask specific IRQs as it initializes drivers.
     * PIC1 (master) mask register = port 0x21, PIC2 (slave) = port 0xA1.
     * Writing 0xFF masks all 8 IRQs on each chip.
     */
    cpu_outb(0x21, 0xFF);  /* Mask all master PIC IRQs */
    cpu_outb(0xA1, 0xFF);  /* Mask all slave PIC IRQs */
    printf("8259A PIC: all IRQs masked (master=0xFF, slave=0xFF)\n");

    return 0;
}

static void
bhyve_accel_class_init(ObjectClass *oc, const void *data)
{
    AccelClass *ac = ACCEL_CLASS(oc);
    ac->name = "Bhyve";
    ac->init_machine = bhyve_accel_init;
    ac->allowed = &bhyve_allowed;

    object_class_property_add(oc, "kernel-irqchip", "on|off|split",
        NULL, bhyve_set_kernel_irqchip,
        NULL, NULL);
    object_class_property_set_description(oc, "kernel-irqchip",
        "Configure Bhyve in-kernel irqchip");
}

static void bhyve_accel_instance_init(Object *obj)
{
    struct bhyve_machine *bhyvep = &bhyve_mach;

    memset(bhyvep, 0, sizeof(struct bhyve_machine));
    bhyvep->host_vmap = g_array_new(FALSE, FALSE, sizeof(struct bhyve_host_seg));

    /* Turn off kernel-irqchip, by default */
    bhyvep->kernel_irqchip_required = true;
    bhyvep->cpu_vendor = get_cpu_vendor();
}

static const TypeInfo bhyve_accel_type = {
    .name = ACCEL_CLASS_NAME("bhyve"),
    .parent = TYPE_ACCEL,
    // Initializes instance specific data
    .instance_init = bhyve_accel_instance_init,
    // Called once when first loaded
    .class_init = bhyve_accel_class_init,
};

static void
bhyve_type_init(void)
{
    type_register_static(&bhyve_accel_type);
}

type_init(bhyve_type_init);
