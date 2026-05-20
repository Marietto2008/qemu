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

#include <signal.h>
#include <unistd.h>
#include <errno.h>
#include <sys/sched.h>

#include <machine/specialreg.h>

/*
 * Tracing wrapper for vm_lapic_irq — logs ALL low-vector injections
 * to help debug trap 30 (reserved fault) in FreeBSD guest.
 */
static inline int traced_vm_lapic_irq(struct vcpu *vcpu, int vector,
                                       const char *caller, int line)
{
    if (vector < 32) {
        fprintf(stderr, "*** TRACED_LAPIC_IRQ: vector=%d (0x%x) from %s:%d — "
                "LOW VECTOR, would cause guest trap!\n",
                vector, vector, caller, line);
        return (-1);  /* block injection */
    }
    return vm_lapic_irq(vcpu, vector);
}
/* Replace all direct vm_lapic_irq calls with traced version */
#define vm_lapic_irq(vcpu, vector) \
    traced_vm_lapic_irq((vcpu), (vector), __func__, __LINE__)
#include <string.h>
#include <sys/ioctl.h>
#include <vmmapi.h>
#include <machine/vmm_dev.h>

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
static void scrub_lapic_bad_vectors(struct vcpu *vcpu)
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

    /* IRR[1]: vectors 32-63 — clear vector 32 (PIC base 0x20) */
    uint32_t irr1 = state.fields[0x21].data;
    if (irr1 & (1u << 0)) {  /* bit 0 = vector 32 */
        state.fields[0x21].data = irr1 & ~(1u << 0);
        modified = 1;
    }

    /* IRR[2]: vectors 64-95 — clear vector 64 (UEFI PIC base 0x40) */
    uint32_t irr2 = state.fields[0x22].data;
    if (irr2 & (1u << 0)) {  /* bit 0 = vector 64 */
        state.fields[0x22].data = irr2 & ~(1u << 0);
        modified = 1;
    }

    /* Check LVT Timer for low vector */
    uint32_t lvt_timer = state.fields[0x32].data;
    if ((lvt_timer & 0xFF) < 32 && !((lvt_timer >> 16) & 1)) {
        state.fields[0x32].data = lvt_timer | (1 << 16);
        modified = 1;
    }

    if (modified) {
        /*
         * Preserve APIC ID (fields[2], offset 0x020). vcpu_ioctl clobbers
         * fields[0] with the vcpuid; verify fields[2] wasn't also affected.
         * Re-read and restore APIC ID to prevent corruption.
         */
        struct vm_lapic_state verify;
        memset(&verify, 0, sizeof(verify));
        vcpu_ioctl(vcpu, VM_LAPIC_GET_STATE, &verify);
        state.fields[2].data = verify.fields[2].data;
        vcpu_ioctl(vcpu, VM_LAPIC_SET_STATE, &state);
    }
}

/* -------------------------------------------------------------------------- */

/* MMIO emulation counters */
static volatile long mmio_kernel_ok = 0;    /* decoded by kernel vie */
static volatile long mmio_user_read = 0;    /* emulated reads in userspace */
static volatile long mmio_user_write = 0;   /* emulated writes in userspace */
static volatile long mmio_user_skip = 0;    /* unknown opcode, skipped */
static volatile long mmio_last_gpa = 0;     /* last GPA accessed */
static volatile long io_total = 0;          /* total I/O port exits */
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

static void mmio_print_stats(void) {
    fprintf(stderr, "\n=== MMIO/IO Statistics ===\n"
            "  vm_run calls:    %ld\n"
            "  I/O port exits:  %ld\n"
            "  MMIO kernel ok:  %ld\n"
            "  MMIO user read:  %ld\n"
            "  MMIO user write: %ld\n"
            "  MMIO user skip:  %ld\n"
            "  Last MMIO GPA:   0x%lx\n"
            "  --- Exit codes ---\n"
            "  HLT:    %ld\n"
            "  BOGUS:  %ld\n"
            "  INOUT:  %ld\n"
            "  DEBUG:  %ld\n"
            "  PAUSE:  %ld\n"
            "  OTHER:  %ld\n"
            "  --- IRQ counters (8259) ---\n"
            "  IRQ0 assert:   %ld\n"
            "  IRQ0 deassert: %ld\n"
            "  Other IRQ:     %ld\n"
            "========================\n",
            vm_run_total, io_total,
            mmio_kernel_ok, mmio_user_read,
            mmio_user_write, mmio_user_skip,
            mmio_last_gpa,
            exit_hlt, exit_bogus, exit_inout,
            exit_debug, exit_pause, exit_other,
            pic_irq0_assert, pic_irq0_deassert,
            pic_other_irq);
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
    int hwintr_state;       /* 0=off, 1=masked, 2=grace, 3=done */
    bool fsgsbase_forced;   /* CR4.FSGSBASE force-set done for this vCPU */
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
static int madt_patch_attempts = 0;

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

    fprintf(stderr, "*** MADT-PATCH: scanning GPA 0x%lx-0x%lx via cpu_physical_memory_read...\n",
            (unsigned long)scan_start, (unsigned long)scan_end);

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
            fprintf(stderr, "*** MADT-PATCH: found BHYVE MADT at GPA 0x%lx len=%u "
                    "OEM=%.6s tbl=%.8s csum=%u\n",
                    (unsigned long)tbl_gpa, tbl_len,
                    full_tbl + 10, full_tbl + 16, csum);

            if (csum == 0 && tbl_len >= 62) {
                madt_gpa = tbl_gpa;
                break;
            }
            fprintf(stderr, "*** MADT-PATCH: bad checksum (%u) or short, skipping\n", csum);
        }
        if (madt_gpa) break;
    }

    if (!madt_gpa) {
        fprintf(stderr, "*** MADT-PATCH: MADT not found in firmware area\n");
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

    fprintf(stderr, "*** MADT-PATCH: found %d CPU entries, need %d\n",
            existing_cpus, num_cpus);

    if (existing_cpus >= num_cpus) {
        fprintf(stderr, "*** MADT-PATCH: already has enough CPUs\n");
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
                    fprintf(stderr, "*** MADT-PATCH: added CPU APIC_ID=%d\n",
                            cpu_id);
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

    fprintf(stderr, "*** MADT-PATCH: SUCCESS — patched MADT at GPA 0x%lx, "
            "new length=%d (%d CPUs)\n",
            (unsigned long)madt_gpa, new_offset, num_cpus);

    madt_patched = true;
}

static bool bhyve_allowed;

int
bhyve_enabled(void) {
    return bhyve_allowed;
}

/*
 * Inject a vector into a vCPU's kernel vLAPIC.  Called by PIC/IOAPIC
 * set_irq handlers to wake vCPUs sleeping in the kernel HLT handler.
 * vm_lapic_irq() sets the IRR bit and calls vcpu_notify_event(),
 * which wakes a VCPU_SLEEPING vCPU via wakeup_one().
 */
void bhyve_inject_lapic_irq(CPUState *cpu, int vector)
{
    if (cpu && cpu->accel && cpu->accel->vcpu) {
        if (vector < 32) {
            fprintf(stderr, "*** LAPIC_IRQ: BLOCKED low vector %d (0x%x) — "
                    "would cause guest trap!\n", vector, vector);
            return;
        }
        vm_lapic_irq(cpu->accel->vcpu, vector);
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

    io_total++;
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
    uint64_t val;

    switch (mach->cpu_vendor) {
    case VENDOR_INTEL:
        error = bhyve_intel_rdmsr(num, &val);
        goto finish;
    case VENDOR_AMD:
        error = bhyve_amd_rdmsr(num, &val);
        goto finish;
    case VENDOR_UNKNOWN:
        return -1;
    }

finish:
    error = vm_set_register(vcpu, VM_REG_GUEST_RAX, val);
    error = vm_set_register(vcpu, VM_REG_GUEST_RDX, val >> 32);

    return error;
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

static void bhyve_vcpu_pre_run(CPUState *cpu) {
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu *vcpu = qcpu->vcpu;
    X86CPU *x86_cpu = X86_CPU(cpu);
    uint8_t tpr;
    bool sync_tpr = false;

    bql_lock();

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
         * We must inject from userspace via vm_lapic_irq().
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
        if (pending) {
            int irq = __builtin_ctz(pending);  /* lowest set bit = highest priority */

            /*
             * Map ISA IRQ to IOAPIC pin: IRQ0→pin2, others→same pin#.
             * Use QEMU's IOAPIC vector table (populated when guest
             * programs IOAPIC RTEs via MMIO). Fall back to PIC vectors
             * only if the guest hasn't programmed the IOAPIC yet.
             */
            int pin = (irq == 0) ? 2 : irq;
            int vector = 0;

            /* Use QEMU's own IOAPIC RTE vector (set by guest MMIO writes) */
            if (pin < 24) {
                uint8_t qemu_vec = bhyve_ioapic_vectors[pin];
                if (qemu_vec >= 0x10) {
                    vector = qemu_vec;
                }
            }

            /*
             * If IOAPIC not configured for this pin, DROP the interrupt.
             * Don't fall back to PIC vectors (0x20+irq) — those vectors
             * likely have no IDT handler during early boot and would
             * cause trap 30 (Xrsvd). The guest will receive the interrupt
             * through the IOAPIC once it programs the proper RTE.
             */
            if (vector == 0) {
                static int pic_drop_log = 0;
                if (pic_drop_log++ < 5)
                    fprintf(stderr, "*** PIC IRQ%d dropped: IOAPIC pin %d "
                            "not configured yet\n", irq, pin);
            } else if (vector < 32) {
                fprintf(stderr, "*** PRE_RUN PIC: BLOCKED low vector %d "
                        "(irq=%d pin=%d)\n", vector, irq, pin);
            } else {
                vm_lapic_irq(vcpu, vector);
            }

            /* If multiple IRQs pending, re-set the flag for next pre_run */
            pending &= ~(1u << irq);
            if (pending) {
                __atomic_or_fetch(&bhyve_pic_pending_irqs, pending,
                                  __ATOMIC_RELEASE);
                cpu_interrupt(cpu, CPU_INTERRUPT_HARD);
            }
        }

        /*
         * Inject pending IOAPIC interrupts.
         *
         * The kernel's vmx_inject_interrupts doesn't work for QEMU-mode VMs
         * because the kernel's vioapic never sees the guest's RTE programming
         * (QEMU handles IOAPIC MMIO in userspace). So we inject from
         * userspace using the vectors captured by bhyve_ioapic_set_irq.
         */
        uint32_t ioapic_pending = __atomic_exchange_n(
            &bhyve_ioapic_pending_irqs, 0, __ATOMIC_ACQ_REL);
        if (ioapic_pending) {
            while (ioapic_pending) {
                int pin = __builtin_ctz(ioapic_pending);
                ioapic_pending &= ~(1u << pin);

                int vector = (pin < 24) ? bhyve_ioapic_vectors[pin] : 0;

                if (vector >= 0x10 && vector >= 32) {
                    vm_lapic_irq(vcpu, vector);
                } else if (vector >= 0x10 && vector < 32) {
                    fprintf(stderr, "*** PRE_RUN IOAPIC: BLOCKED low vector "
                            "%d (pin=%d) — would cause guest trap!\n",
                            vector, pin);
                } else {
                    /* Vector not yet programmed — drop (guest will
                     * re-trigger once IOAPIC RTEs are configured) */
                    static int ioapic_drop_log = 0;
                    if (ioapic_drop_log++ < 5)
                        fprintf(stderr, "*** IOAPIC pin %d dropped: "
                                "vector not configured\n", pin);
                }
            }
        }
    }

    if (sync_tpr) {
        vm_set_register(vcpu, VM_REG_GUEST_TPR, qcpu->tpr);
    }

    bql_unlock();
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
        bql_lock();
        cpu_set_apic_tpr(x86_cpu->apic_state, qcpu->tpr);
        bql_unlock();
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
         */
        {
            struct vm_lapic_state lapic_state;
            int lapic_err;

            /* Read current kernel LAPIC state */
            lapic_err = vm_lapic_get_state(qcpu->vcpu, &lapic_state);
            if (lapic_err == 0) {
                /* Zero out IRR (Interrupt Request Register) — indices 0x20..0x27 */
                for (int i = 0x20; i <= 0x27; i++)
                    lapic_state.fields[i].data = 0;
                /* Zero out ISR (In-Service Register) — indices 0x10..0x17 */
                for (int i = 0x10; i <= 0x17; i++)
                    lapic_state.fields[i].data = 0;
                /* Zero out TMR (Trigger Mode Register) — indices 0x18..0x1f */
                for (int i = 0x18; i <= 0x1f; i++)
                    lapic_state.fields[i].data = 0;
                /* Reset DFR to all-ones (flat model) per Intel INIT spec */
                lapic_state.fields[0xe].data = 0xffffffff;
                /* Reset SVR — mask all, spurious vector 0xff */
                lapic_state.fields[0xf].data = 0xff;
                /* Zero TPR, PPR, LDR */
                lapic_state.fields[0x8].data = 0;  /* TPR */
                lapic_state.fields[0xa].data = 0;  /* PPR */
                lapic_state.fields[0xd].data = 0;  /* LDR */
                /* Mask all LVT entries (bit 16 = masked) */
                lapic_state.fields[0x32].data = 0x00010000; /* LVT_TIMER */
                lapic_state.fields[0x33].data = 0x00010000; /* LVT_THERMAL */
                lapic_state.fields[0x34].data = 0x00010000; /* LVT_PCINT */
                lapic_state.fields[0x35].data = 0x00010000; /* LVT_LINT0 */
                lapic_state.fields[0x36].data = 0x00010000; /* LVT_LINT1 */
                lapic_state.fields[0x37].data = 0x00010000; /* LVT_ERROR */
                lapic_state.fields[0x2f].data = 0x00010000; /* LVT_CMCI */

                /*
                 * Explicitly set the APIC ID to match the CPU index.
                 * xAPIC format: APIC ID in bits 31:24 of the APIC ID register.
                 * LAPIC offset 0x020 = fields[2].
                 * Without this, the kernel vLAPIC may have APIC ID 0 for all
                 * CPUs after INIT, causing Linux to log "APIC ID mismatch"
                 * and fail cpuhp synchronization.
                 */
                lapic_state.fields[2].data = (uint32_t)(cpu->cpu_index << 24);

                lapic_err = vm_lapic_set_state(qcpu->vcpu, &lapic_state);
                if (lapic_err != 0) {
                    fprintf(stderr, "INIT[%d]: kernel vLAPIC reset FAILED: %d\n",
                            cpu->cpu_index, lapic_err);
                }
            } else {
                fprintf(stderr, "INIT[%d]: vm_lapic_get_state failed: %d\n",
                        cpu->cpu_index, lapic_err);
            }
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
        bql_unlock();
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
                scrub_lapic_bad_vectors(qcpu->vcpu);
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

            if (qcpu->hwintr_state == 0 && in_kernel && !guest_if) {
                /* Guest entered kernel with IF=0 — mask interrupts */
                vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 1);
                qcpu->hwintr_state = 1;
                fprintf(stderr, "*** MASK_HWINTR[%d]: enabled (kernel IF=0, RIP=0x%lx)\n",
                        cpu->cpu_index, (unsigned long)pre_rip);
            } else if (qcpu->hwintr_state == 1 && guest_if && in_kernel) {
                /*
                 * Guest did STI in kernel mode — scrub ALL stale IRR
                 * vectors and immediately unmask. The guest needs
                 * interrupts for disk I/O (root mount), but stale
                 * PIC/IOAPIC vectors in IRR would cause trap 30.
                 * After scrub, fresh interrupts use properly-configured
                 * IOAPIC vectors with installed IDT handlers.
                 */
                struct vm_lapic_state unmask_lapic;
                memset(&unmask_lapic, 0, sizeof(unmask_lapic));
                if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE, &unmask_lapic) == 0) {
                    for (int i = 0; i < 8; i++) {
                        if (unmask_lapic.fields[0x20 + i].data != 0) {
                            fprintf(stderr, "*** MASK_HWINTR: scrubbing IRR[%d]"
                                    "=0x%08x before unmask\n",
                                    i, unmask_lapic.fields[0x20 + i].data);
                            unmask_lapic.fields[0x20 + i].data = 0;
                        }
                    }
                    vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE, &unmask_lapic);
                }
                vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 0);
                qcpu->hwintr_state = 3;
                fprintf(stderr, "*** MASK_HWINTR[%d]: scrubbed + disabled at IF=1 "
                        "(run #%ld, RIP=0x%lx)\n",
                        cpu->cpu_index, vm_run_total, (unsigned long)pre_rip);
            }
        }

        /* Targeted LAPIC dump when RIP is near intr_init_final (0xffffffff810411f0) */
        {
            uint64_t pre_rip = 0;
            vm_get_register(qcpu->vcpu, VM_REG_GUEST_RIP, &pre_rip);
            if (pre_rip >= 0xffffffff81041100 && pre_rip <= 0xffffffff81041210) {
                static int dump_done = 0;
                if (!dump_done) {
                    dump_done = 1;
                    fprintf(stderr, "\n*** INTR_INIT_FINAL REACHED: RIP=0x%lx (run #%ld)\n",
                            (unsigned long)pre_rip, vm_run_total);

                    /* Read RFLAGS to check IF */
                    uint64_t rflags = 0;
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RFLAGS, &rflags);
                    fprintf(stderr, "  RFLAGS=0x%lx IF=%d\n",
                            (unsigned long)rflags, (int)((rflags >> 9) & 1));

                    /* Dump full LAPIC state */
                    struct vm_lapic_state ls;
                    memset(&ls, 0, sizeof(ls));
                    if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE, &ls) == 0) {
                        fprintf(stderr, "  LAPIC state:\n");
                        /* IRR: indices 0x20-0x27 (8 regs × 32 bits = 256 vectors) */
                        for (int i = 0; i < 8; i++) {
                            uint32_t irr = ls.fields[0x20 + i].data;
                            if (irr != 0) {
                                fprintf(stderr, "    IRR[%d] (vec %d-%d) = 0x%08x\n",
                                        i, i*32, i*32+31, irr);
                            }
                        }
                        /* ISR: indices 0x10-0x17 */
                        for (int i = 0; i < 8; i++) {
                            uint32_t isr = ls.fields[0x10 + i].data;
                            if (isr != 0) {
                                fprintf(stderr, "    ISR[%d] (vec %d-%d) = 0x%08x\n",
                                        i, i*32, i*32+31, isr);
                            }
                        }
                        /* LVT Timer: index 0x32 */
                        fprintf(stderr, "    LVT_Timer = 0x%08x (vec=%d masked=%d)\n",
                                ls.fields[0x32].data,
                                ls.fields[0x32].data & 0xFF,
                                (ls.fields[0x32].data >> 16) & 1);
                        /* LVT LINT0/1: indices 0x35/0x36 */
                        fprintf(stderr, "    LVT_LINT0 = 0x%08x\n", ls.fields[0x35].data);
                        fprintf(stderr, "    LVT_LINT1 = 0x%08x\n", ls.fields[0x36].data);
                        /* TPR: index 0x08 */
                        fprintf(stderr, "    TPR = 0x%08x\n", ls.fields[0x08].data);
                        /* SVR: index 0x0F */
                        fprintf(stderr, "    SVR = 0x%08x\n", ls.fields[0x0F].data);
                    } else {
                        fprintf(stderr, "  LAPIC GET_STATE failed: errno=%d\n", errno);
                    }

                    /* Check intinfo (pending VMCS injection) */
                    uint64_t info1 = 0, info2 = 0;
                    if (vm_get_intinfo(qcpu->vcpu, &info1, &info2) == 0) {
                        fprintf(stderr, "  INTINFO: info1=0x%lx info2=0x%lx",
                                (unsigned long)info1, (unsigned long)info2);
                        if (info1 & (1ULL << 31)) {
                            fprintf(stderr, " [VALID vec=%d type=%d]",
                                    (int)(info1 & 0xFF),
                                    (int)((info1 >> 8) & 7));
                        }
                        fprintf(stderr, "\n");
                    }
                }
            }
        }

		error = vm_run(qcpu->vcpu, &vmrun);
		vm_run_total++;

<<<<<<< Updated upstream
=======
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
                fprintf(stderr, "*** CR4.FSGSBASE[%d]: forced ON (CR4=0x%lx, run #%ld)\n",
                        cpu->cpu_index, (unsigned long)cr4_now, vm_run_total);
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

>>>>>>> Stashed changes
        /* Ring buffer: last 4096 exits before crash for post-mortem */
        {
            #define EXIT_RING_SIZE 4096
            #define EXIT_RING_MASK (EXIT_RING_SIZE - 1)
            static struct {
                int exitcode; uint64_t rip; uint32_t port; long count;
                uint64_t cr4; uint8_t dirty;
            } last_exits[EXIT_RING_SIZE];
            static int exit_idx = 0;
            int ri = exit_idx & EXIT_RING_MASK;
            last_exits[ri].exitcode = vme.exitcode;
            last_exits[ri].rip = vme.rip;
            last_exits[ri].port = (vme.exitcode == VM_EXITCODE_INOUT) ? vme.u.inout.port : 0;
            last_exits[ri].count = vm_run_total;
            last_exits[ri].dirty = qcpu->dirty ? 1 : 0;
            /* Read CR4 from VMCS for corruption detection */
            {
                uint64_t cr4_val = 0;
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR4, &cr4_val);
                last_exits[ri].cr4 = cr4_val;
            }
            exit_idx++;

            /* Dump ring buffer on: VMX error, SUSPENDED, or unknown exit */
            bool do_dump = (vme.exitcode == VM_EXITCODE_VMX ||
                            vme.exitcode == VM_EXITCODE_SUSPENDED);
            if (!do_dump &&
                vme.exitcode != VM_EXITCODE_INOUT &&
                vme.exitcode != VM_EXITCODE_BOGUS &&
                vme.exitcode != VM_EXITCODE_HLT &&
                vme.exitcode != VM_EXITCODE_RDMSR &&
                vme.exitcode != VM_EXITCODE_WRMSR &&
                vme.exitcode != VM_EXITCODE_INST_EMUL &&
                vme.exitcode != VM_EXITCODE_PAUSE &&
                vme.exitcode != VM_EXITCODE_REQIDLE &&
                vme.exitcode != VM_EXITCODE_INOUT_STR &&
                vme.exitcode != VM_EXITCODE_IPI &&
                vme.exitcode != VM_EXITCODE_SPINUP_AP &&
                vme.exitcode != VM_EXITCODE_IOAPIC_EOI) {
                do_dump = true;
            }
            if (do_dump) {
                /* Print last 200 entries (not all 4096) to keep output manageable */
                int dump_count = (exit_idx < 200) ? exit_idx : 200;
                fprintf(stderr, "\n=== EXIT %d at rip=0x%lx (run #%ld) ===\n",
                        vme.exitcode, (unsigned long)vme.rip, vm_run_total);
                fprintf(stderr, "Last %d exits:\n", dump_count);
                for (int i = 0; i < dump_count; i++) {
                    int j = (exit_idx - dump_count + i) & EXIT_RING_MASK;
                    fprintf(stderr, "  [%ld] exit=%d rip=0x%lx port=0x%x cr4=0x%lx d=%d\n",
                            last_exits[j].count, last_exits[j].exitcode,
                            (unsigned long)last_exits[j].rip, last_exits[j].port,
                            (unsigned long)last_exits[j].cr4, last_exits[j].dirty);
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

		exitcode = vme.exitcode;

        switch (exitcode) {
        case VM_EXITCODE_HLT:
            exit_hlt++;
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
                if (qcpu->hwintr_state == 1) {
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
                                fprintf(stderr,
                                    "*** MASK_HWINTR[%d]: HLT scrub IRR[%d]"
                                    "=0x%08x\n",
                                    cpu->cpu_index, i,
                                    unmask_lapic.fields[0x20 + i].data);
                                unmask_lapic.fields[0x20 + i].data = 0;
                            }
                        }
                        unmask_lapic.fields[2].data = saved_apic_id;
                        vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE,
                                   &unmask_lapic);
                    }
                    vm_set_capability(qcpu->vcpu, VM_CAP_MASK_HWINTR, 0);
                    qcpu->hwintr_state = 3;
                    fprintf(stderr,
                        "*** MASK_HWINTR[%d]: scrubbed + disabled at HLT "
                        "(run #%ld)\n",
                        cpu->cpu_index, vm_run_total);
                }

                /*
                 * Precise LAPIC timer wakeup for HLT exits.
                 *
                 * 1. Read kernel vLAPIC state
                 * 2. If IRR has pending bits -> skip halt, re-enter immediately
                 * 3. Otherwise compute exact LAPIC timer deadline from CCR/DCR
                 * 4. Arm host timer for that precise moment
                 */
                struct vm_lapic_state hlt_lapic;
                int hlt_lapic_err = vm_lapic_get_state(qcpu->vcpu, &hlt_lapic);
                bool irr_pending = false;

                if (hlt_lapic_err == 0) {
                    /* Check IRR (fields 0x20..0x27) for pending interrupts */
                    for (int i = 0x20; i <= 0x27; i++) {
                        if (hlt_lapic.fields[i].data != 0) {
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
                uint64_t dbg_dr0 = 0, dbg_dr6 = 0, dbg_dr7 = 0, dbg_rflags = 0;
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_DR0, &dbg_dr0);
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_DR6, &dbg_dr6);
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_DR7, &dbg_dr7);
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_RFLAGS, &dbg_rflags);
                fprintf(stderr, "\n*** DEBUG EXIT: RIP=0x%lx (run #%ld) "
                        "DR0=0x%lx DR6=0x%lx DR7=0x%lx RFLAGS=0x%lx\n",
                        (unsigned long)dbg_rip, vm_run_total,
                        (unsigned long)dbg_dr0, (unsigned long)dbg_dr6,
                        (unsigned long)dbg_dr7, (unsigned long)dbg_rflags);

                /* If this is our intr_init_final breakpoint, dump and scrub IRR */
                if (dbg_rip >= 0xffffffff810411f0 &&
                    dbg_rip <= 0xffffffff810411f6) {
                    fprintf(stderr, "  === INTR_INIT_FINAL BREAKPOINT HIT ===\n");

                    /* Read RFLAGS */
                    uint64_t rflags = 0;
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RFLAGS, &rflags);
                    fprintf(stderr, "  RFLAGS=0x%lx IF=%d\n",
                            (unsigned long)rflags, (int)((rflags >> 9) & 1));

                    /* Dump and scrub full LAPIC state */
                    struct vm_lapic_state dbg_lapic;
                    memset(&dbg_lapic, 0, sizeof(dbg_lapic));
                    if (vcpu_ioctl(qcpu->vcpu, VM_LAPIC_GET_STATE, &dbg_lapic) == 0) {
                        int any_irr = 0;
                        fprintf(stderr, "  LAPIC IRR (pending vectors):\n");
                        for (int i = 0; i < 8; i++) {
                            uint32_t irr = dbg_lapic.fields[0x20 + i].data;
                            if (irr != 0) {
                                any_irr = 1;
                                fprintf(stderr, "    IRR[%d] (vec %d-%d) = 0x%08x",
                                        i, i*32, i*32+31, irr);
                                /* List individual vectors */
                                for (int b = 0; b < 32; b++) {
                                    if (irr & (1u << b))
                                        fprintf(stderr, " vec=%d", i*32+b);
                                }
                                fprintf(stderr, "\n");
                            }
                        }
                        if (!any_irr)
                            fprintf(stderr, "    (no pending vectors)\n");

                        /* ISR */
                        for (int i = 0; i < 8; i++) {
                            uint32_t isr = dbg_lapic.fields[0x10 + i].data;
                            if (isr != 0)
                                fprintf(stderr, "    ISR[%d] (vec %d-%d) = 0x%08x\n",
                                        i, i*32, i*32+31, isr);
                        }

                        /* LVT Timer, LINT0, LINT1, SVR */
                        fprintf(stderr, "    LVT_Timer=0x%08x (vec=%d masked=%d)\n",
                                dbg_lapic.fields[0x32].data,
                                dbg_lapic.fields[0x32].data & 0xFF,
                                (dbg_lapic.fields[0x32].data >> 16) & 1);
                        fprintf(stderr, "    LVT_LINT0=0x%08x LVT_LINT1=0x%08x\n",
                                dbg_lapic.fields[0x35].data,
                                dbg_lapic.fields[0x36].data);
                        fprintf(stderr, "    SVR=0x%08x TPR=0x%08x\n",
                                dbg_lapic.fields[0x0F].data,
                                dbg_lapic.fields[0x08].data);

                        /*
                         * SCRUB: clear ALL pending IRR vectors.
                         * At this point the guest is about to do STI.
                         * Any pending vector whose IDT entry is Xrsvd
                         * will cause trap 30. We clear all IRR and let
                         * the guest re-request interrupts after IDT setup.
                         */
                        int scrubbed = 0;
                        for (int i = 0; i < 8; i++) {
                            if (dbg_lapic.fields[0x20 + i].data != 0) {
                                fprintf(stderr, "  SCRUB: clearing IRR[%d] = 0x%08x\n",
                                        i, dbg_lapic.fields[0x20 + i].data);
                                dbg_lapic.fields[0x20 + i].data = 0;
                                scrubbed = 1;
                            }
                        }
                        if (scrubbed) {
                            vcpu_ioctl(qcpu->vcpu, VM_LAPIC_SET_STATE, &dbg_lapic);
                            fprintf(stderr, "  SCRUB: all IRR cleared, SET_STATE done\n");
                        }
                    }

                    /* Clear DR0/DR7 — breakpoint no longer needed */
                    vm_set_register(qcpu->vcpu, VM_REG_GUEST_DR0, 0);
                    vm_set_register(qcpu->vcpu, VM_REG_GUEST_DR7, 0);
                    fprintf(stderr, "  DR0/DR7 cleared, resuming guest\n");
                }
            }
            /* Clear debug state so next vm_run doesn't exit immediately */
            vm_resume_cpu(qcpu->vcpu);
            break;
        case VM_EXITCODE_INOUT:
        case VM_EXITCODE_INOUT_STR:
            exit_inout++;

            /* Safety valve: detect infinite INOUT loops.
             * Port 0x408 (PM timer) legitimately loops — only warn once.
             * For other ports, if same RIP >10000 times → abort. */
            {
                static uint64_t last_inout_rip = 0;
                static int inout_repeat_count = 0;
                static bool pm_timer_warned = false;
                if (vme.rip == last_inout_rip) {
                    inout_repeat_count++;
                    if (vme.u.inout.port == 0x408) {
                        /* PM timer busy-wait is normal firmware behavior */
                        if (!pm_timer_warned && inout_repeat_count > 1000) {
                            fprintf(stderr,
                                "*** NOTE: PM timer loop at RIP=0x%lx "
                                "(normal firmware delay, suppressing)\n",
                                (unsigned long)vme.rip);
                            pm_timer_warned = true;
                        }
                    } else if (inout_repeat_count > 10000) {
                        fprintf(stderr,
                            "\n*** FATAL: INOUT loop at RIP=0x%lx "
                            "port=0x%x (%d times, run #%ld) — aborting\n",
                            (unsigned long)vme.rip,
                            vme.u.inout.port, inout_repeat_count,
                            vm_run_total);
                        goto abort_vcpu_loop;
                    }
                } else {
                    last_inout_rip = vme.rip;
                    inout_repeat_count = 1;
                }
            }

            /*
             * Acquire BQL for I/O emulation — device models (serial, PIC,
             * etc.) expect it when modifying state and raising interrupts.
             * This mirrors KVM's pattern of locking BQL for exit handling.
             */
            bql_lock();
            rc = vm_assist_qio(qcpu->vcpu, vmm_io_callback, &vme);
            /*
             * Run timers and process main-loop I/O periodically.
             * This is critical for SLIRP networking: DHCP responses
             * are queued by SLIRP and need aio_poll to be delivered
             * back to the e1000 device model.
             *
             * Every 10 exits: run timers + poll AIO (non-blocking).
             * Every 200 exits: yield CPU so the main thread can run
             * the full main loop (SLIRP fd polling, GMainContext, etc).
             */
            if ((exit_inout % 10) == 0) {
                qemu_clock_run_timers(QEMU_CLOCK_VIRTUAL);
                qemu_clock_run_timers(QEMU_CLOCK_REALTIME);
                {
                    AioContext *ctx = qemu_get_aio_context();
                    timerlistgroup_run_timers(&ctx->tlg);
                    aio_poll(ctx, false);
                }
            }
            bql_unlock();
            if ((exit_inout % 200) == 0) {
                sched_yield();
            }
            break;
        case VM_EXITCODE_INST_EMUL:
            bql_lock();
            {
                /* Trace MMIO accesses to PCI MMIO window.
                 * Separate counters for UEFI (early) and kernel (late). */
                uint64_t mmio_gpa = vme.u.inst_emul.gpa;
                static int mmio_uefi_log = 0;
                static int mmio_kern_log = 0;
                bool is_kernel = (vme.rip >= 0xffffffff80000000ULL);
                if (mmio_gpa >= 0xc0000000ULL && mmio_gpa < 0x100000000ULL) {
                    if (is_kernel) {
                        if (mmio_kern_log < 100) {
                            fprintf(stderr, "MMIO_KERN: GPA=0x%lx rip=0x%lx vie_valid=%d\n",
                                    (unsigned long)mmio_gpa,
                                    (unsigned long)vme.rip,
                                    vme.u.inst_emul.vie.num_valid);
                            mmio_kern_log++;
                        }
                    } else if (mmio_uefi_log < 10) {
                        fprintf(stderr, "MMIO_UEFI: GPA=0x%lx rip=0x%lx\n",
                                (unsigned long)mmio_gpa,
                                (unsigned long)vme.rip);
                        mmio_uefi_log++;
                    }
                }
            }
            rc = vm_assist_qmem(qcpu->vcpu, vmm_mem_callback, &vme);
            if (rc == 0) {
                mmio_kernel_ok++;
            } else {
                /*
                 * MMIO instruction decode failed in kernel vie.
                 * Perform userspace MMIO emulation: decode the instruction,
                 * do the actual read/write through QEMU's address_space_rw,
                 * and update the guest register accordingly.
                 */
                struct vie *vie = &vme.u.inst_emul.vie;
                uint64_t gpa = vme.u.inst_emul.gpa;
                if (vie->num_valid == 0) {
                    bql_unlock();
                    rc = 0; /* Reset rc (was set by vm_assist_qmem) so
                             * the while loop continues. */
                    break;
                }

                uint8_t *p = vie->inst;
                int n = vie->num_valid;
                int idx = 0;
                int addr32 = vme.u.inst_emul.cs_d;
                int op32 = vme.u.inst_emul.cs_d;

                /* x86 reg encoding → VM_REG_GUEST_* */
                static const int reg_map[8] = {
                    VM_REG_GUEST_RAX, VM_REG_GUEST_RCX,
                    VM_REG_GUEST_RDX, VM_REG_GUEST_RBX,
                    VM_REG_GUEST_RSP, VM_REG_GUEST_RBP,
                    VM_REG_GUEST_RSI, VM_REG_GUEST_RDI,
                };

                /* Parse prefixes */
                while (idx < n) {
                    uint8_t b = p[idx];
                    if (b == 0x66) { op32 = !op32; idx++; }
                    else if (b == 0x67) { addr32 = !addr32; idx++; }
                    else if (b == 0x26 || b == 0x2e || b == 0x36 ||
                             b == 0x3e || b == 0x64 || b == 0x65 ||
                             b == 0xf0 || b == 0xf2 || b == 0xf3) { idx++; }
                    else if ((b & 0xf0) == 0x40 &&
                             vme.u.inst_emul.paging.cpu_mode == 4) {
                        idx++; /* REX prefix */
                    }
                    else break;
                }

                if (idx >= n) {
                    /* Only prefixes, no opcode — skip all */
                    vm_set_register(qcpu->vcpu, VM_REG_GUEST_RIP,
                                    vme.rip + n);
                    bql_unlock();
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

                switch (opcode) {
                case 0x8a: /* MOV r8, r/m8 — byte read */
                    if (idx >= n) break;
                    reg_field = (p[idx] >> 3) & 7;
                    op_size = 1; is_write = 0; has_modrm = 1;
                    is_high_byte = (reg_field >= 4);
                    if (is_high_byte) reg_field -= 4;
                    break;
                case 0x8b: /* MOV r16/32, r/m16/32 — read */
                    if (idx >= n) break;
                    reg_field = (p[idx] >> 3) & 7;
                    op_size = op32 ? 4 : 2; is_write = 0; has_modrm = 1;
                    break;
                case 0x88: /* MOV r/m8, r8 — byte write */
                    if (idx >= n) break;
                    reg_field = (p[idx] >> 3) & 7;
                    op_size = 1; is_write = 1; has_modrm = 1;
                    is_high_byte = (reg_field >= 4);
                    if (is_high_byte) reg_field -= 4;
                    break;
                case 0x89: /* MOV r/m16/32, r16/32 — write */
                    if (idx >= n) break;
                    reg_field = (p[idx] >> 3) & 7;
                    op_size = op32 ? 4 : 2; is_write = 1; has_modrm = 1;
                    break;
                case 0xa0: /* MOV AL, moffs8 */
                    reg_field = 0; op_size = 1; is_write = 0;
                    imm_size = addr32 ? 4 : 2;
                    break;
                case 0xa1: /* MOV AX/EAX, moffs */
                    reg_field = 0; op_size = op32 ? 4 : 2; is_write = 0;
                    imm_size = addr32 ? 4 : 2;
                    break;
                case 0xa2: /* MOV moffs8, AL */
                    reg_field = 0; op_size = 1; is_write = 1;
                    imm_size = addr32 ? 4 : 2;
                    break;
                case 0xa3: /* MOV moffs, AX/EAX */
                    reg_field = 0; op_size = op32 ? 4 : 2; is_write = 1;
                    imm_size = addr32 ? 4 : 2;
                    break;
                case 0x0f: /* 2-byte opcode */
                    if (idx < n) {
                        uint8_t op2 = p[idx++];
                        if (op2 == 0xb6) {
                            /* MOVZX r16/32, r/m8 — zero-extend byte read */
                            if (idx < n) {
                                reg_field = (p[idx] >> 3) & 7;
                                op_size = 1; is_write = 0; has_modrm = 1;
                            }
                        } else if (op2 == 0xb7) {
                            /* MOVZX r32, r/m16 — zero-extend word read */
                            if (idx < n) {
                                reg_field = (p[idx] >> 3) & 7;
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
                    op_size = op32 ? 4 : 2; is_write = 2;
                    has_modrm = 1; imm_size = op_size;
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
                        if (addr32) {
                            if (rm == 4 && idx < n) { idx++; inst_len = idx; }
                            if (mod == 0 && rm == 5) idx += 4;
                            else if (mod == 1) idx += 1;
                            else if (mod == 2) idx += 4;
                        } else {
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
                    mmio_user_read++;
                    mmio_last_gpa = gpa;
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
                    }
                    vm_set_register(qcpu->vcpu, reg_map[reg_field], regval);
                } else if (is_write == 1 && reg_field >= 0 && op_size > 0) {
                    /* MMIO WRITE: read from guest register, write to device */
                    mmio_user_write++;
                    mmio_last_gpa = gpa;
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
                    mmio_user_write++;
                    mmio_last_gpa = gpa;
                    uint8_t data[8] = {0};
                    if (imm_start + imm_size <= n)
                        memcpy(data, &p[imm_start], imm_size);
                    address_space_rw(&address_space_memory, gpa,
                                     MEMTXATTRS_UNSPECIFIED,
                                     data, op_size, true);
                } else {
                    /* Can't decode — skip */
                    mmio_user_skip++;
                }

                vm_set_register(qcpu->vcpu, VM_REG_GUEST_RIP,
                                vme.rip + inst_len);
                rc = 0;
            }
            bql_unlock();
            break;
        case VM_EXITCODE_RDMSR:
            rc = bhyve_rdmsr(qcpu->vcpu, &vme);
            if (rc) {
                static int msr_rd_err = 0;
                if (msr_rd_err < 5) {
                    fprintf(stderr, "bhyve: rdmsr error, msr=0x%x\n",
                            vme.u.msr.code);
                    msr_rd_err++;
                }
                continue;
            }
            break;
        case VM_EXITCODE_WRMSR:
            rc = bhyve_wrmsr(&vme);
            if (rc) {
                static int msr_wr_err = 0;
                if (msr_wr_err < 5) {
                    fprintf(stderr, "bhyve: wrmsr error, msr=0x%x\n",
                            vme.u.msr.code);
                    msr_wr_err++;
                }
                continue;
            }
            break;
        case VM_EXITCODE_BOGUS:
        case 20: /* VM_EXITCODE_REQIDLE -- scheduler yield, just re-enter */
            exit_bogus++;
            /* Run timers periodically on BOGUS/REQIDLE exits too */
            if ((exit_bogus % 100) == 0) {
                bql_lock();
                qemu_clock_run_timers(QEMU_CLOCK_VIRTUAL);
                {
                    AioContext *ctx = qemu_get_aio_context();
                    timerlistgroup_run_timers(&ctx->tlg);
                    aio_poll(ctx, false);
                }
                bql_unlock();
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
            /*
             * Dump guest IDT entries to debug trap 30.
             * Read IDTR and CR3, do 4-level page walk to find IDT phys addr,
             * then read IDT entries for vectors 30 and 64.
             */
            {
                uint64_t idtr_base = 0, cr3 = 0;
                size_t idtr_base_sz = sizeof(idtr_base);
                size_t cr3_sz = sizeof(cr3);
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_IDTR, &idtr_base);
                vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR3, &cr3);
                fprintf(stderr, "IDT_DUMP: IDTR_BASE=0x%lx CR3=0x%lx\n",
                        (unsigned long)idtr_base, (unsigned long)cr3);

                /* 4-level page walk: translate IDTR virtual addr to physical */
                if (cr3 != 0 && idtr_base != 0) {
                    uint64_t va = idtr_base;
                    uint64_t pml4e, pdpte, pde, pte;
                    uint64_t phys_addr = 0;
                    int walk_ok = 0;

                    /* PML4 entry */
                    uint64_t pml4_idx = (va >> 39) & 0x1FF;
                    cpu_physical_memory_read((cr3 & ~0xFFFULL) + pml4_idx * 8, &pml4e, 8);
                    if (pml4e & 1) {
                        /* PDPT entry */
                        uint64_t pdpt_idx = (va >> 30) & 0x1FF;
                        cpu_physical_memory_read((pml4e & 0x000FFFFFFFFFF000ULL) + pdpt_idx * 8, &pdpte, 8);
                        if (pdpte & 1) {
                            if (pdpte & 0x80) {
                                /* 1GB page */
                                phys_addr = (pdpte & 0x000FFFFFC0000000ULL) | (va & 0x3FFFFFFF);
                                walk_ok = 1;
                            } else {
                                /* PD entry */
                                uint64_t pd_idx = (va >> 21) & 0x1FF;
                                cpu_physical_memory_read((pdpte & 0x000FFFFFFFFFF000ULL) + pd_idx * 8, &pde, 8);
                                if (pde & 1) {
                                    if (pde & 0x80) {
                                        /* 2MB page */
                                        phys_addr = (pde & 0x000FFFFFFFE00000ULL) | (va & 0x1FFFFF);
                                        walk_ok = 1;
                                    } else {
                                        /* PT entry */
                                        uint64_t pt_idx = (va >> 12) & 0x1FF;
                                        cpu_physical_memory_read((pde & 0x000FFFFFFFFFF000ULL) + pt_idx * 8, &pte, 8);
                                        if (pte & 1) {
                                            phys_addr = (pte & 0x000FFFFFFFFFF000ULL) | (va & 0xFFF);
                                            walk_ok = 1;
                                        }
                                    }
                                }
                            }
                        }
                    }

                    if (walk_ok) {
                        fprintf(stderr, "IDT_DUMP: IDTR phys=0x%lx\n", (unsigned long)phys_addr);
                        /* Read IDT entries — each is 16 bytes in long mode */
                        int vecs[] = {0, 8, 13, 14, 30, 64, 0x20, 0x40};
                        for (int vi = 0; vi < 8; vi++) {
                            int vec = vecs[vi];
                            uint8_t idt_entry[16];
                            uint64_t entry_phys = phys_addr + (uint64_t)vec * 16;
                            /* Adjust if crossing page boundary */
                            uint64_t entry_va = idtr_base + (uint64_t)vec * 16;
                            /* Re-walk if on different page than IDTR base */
                            uint64_t use_phys = entry_phys; /* approximation: assume same 2MB/1GB page */
                            if ((entry_va >> 12) != (idtr_base >> 12)) {
                                /* Different page — need another walk, skip for now */
                                use_phys = phys_addr - (idtr_base & 0xFFF) + (entry_va & 0xFFF)
                                           + ((entry_va >> 12) - (idtr_base >> 12)) * 0x1000;
                            }
                            cpu_physical_memory_read(use_phys, idt_entry, 16);
                            uint16_t off_lo = *(uint16_t *)&idt_entry[0];
                            uint16_t seg = *(uint16_t *)&idt_entry[2];
                            uint8_t ist = idt_entry[4] & 0x7;
                            uint8_t type = (idt_entry[5] >> 0) & 0xF;
                            uint8_t dpl = (idt_entry[5] >> 5) & 0x3;
                            uint8_t present = (idt_entry[5] >> 7) & 0x1;
                            uint16_t off_mid = *(uint16_t *)&idt_entry[6];
                            uint32_t off_hi = *(uint32_t *)&idt_entry[8];
                            uint64_t handler = ((uint64_t)off_hi << 32) | ((uint64_t)off_mid << 16) | off_lo;
                            fprintf(stderr, "IDT[%3d]: handler=0x%016lx seg=0x%04x "
                                    "type=%x dpl=%d p=%d ist=%d\n",
                                    vec, (unsigned long)handler, seg, type, dpl, present, ist);
                        }
                    } else {
                        fprintf(stderr, "IDT_DUMP: page walk FAILED\n");
                    }
                }
            }
            rc = -1;
            break;
        }
        case VM_EXITCODE_SVM:
            rc = -1;
            break;
        case VM_EXITCODE_PAUSE:
            exit_pause++;
            /*
             * Guest executed PAUSE — typically in a spin-wait loop.
             * We must periodically run QEMU timers so the PIT can fire
             * IRQ0 (timer interrupt) into the guest. Without this, the
             * guest never receives timer ticks and gets stuck forever
             * in busy-wait loops (e.g., i8042 probing, calibration).
             */
            if ((exit_pause % 10000) == 0) {
                bql_lock();
                qemu_clock_run_timers(QEMU_CLOCK_VIRTUAL);
                {
                    AioContext *ctx = qemu_get_aio_context();
                    timerlistgroup_run_timers(&ctx->tlg);
                    aio_poll(ctx, false);
                }
                bql_unlock();
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

            bql_lock();
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
                     */
                    cpu_interrupt(target_cs, CPU_INTERRUPT_INIT);
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
                     * signal the AP thread (mirrors apic_startup) */
                    target_x86->apic_state->sipi_vector = ipi_vector;
                    cpu_interrupt(target_cs, CPU_INTERRUPT_SIPI);

                    /* Wake QEMU AP thread */
                    target_cs->halted = false;
                    target_cs->stopped = false;
                    tqcpu->dirty = true;
                    break;
                }
                case APIC_DELMODE_FIXED:
                case APIC_DELMODE_LOWPRIO: {
                    /*
                     * Fixed/LowPri IPI: inject the vector into the target's
                     * kernel vLAPIC (sets IRR), then kick the target vCPU
                     * so it re-enters vm_run where the kernel injects it.
                     *
                     * Without vm_lapic_irq(), cpu_interrupt(HARD) only wakes
                     * the target but pre_run clears the flag without injecting
                     * any vector -- the IPI is lost, causing ~30s cross-CPU
                     * stalls (BSP times out waiting for AP acknowledgement).
                     */
                    AccelCPUState *tqcpu = target_cs->accel;
                    vm_lapic_irq(tqcpu->vcpu, ipi_vector);
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
            bql_unlock();
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

            bql_lock();
            CPUState *ap_cs = qemu_get_cpu(ap_idx);
            if (ap_cs && ap_cs->accel) {
                AccelCPUState *ap_qcpu = ap_cs->accel;
                X86CPU *ap_x86 = X86_CPU(ap_cs);

                vm_activate_cpu(ap_qcpu->vcpu);

                /* Set SIPI vector and signal the AP thread */
                ap_x86->apic_state->sipi_vector = (uint8_t)(ap_rip >> 12);
                cpu_interrupt(ap_cs, CPU_INTERRUPT_INIT);
                cpu_interrupt(ap_cs, CPU_INTERRUPT_SIPI);

                ap_cs->halted = false;
                ap_cs->stopped = false;
                ap_qcpu->dirty = true;

                fprintf(stderr, "*** SPINUP_AP[%d]: activating AP%d at RIP=0x%lx\n",
                        cpu->cpu_index, ap_idx, (unsigned long)ap_rip);
            } else {
                fprintf(stderr, "*** SPINUP_AP: no CPUState for AP%d!\n", ap_idx);
            }
            bql_unlock();
            break;
        }
        case VM_EXITCODE_IOAPIC_EOI: {
            /*
             * IOAPIC_EOI: the guest wrote to the LAPIC EOI register for
             * a level-triggered IOAPIC interrupt. The kernel tells us
             * the vector so we can notify QEMU's IOAPIC model to deassert
             * the pin. Without this, level-triggered interrupts (e.g.,
             * ACPI SCI, PCI INTx) never re-trigger.
             */
            int eoi_vector = vme.u.ioapic_eoi.vector;
            bql_lock();
            /* Notify QEMU's IOAPIC that this vector was EOI'd.
             * For now just re-enter — the kernel handles most of it. */
            (void)eoi_vector;
            bql_unlock();
            break;
        }
        default:
            exit_other++;
            printf("Unhandled exit (code=%d). Register Dump...\n", exitcode);
            dump_registers(qcpu->vcpu);
            bql_lock();
            qemu_system_guest_panicked(cpu_get_crash_info(cpu));
            bql_unlock();
            break;
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
         */
        if (cpu->halted) {
            cpu->exception_index = EXCP_HLT;
            ret = EXCP_HLT;
            break;
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
        fprintf(stderr, "EPT_MAP: GPA=0x%lx size=0x%lx prot=%d rom=%d name=%s segid=%d segoff=0x%lx\n",
                (unsigned long)start_pa, (unsigned long)size, prot, rom,
                name ? name : "(null)", segoff.seg.segid, (unsigned long)segoff.offset);
        vm_mmap_memseg(mach->vm, start_pa, segoff.seg.segid, segoff.offset, size, prot);
    } else {
        fprintf(stderr, "EPT_UNMAP: GPA=0x%lx size=0x%lx name=%s\n",
                (unsigned long)start_pa, (unsigned long)size, name ? name : "(null)");
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
    atexit(mmio_print_stats);

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
