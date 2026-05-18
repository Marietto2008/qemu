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
#include "strings.h"
#include "qapi/qapi-types-common.h"
#include "qapi/qapi-visit-common.h"

#include "bhyve-accel-ops.h"
#include "bhyve-internal.h"
#include "hw/i386/apic_internal.h"

#include <signal.h>
#include <unistd.h>
#include <errno.h>

#include <machine/specialreg.h>
#include <string.h>
#include <vmmapi.h>

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
    fflush(stderr);
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
};

/* -------------------------------------------------------------------------- */

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

/* Debug version: logs which register fails */
static void vmm_set_registers_debug(CPUState *cpu) {
    CPUX86State *env = cpu_env(cpu);
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu* vcpu = qcpu->vcpu;
    int ret;
#define TRY_SET(name, reg, val) do { \
    ret = vm_set_register(vcpu, (reg), (val)); \
    if (ret != 0) fprintf(stderr, "  SET_REG FAIL: %s = 0x%lx err=%d errno=%d\n", \
                          name, (unsigned long)(val), ret, errno); \
} while(0)
    TRY_SET("RAX", VM_REG_GUEST_RAX, env->regs[R_EAX]);
    TRY_SET("RIP", VM_REG_GUEST_RIP, env->eip);
    TRY_SET("RFLAGS", VM_REG_GUEST_RFLAGS, env->eflags);
    TRY_SET("CR0", VM_REG_GUEST_CR0, env->cr[0]);
    TRY_SET("CR3", VM_REG_GUEST_CR3, env->cr[3]);
    TRY_SET("CR4", VM_REG_GUEST_CR4, env->cr[4]);
    TRY_SET("EFER", VM_REG_GUEST_EFER, env->efer);
    TRY_SET("DR7", VM_REG_GUEST_DR7, env->dr[7]);
    fprintf(stderr, "  vmm_set_registers_debug: eip=0x%lx cr0=0x%lx cr4=0x%lx efer=0x%lx eflags=0x%lx\n",
            (unsigned long)env->eip, (unsigned long)env->cr[0],
            (unsigned long)env->cr[4], (unsigned long)env->efer,
            (unsigned long)env->eflags);
    /* Try segments */
    {
        struct { int reg; int qemu_idx; const char *name; } segs[] = {
            { VM_REG_GUEST_CS, R_CS, "CS" },
            { VM_REG_GUEST_DS, R_DS, "DS" },
            { VM_REG_GUEST_SS, R_SS, "SS" },
        };
        for (int i = 0; i < 3; i++) {
            ret = vm_set_register(vcpu, segs[i].reg, env->segs[segs[i].qemu_idx].selector);
            if (ret != 0) fprintf(stderr, "  SET_REG FAIL: %s selector err=%d\n", segs[i].name, ret);
            /* Try setting desc */
            uint32_t _f = env->segs[segs[i].qemu_idx].flags;
            uint32_t _lo = (_f >> 8) & 0xFF;
            uint32_t _l  = (_f >> 21) & 1;
            uint32_t _db = (_f >> 22) & 1;
            uint32_t _g  = (_f >> 23) & 1;
            uint32_t _ar = _lo | (_l << 13) | (_db << 14) | (_g << 15);
            if (!(_ar & 0x80)) _ar |= (1 << 16);
            ret = vm_set_desc(vcpu, segs[i].reg,
                              env->segs[segs[i].qemu_idx].base,
                              env->segs[segs[i].qemu_idx].limit, _ar);
            if (ret != 0) fprintf(stderr, "  SET_DESC FAIL: %s base=0x%lx limit=0x%x ar=0x%x flags=0x%x err=%d errno=%d\n",
                                  segs[i].name, (unsigned long)env->segs[segs[i].qemu_idx].base,
                                  (unsigned)env->segs[segs[i].qemu_idx].limit, _ar, _f, ret, errno);
        }
    }
#undef TRY_SET
}

static int vmm_set_registers(CPUState *cpu) {
    CPUX86State *env = cpu_env(cpu);
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu* vcpu = qcpu->vcpu;

    /* GPRs */
    int ret;
    static int set_reg_debug = 1; /* enable for first failure */

    int any_fail = 0;
#define VM_SET_REG_CHECK(name, reg, val) do { \
    ret = vm_set_register(vcpu, (reg), (val)); \
    if (ret != 0) { \
        if (set_reg_debug) { \
            fprintf(stderr, "vmm_set_registers: FAIL at %s reg=%d val=0x%lx err=%d errno=%d\n", \
                    name, (reg), (unsigned long)(val), ret, errno); \
        } \
        any_fail = ret; \
    } \
} while(0)

#define VM_SET_DESC_CHECK(name, reg, base, limit, ar) do { \
    ret = vm_set_desc(vcpu, (reg), (base), (limit), (ar)); \
    if (ret != 0) { \
        if (set_reg_debug) { \
            fprintf(stderr, "vmm_set_desc: FAIL at %s base=0x%lx limit=0x%x ar=0x%x err=%d errno=%d\n", \
                    name, (unsigned long)(base), (unsigned)(limit), (unsigned)(ar), ret, errno); \
        } \
        any_fail = ret; \
    } \
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
    if (any_fail && set_reg_debug) {
        set_reg_debug = 0; /* only log once */
    }
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
    ret = address_space_rw(&address_space_io, io->port, attrs, io->data,
        io->size, !io->in);
    if (ret != MEMTX_OK) {
        error_report("Bhyve: I/O Transaction Failed "
            "[%s, port=%u, size=%zu]", (io->in ? "in" : "out"),
            io->port, io->size);
    }

    /* Log IDE I/O after kernel takes over (skip first 5000 total IOs = SeaBIOS) */
    {
        static long io_count = 0;
        static int ide_log = 0;
        uint16_t port = io->port;
        io_count++;
        if (io_count > 5000 && ide_log < 100) {
            if ((port >= 0x1f0 && port <= 0x1f7) ||
                (port >= 0x170 && port <= 0x177) ||
                port == 0x3f6 || port == 0x376) {
                fprintf(stderr, "IDE[%ld]: %s port=0x%04x size=%zu data=0x",
                        io_count, io->in ? "IN " : "OUT", port, io->size);
                for (int j = (int)io->size - 1; j >= 0; j--)
                    fprintf(stderr, "%02x", io->data[j]);
                fprintf(stderr, "\n");
                ide_log++;
            }
        }
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
    int ret;

    bql_lock();

    /* Suppressed PRE_RUN noise */

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
        printf("Hung here\n");
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
         * bhyve's kernel vatpic/vioapic do NOT auto-inject into
         * the vLAPIC — vmx_inject_interrupts doesn't pick them up.
         * We must inject from userspace via vm_lapic_irq().
         *
         * Read the pending IRQ bitmask (set by bhyve_pic_set_irq),
         * find the highest-priority pending IRQ (lowest number),
         * and look up the correct vector from the kernel's IOAPIC
         * redirection table. The IOAPIC vector is what the guest
         * expects (e.g., 0x30 for timer, not PIC's 0x20).
         */
        uint32_t pending = __atomic_exchange_n(
            &bhyve_pic_pending_irqs, 0, __ATOMIC_ACQ_REL);
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

            /* Fall back to PIC vector if IOAPIC not yet configured */
            if (vector == 0) {
                vector = (irq < 8) ? (0x20 + irq) : (0x28 + irq - 8);
            }

            int irq_err = vm_lapic_irq(vcpu, vector);

            {
                static int inj_log = 0;
                if (inj_log < 50) {
                    fprintf(stderr, "IRQ_INJ[%d]: irq=%d pin=%d vec=0x%x err=%d irq0=%ld\n",
                            inj_log, irq, pin, vector, irq_err,
                            pic_irq0_assert);
                    inj_log++;
                }
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

                if (vector >= 0x10) {
                    int err = vm_lapic_irq(vcpu, vector);
                    {
                        static int ioapic_inj_log = 0;
                        if (ioapic_inj_log < 30) {
                            fprintf(stderr, "IOAPIC_INJ[%d]: pin=%d vec=0x%x err=%d\n",
                                    ioapic_inj_log, pin, vector, err);
                            ioapic_inj_log++;
                        }
                    }
                } else {
                    /* Vector not yet programmed — re-queue */
                    __atomic_or_fetch(&bhyve_ioapic_pending_irqs,
                                      (1u << pin), __ATOMIC_RELEASE);
                }
            }
        }
    }

    if (sync_tpr) {
        ret = vm_set_register(vcpu, VM_REG_GUEST_TPR, qcpu->tpr);
    }

    bql_unlock();
}

static void bhyve_vcpu_post_run(CPUState *cpu) {
    CPUX86State *env = cpu_env(cpu);
    X86CPU *x86_cpu = X86_CPU(cpu);
    AccelCPUState *qcpu = cpu->accel;
    struct vcpu *vcpu = qcpu->vcpu;
    uint64_t val;
    int ret;

    // Set Eflags
    ret = vm_get_register(vcpu, VM_REG_GUEST_RFLAGS, &env->eflags);

    // TPR
    ret = vm_get_register(vcpu, VM_REG_GUEST_TPR, &val);
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
        fprintf(stderr, "INIT[%d]: processing, irq_req=0x%x apic=%p\n",
                cpu->cpu_index, cpu->interrupt_request,
                (void *)x86_cpu->apic_state);
        bhyve_cpu_synchronize_state(cpu);
        do_cpu_init(x86_cpu);
        qcpu->wait_for_sipi = true;  /* Accept next SIPI, reject duplicates */
        fprintf(stderr, "INIT[%d]: after do_cpu_init, wait_for_sipi=%d bsp=%d apicbase=0x%lx\n",
                cpu->cpu_index,
                x86_cpu->apic_state ? x86_cpu->apic_state->wait_for_sipi : -1,
                x86_cpu->apic_state ? cpu_is_bsp(x86_cpu) : -1,
                x86_cpu->apic_state ? (unsigned long)cpu_get_apic_base(x86_cpu->apic_state) : 0);
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
                fprintf(stderr, "INIT[%d]: APIC ID field[2] BEFORE reset: 0x%08x (expected cpu_index=%d → 0x%08x)\n",
                        cpu->cpu_index,
                        lapic_state.fields[2].data,
                        cpu->cpu_index,
                        (uint32_t)(cpu->cpu_index << 24));

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

                fprintf(stderr, "INIT[%d]: APIC ID field[2] AFTER fix: 0x%08x\n",
                        cpu->cpu_index, lapic_state.fields[2].data);

                lapic_err = vm_lapic_set_state(qcpu->vcpu, &lapic_state);
                fprintf(stderr, "INIT[%d]: kernel vLAPIC reset: %s\n",
                        cpu->cpu_index,
                        lapic_err == 0 ? "OK" : "FAILED");
            } else {
                fprintf(stderr, "INIT[%d]: vm_lapic_get_state failed: %d\n",
                        cpu->cpu_index, lapic_err);
            }
        }

        fprintf(stderr, "INIT[%d]: after vmm_set_registers, wait_for_sipi=%d irq_req=0x%x\n",
                cpu->cpu_index,
                x86_cpu->apic_state ? x86_cpu->apic_state->wait_for_sipi : -1,
                cpu->interrupt_request);
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
            fprintf(stderr, "SIPI[%d]: IGNORED (AP already running, not in wait-for-SIPI state)\n",
                    cpu->cpu_index);
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
            fprintf(stderr, "SIPI[%d]: direct, vec=%d eip=0x%lx cs_base=0x%lx cs_sel=0x%x dirty=true halted=false\n",
                    cpu->cpu_index, sipi_vec,
                    (unsigned long)env->eip,
                    (unsigned long)env->segs[R_CS].base,
                    (unsigned)env->segs[R_CS].selector);

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
            /* Log AP's first entry registers from kernel VMCS */
            if (cpu->cpu_index > 0) {
                static int ap_entry_log = 0;
                if (ap_entry_log < 2) {
                    uint64_t rip_k, cs_sel_k;
                    uint64_t cs_base_k;
                    uint32_t cs_limit_k, cs_ar_k;
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RIP, &rip_k);
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_CS, &cs_sel_k);
                    vm_get_desc(qcpu->vcpu, VM_REG_GUEST_CS, &cs_base_k, &cs_limit_k, &cs_ar_k);
                    fprintf(stderr, "AP[%d] VMCS after set_registers: RIP=0x%lx CS=0x%lx base=0x%lx limit=0x%x ar=0x%x\n",
                            cpu->cpu_index, (unsigned long)rip_k, (unsigned long)cs_sel_k,
                            (unsigned long)cs_base_k, cs_limit_k, cs_ar_k);
                    /* Also log CR0 to verify real mode */
                    uint64_t cr0_k;
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR0, &cr0_k);
                    fprintf(stderr, "AP[%d] VMCS: CR0=0x%lx\n", cpu->cpu_index, (unsigned long)cr0_k);
                    /* Dump guest physical memory via BOTH QEMU address_space and bhyve mmap */
                    {
                        hwaddr phys_addr = cs_base_k + rip_k;
                        uint8_t code[64];
                        MemTxResult mtr = address_space_read(
                            &address_space_memory, phys_addr,
                            MEMTXATTRS_UNSPECIFIED, code, sizeof(code));
                        if (mtr == MEMTX_OK) {
                            fprintf(stderr, "AP[%d] QEMU address_space at 0x%lx:", cpu->cpu_index, (unsigned long)phys_addr);
                            for (int ci = 0; ci < 32; ci++) {
                                if (ci % 16 == 0) fprintf(stderr, "\n  %04x:", ci);
                                fprintf(stderr, " %02x", code[ci]);
                            }
                            fprintf(stderr, "\n");
                        }
                        /* Also read from bhyve's mmap'd guest memory */
                        {
                            char *baseaddr;
                            struct bhyve_machine *mach_tmp = get_bhyve_mach();
                            if (vm_get_guestmem_from_ctx(mach_tmp->vm, &baseaddr, NULL, NULL) == 0) {
                                uint8_t *bhyve_mem = (uint8_t *)(baseaddr + phys_addr);
                                fprintf(stderr, "AP[%d] BHYVE mmap at 0x%lx:", cpu->cpu_index, (unsigned long)phys_addr);
                                for (int ci = 0; ci < 32; ci++) {
                                    if (ci % 16 == 0) fprintf(stderr, "\n  %04x:", ci);
                                    fprintf(stderr, " %02x", bhyve_mem[ci]);
                                }
                                fprintf(stderr, "\n");
                            }
                        }
                    }
                    ap_entry_log++;
                }
            }
        }

        bhyve_vcpu_pre_run(cpu);

        smp_rmb();
        {
            static int pre_run_debug = 0; /* set to 1 for VMX register dump */
            if (pre_run_debug) {
                uint64_t val;
                int terr;
                fprintf(stderr, "\n=== DRY-RUN: Full VMX register dump before vm_run ===\n");

                /* GPRs */
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_RIP, &val);
                fprintf(stderr, "  RIP=0x%016lx (get=%d)\n", (unsigned long)val, terr);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_RFLAGS, &val);
                fprintf(stderr, "  RFLAGS=0x%016lx (get=%d)\n", (unsigned long)val, terr);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_RAX, &val);
                fprintf(stderr, "  RAX=0x%016lx\n", (unsigned long)val);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_RBX, &val);
                fprintf(stderr, "  RBX=0x%016lx\n", (unsigned long)val);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_RCX, &val);
                fprintf(stderr, "  RCX=0x%016lx\n", (unsigned long)val);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_RDX, &val);
                fprintf(stderr, "  RDX=0x%016lx\n", (unsigned long)val);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_RSP, &val);
                fprintf(stderr, "  RSP=0x%016lx\n", (unsigned long)val);

                /* Segment selectors + descriptors (base, limit, access) via vm_get_desc */
                fprintf(stderr, "  --- Segment Registers (from VMCS via vm_get_desc) ---\n");
                {
                    int seg_regs[] = { VM_REG_GUEST_CS, VM_REG_GUEST_DS, VM_REG_GUEST_ES,
                                       VM_REG_GUEST_SS, VM_REG_GUEST_FS, VM_REG_GUEST_GS,
                                       VM_REG_GUEST_TR, VM_REG_GUEST_LDTR };
                    const char *seg_names[] = { "CS", "DS", "ES", "SS", "FS", "GS", "TR", "LDTR" };
                    for (int i = 0; i < 8; i++) {
                        uint64_t sel_v = 0, base_v = 0;
                        uint32_t lim_v = 0, acc_v = 0;
                        vm_get_register(qcpu->vcpu, seg_regs[i], &sel_v);
                        vm_get_desc(qcpu->vcpu, seg_regs[i], &base_v, &lim_v, &acc_v);
                        fprintf(stderr, "  %4s: sel=0x%04lx base=0x%016lx limit=0x%08x access=0x%08x\n",
                                seg_names[i], (unsigned long)sel_v, (unsigned long)base_v, lim_v, acc_v);
                    }
                }

                /* GDTR / IDTR */
                uint64_t gdtr_base = 0, idtr_base = 0;
                uint32_t gdtr_limit = 0, idtr_limit = 0, dummy_acc = 0;
                vm_get_desc(qcpu->vcpu, VM_REG_GUEST_GDTR, &gdtr_base, &gdtr_limit, &dummy_acc);
                vm_get_desc(qcpu->vcpu, VM_REG_GUEST_IDTR, &idtr_base, &idtr_limit, &dummy_acc);
                fprintf(stderr, "  GDTR: base=0x%016lx limit=0x%04x\n", (unsigned long)gdtr_base, gdtr_limit);
                fprintf(stderr, "  IDTR: base=0x%016lx limit=0x%04x\n", (unsigned long)idtr_base, idtr_limit);

                /* Control registers */
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR0, &val);
                fprintf(stderr, "  CR0=0x%016lx (get=%d)\n", (unsigned long)val, terr);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR3, &val);
                fprintf(stderr, "  CR3=0x%016lx\n", (unsigned long)val);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR4, &val);
                fprintf(stderr, "  CR4=0x%016lx\n", (unsigned long)val);
                terr = vm_get_register(qcpu->vcpu, VM_REG_GUEST_EFER, &val);
                fprintf(stderr, "  EFER=0x%016lx\n", (unsigned long)val);

                fprintf(stderr, "=== LIVE RUN: vm_run enabled with iteration limit ===\n");
                fflush(stderr);
                pre_run_debug = 0;
            }
        }

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

		error = vm_run(qcpu->vcpu, &vmrun);
		{
		    static int vmrun_log = 0;
		    static long port402_count = 0;
		    if (error == 0) {
		        int interesting = 0;
		        if (vme.exitcode == VM_EXITCODE_INOUT && vme.u.inout.port == 0x402) {
		            port402_count++;
		            /* Log port 0x402 summary every 100K */
		            if ((port402_count % 100000) == 0) {
		                fprintf(stderr, "vm_run[%d] #%ld: port 0x402 count=%ld\n",
		                        cpu->cpu_index, vm_run_total, port402_count);
		                fflush(stderr);
		            }
		        } else if (vme.exitcode == VM_EXITCODE_INOUT) {
		            if (vmrun_log < 200) {
		                fprintf(stderr, "vm_run[%d] #%ld: INOUT port=0x%x %s rip=0x%lx\n",
		                        cpu->cpu_index, vm_run_total,
		                        vme.u.inout.port,
		                        vme.u.inout.in ? "IN" : "OUT",
		                        (unsigned long)vme.rip);
		                fflush(stderr);
		                vmrun_log++;
		            }
		        } else if (vmrun_log < 200) {
		            /* Log non-INOUT, non-port402 exits (limited) */
		            fprintf(stderr, "vm_run[%d] #%ld: exit=%d rip=0x%lx\n",
		                    cpu->cpu_index, vm_run_total, vme.exitcode,
		                    (unsigned long)vme.rip);
		            fflush(stderr);
		            vmrun_log++;
		        }
		    }
		}
		vm_run_total++;
		if ((vm_run_total % 1000000) == 0) {
		    mmio_print_stats();
		}

        /* Per-CPU periodic stats (every 5 seconds wall clock) */
        {
            static __thread long cpu_runs = 0;
            static __thread long cpu_hlt = 0;
            static __thread long cpu_inst_emul = 0;
            static __thread long cpu_inout = 0;
            static __thread int64_t last_report_ms = 0;
            cpu_runs++;
            if (error == 0) {
                if (vme.exitcode == VM_EXITCODE_HLT) cpu_hlt++;
                else if (vme.exitcode == VM_EXITCODE_INST_EMUL) cpu_inst_emul++;
                else if (vme.exitcode == VM_EXITCODE_INOUT ||
                         vme.exitcode == VM_EXITCODE_INOUT_STR) cpu_inout++;
            }
            int64_t now_ms = qemu_clock_get_ms(QEMU_CLOCK_REALTIME);
            if (last_report_ms == 0) last_report_ms = now_ms;
            if (now_ms - last_report_ms >= 5000) {
                fprintf(stderr, "CPU_STATS[%d] t=%lds: runs=%ld hlt=%ld inst_emul=%ld inout=%ld\n",
                        cpu->cpu_index,
                        (long)((now_ms - last_report_ms) / 1000),
                        cpu_runs, cpu_hlt, cpu_inst_emul, cpu_inout);
                fflush(stderr);
                cpu_runs = cpu_hlt = cpu_inst_emul = cpu_inout = 0;
                last_report_ms = now_ms;
            }
        }

        if (error != 0) {
            static int vm_run_err_log = 0;
            if (vm_run_err_log < 5) {
                fprintf(stderr, "Error running vm: %s (errno=%d, error=%d)\n",
                        strerror(errno), errno, error);
                fflush(stderr);
                vm_run_err_log++;
            }
            rc = 1;
            break;
        }

        bhyve_vcpu_post_run(cpu);

		exitcode = vme.exitcode;

        /* Minimal exit logging - only HLT exits for now */

        switch (exitcode) {
        case VM_EXITCODE_HLT:
            exit_hlt++;
            {
                static int hlt_log = 0;

                /*
                 * Precise LAPIC timer wakeup for HLT exits.
                 *
                 * 1. Read kernel vLAPIC state
                 * 2. If IRR has pending bits → skip halt, re-enter immediately
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
                    /* Interrupt already pending — re-enter VM immediately.
                     * The kernel will inject it on the next VMX entry. */
                    if (hlt_log < 20) {
                        fprintf(stderr, "HLT[%d]: IRR pending, skip halt → re-enter\n",
                                cpu->cpu_index);
                        fflush(stderr);
                        hlt_log++;
                    }
                    /* Don't set halted — just continue the vm_run loop */
                    break;
                }

                /* No pending interrupt. Compute LAPIC timer deadline. */
                if (hlt_log < 20) {
                    fprintf(stderr, "HLT[%d]: cpu=%d rip=0x%lx, computing timer deadline\n",
                            hlt_log, cpu->cpu_index, (unsigned long)vme.rip);
                    fflush(stderr);
                    hlt_log++;
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

                        /*
                         * Time until next LAPIC timer fire:
                         *   CCR * divisor / VLAPIC_BUS_FREQ  (seconds)
                         * Convert to nanoseconds:
                         *   CCR * divisor * 1e9 / (128 * 1024 * 1024)
                         */
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

                        static int deadline_log = 0;
                        if (deadline_log < 20) {
                            fprintf(stderr, "HLT[%d]: LAPIC timer: ccr=%u icr=%u dcr=0x%x div=%u → %ld ns\n",
                                    cpu->cpu_index, ccr, icr, dcr, divisor,
                                    (long)deadline_ns);
                            fflush(stderr);
                            deadline_log++;
                        }
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
            /* Clear debug state so next vm_run doesn't exit immediately */
            vm_resume_cpu(qcpu->vcpu);
            if (exit_debug <= 5) {
                fprintf(stderr, "DEBUG EXIT #%ld: rip=0x%lx (resume_rc=%d)\n",
                        exit_debug, (unsigned long)vme.rip,
                        vm_resume_cpu(qcpu->vcpu));
            }
            break;
        case VM_EXITCODE_INOUT:
        case VM_EXITCODE_INOUT_STR:
            exit_inout++;
            /*
             * Acquire BQL for I/O emulation — device models (serial, PIC,
             * etc.) expect it when modifying state and raising interrupts.
             * This mirrors KVM's pattern of locking BQL for exit handling.
             */
            bql_lock();
            rc = vm_assist_qio(qcpu->vcpu, vmm_io_callback, &vme);
            bql_unlock();
            break;
        case VM_EXITCODE_INST_EMUL:
            bql_lock();
            {
                static uint64_t inst_emul_total = 0;
                static uint64_t inst_emul_lapic = 0;
                static uint64_t inst_emul_ioapic = 0;
                static uint64_t inst_emul_hpet = 0;
                static uint64_t inst_emul_other = 0;
                static int inst_emul_log = 0;
                uint64_t gpa_pre = vme.u.inst_emul.gpa;

                inst_emul_total++;
                if (gpa_pre >= 0xFEE00000ULL && gpa_pre < 0xFEF00000ULL)
                    inst_emul_lapic++;
                else if (gpa_pre >= 0xFEC00000ULL && gpa_pre < 0xFED00000ULL)
                    inst_emul_ioapic++;
                else if (gpa_pre >= 0xFED00000ULL && gpa_pre < 0xFEE00000ULL)
                    inst_emul_hpet++;
                else
                    inst_emul_other++;

                /* Log first 50 individual accesses */
                if (inst_emul_log < 50) {
                    fprintf(stderr, "INST_EMUL[%d]: gpa=0x%lx rip=0x%lx inst[0..3]=%02x %02x %02x %02x\n",
                            cpu->cpu_index, (unsigned long)gpa_pre,
                            (unsigned long)vme.rip,
                            vme.u.inst_emul.vie.inst[0],
                            vme.u.inst_emul.vie.inst[1],
                            vme.u.inst_emul.vie.inst[2],
                            vme.u.inst_emul.vie.inst[3]);
                    fflush(stderr);
                    inst_emul_log++;
                }
                /* Periodic summary every 10000 exits */
                if ((inst_emul_total % 10000) == 0) {
                    fprintf(stderr, "INST_EMUL STATS: total=%lu lapic=%lu ioapic=%lu hpet=%lu other=%lu\n",
                            (unsigned long)inst_emul_total,
                            (unsigned long)inst_emul_lapic,
                            (unsigned long)inst_emul_ioapic,
                            (unsigned long)inst_emul_hpet,
                            (unsigned long)inst_emul_other);
                    fflush(stderr);
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
                static int mmio_emul_log = 0;

                if (vie->num_valid == 0) {
                    if (mmio_emul_log < 10) {
                        fprintf(stderr, "MMIO EMUL[%d]: no instruction bytes at "
                                "gpa=0x%lx rip=0x%lx (skipping)\n",
                                cpu->cpu_index,
                                (unsigned long)gpa, (unsigned long)vme.rip);
                        mmio_emul_log++;
                    }
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

                    if (mmio_emul_log < 5) {
                        fprintf(stderr, "MMIO READ: gpa=0x%lx size=%d "
                                "val=0x%lx → reg%d (inst_len=%d)\n",
                                (unsigned long)gpa, op_size,
                                (unsigned long)(op_size == 1 ? data[0] :
                                 op_size == 2 ? *(uint16_t*)data :
                                 *(uint32_t*)data),
                                reg_field, inst_len);
                        mmio_emul_log++;
                    }
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

                    if (mmio_emul_log < 50) {
                        fprintf(stderr, "MMIO WRITE: gpa=0x%lx size=%d "
                                "val=0x%lx from reg%d\n",
                                (unsigned long)gpa, op_size,
                                (unsigned long)(op_size == 1 ? data[0] :
                                 op_size == 2 ? *(uint16_t*)data :
                                 *(uint32_t*)data),
                                reg_field);
                        mmio_emul_log++;
                    }
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

                    if (mmio_emul_log < 10) {
                        fprintf(stderr, "MMIO WRITE IMM: gpa=0x%lx size=%d "
                                "val=0x%lx\n",
                                (unsigned long)gpa, op_size,
                                (unsigned long)(op_size == 1 ? data[0] :
                                 op_size == 2 ? *(uint16_t*)data :
                                 *(uint32_t*)data));
                        mmio_emul_log++;
                    }
                } else {
                    /* Can't decode — log and skip (old behavior) */
                    mmio_user_skip++;
                    if (mmio_emul_log < 20) {
                        fprintf(stderr, "MMIO SKIP: gpa=0x%lx rip=0x%lx "
                                "opcode=0x%02x inst:",
                                (unsigned long)gpa, (unsigned long)vme.rip,
                                opcode);
                        for (int j = 0; j < vie->num_valid && j < 15; j++)
                            fprintf(stderr, " %02x", vie->inst[j]);
                        fprintf(stderr, "\n");
                        fflush(stderr);
                        mmio_emul_log++;
                    }
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
                printf("Error Reading to MSR...\n");
                continue;
            }
            break;
        case VM_EXITCODE_WRMSR:
            rc = bhyve_wrmsr(&vme);
            if (rc) {
                printf("Error Writing to MSR...\n");
                continue;
            }
            break;
        case VM_EXITCODE_BOGUS:
        case 20: /* VM_EXITCODE_REQIDLE — scheduler yield, just re-enter */
            exit_bogus++;
            /* AP diagnostic: log RFLAGS and code at stuck RIP */
            if (cpu->cpu_index > 0) {
                static int ap_bogus_log = 0;
                if (ap_bogus_log < 3) {
                    uint64_t ap_rflags = 0, ap_rip_k = 0, ap_cr3 = 0, ap_rsp = 0, ap_rdx = 0, ap_rax = 0;
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RFLAGS, &ap_rflags);
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RIP, &ap_rip_k);
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_CR3, &ap_cr3);
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RSP, &ap_rsp);
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RDX, &ap_rdx);
                    vm_get_register(qcpu->vcpu, VM_REG_GUEST_RAX, &ap_rax);
                    fprintf(stderr, "AP_BOGUS[%d] #%d: rip=0x%lx rflags=0x%lx IF=%d cr3=0x%lx rsp=0x%lx rdx=0x%lx rax=0x%lx\n",
                            cpu->cpu_index, ap_bogus_log,
                            (unsigned long)ap_rip_k, (unsigned long)ap_rflags,
                            (int)((ap_rflags >> 9) & 1),
                            (unsigned long)ap_cr3, (unsigned long)ap_rsp,
                            (unsigned long)ap_rdx, (unsigned long)ap_rax);
                    /* Try to read code at physical address (for kernel with nokaslr:
                     * virt 0xffffffff81XXXXXX → phys 0x01XXXXXX) */
                    if (ap_rip_k >= 0xffffffff81000000ULL && ap_rip_k < 0xffffffff82000000ULL) {
                        uint64_t phys = (ap_rip_k - 0xffffffff80000000ULL) - 16; /* dump 16 bytes before RIP */
                        char *baseaddr;
                        struct bhyve_machine *mach_tmp = get_bhyve_mach();
                        size_t low_sz, high_sz;
                        if (vm_get_guestmem_from_ctx(mach_tmp->vm, &baseaddr, &low_sz, &high_sz) == 0 && phys < low_sz) {
                            uint8_t *code = (uint8_t *)(baseaddr + phys);
                            fprintf(stderr, "AP[%d] code at phys 0x%lx (rip-16):", cpu->cpu_index, (unsigned long)phys);
                            for (int ci = 0; ci < 48; ci++) {
                                if (ci % 16 == 0) fprintf(stderr, "\n  %04x:", ci);
                                fprintf(stderr, " %02x", code[ci]);
                            }
                            fprintf(stderr, "\n");
                        }
                    }
                    fflush(stderr);
                    ap_bogus_log++;
                }
            }
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
            /* BSP: periodically read the AP's cpuhp state from guest memory */
            if (cpu->cpu_index == 0) {
                static int bsp_cpuhp_log = 0;
                if (bsp_cpuhp_log < 10) {
                    /* AP's ap_sync_state at phys 0x3bc213d8 */
                    char *baseaddr;
                    struct bhyve_machine *mach_tmp = get_bhyve_mach();
                    size_t low_sz, high_sz;
                    if (vm_get_guestmem_from_ctx(mach_tmp->vm, &baseaddr, &low_sz, &high_sz) == 0) {
                        uint32_t *ap_state = (uint32_t *)(baseaddr + 0x3bc213d8ULL);
                        if (0x3bc213d8ULL < low_sz) {
                            fprintf(stderr, "BSP_CPUHP_CHECK: phys 0x3bc213d8 = %d (AP wants 4)\n",
                                    *ap_state);
                            fflush(stderr);
                        }
                    }
                    bsp_cpuhp_log++;
                }
            }
            break;
        case VM_EXITCODE_SUSPENDED:
            how = vme.u.suspended.how;

            switch (how) {
            case VM_SUSPEND_RESET:
                exit(0);
            case VM_SUSPEND_POWEROFF:
                qemu_system_reset_request(SHUTDOWN_CAUSE_GUEST_RESET);
                cpu->exception_index = EXCP_INTERRUPT;
                vm_destroy(mach->vm);
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
            static int ipi_log = 0;

            if (ipi_log < 20) {
                fprintf(stderr, "IPI: mode=0x%x vec=%d dmask targets:",
                        ipi_mode, ipi_vector);
            }

            bql_lock();
            CPU_FOREACH_ISSET(target_cpu, &dmask) {
                CPUState *target_cs = qemu_get_cpu(target_cpu);
                if (!target_cs) {
                    if (ipi_log < 20)
                        fprintf(stderr, " [%d:MISSING]", target_cpu);
                    continue;
                }
                if (ipi_log < 20)
                    fprintf(stderr, " %d", target_cpu);

                switch (ipi_mode) {
                case APIC_DELMODE_INIT:
                    /*
                     * INIT: let QEMU handle via do_cpu_init which
                     * resets the APIC and sets wait_for_sipi=1.
                     * The kernel already called vm_await_start().
                     */
                    cpu_interrupt(target_cs, CPU_INTERRUPT_INIT);
                    if (ipi_log < 20)
                        fprintf(stderr, "(INIT)");
                    break;
                case APIC_DELMODE_STARTUP: {
                    /*
                     * SIPI: activate AP in kernel, then use QEMU's
                     * standard SIPI path. QEMU handles everything:
                     * do_cpu_init (cpu_reset + apic_init_reset) +
                     * do_cpu_sipi (cpu_x86_load_seg_cache_sipi).
                     *
                     * DO NOT call vcpu_reset — let QEMU's cpu_reset
                     * set the definitive state, then vmm_set_registers
                     * syncs it to the kernel VMCS.
                     */
                    AccelCPUState *tqcpu = target_cs->accel;
                    X86CPU *target_x86 = X86_CPU(target_cs);
                    int aerr;

                    /* Activate AP in kernel (idempotent) */
                    aerr = vm_activate_cpu(tqcpu->vcpu);
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

                    if (ipi_log < 20)
                        fprintf(stderr, "(SIPI:act=%d,vec=%d)",
                                aerr, ipi_vector);
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
                     * any vector — the IPI is lost, causing ~30s cross-CPU
                     * stalls (BSP times out waiting for AP acknowledgement).
                     */
                    AccelCPUState *tqcpu = target_cs->accel;
                    int ipi_err = vm_lapic_irq(tqcpu->vcpu, ipi_vector);
                    if (ipi_log < 20)
                        fprintf(stderr, "(FIXED:vec=%d,err=%d)", ipi_vector, ipi_err);
                    cpu_interrupt(target_cs, CPU_INTERRUPT_HARD);
                    break;
                }
                case APIC_DELMODE_NMI:
                    cpu_interrupt(target_cs, CPU_INTERRUPT_NMI);
                    break;
                default:
                    if (ipi_log < 20)
                        fprintf(stderr, "(unhandled mode 0x%x)", ipi_mode);
                    break;
                }
            }
            bql_unlock();

            if (ipi_log < 20) {
                fprintf(stderr, "\n");
                fflush(stderr);
                ipi_log++;
            }
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
    fprintf(stderr, "vcpu_open: cpu_index=%d vcpu=%p\n", cpu->cpu_index, (void*)qcpu->vcpu);

    err = vm_get_capability(qcpu->vcpu, VM_CAP_HALT_EXIT, &tmp);
    if (err < 0) {
		fprintf(stderr, "Could not get capability halt exit (%d)\n", err);
    }
    err = vm_set_capability(qcpu->vcpu, VM_CAP_HALT_EXIT, 1);
    fprintf(stderr, "set HALT_EXIT: %d\n", err);

    err = vm_set_capability(qcpu->vcpu, VM_CAP_PAUSE_EXIT, 0);
    fprintf(stderr, "set PAUSE_EXIT(disabled): %d\n", err);

    err = vm_set_x2apic_state(qcpu->vcpu, X2APIC_DISABLED);
    fprintf(stderr, "set x2apic: %d\n", err);

	err = vm_set_capability(qcpu->vcpu, VM_CAP_ENABLE_INVPCID, 1);
    fprintf(stderr, "set INVPCID: %d\n", err);

	err = vm_set_capability(qcpu->vcpu, VM_CAP_IPI_EXIT, 1);
    fprintf(stderr, "set IPI_EXIT: %d\n", err);

    // Start vCPU
    if (cpu->cpu_index == 0) { // BSP
        // Can run in real mode
        err = vm_set_capability(qcpu->vcpu,
            VM_CAP_UNRESTRICTED_GUEST, 1);
        fprintf(stderr, "set UNRESTRICTED_GUEST: %d\n", err);

        err = vcpu_reset(qcpu->vcpu);
        fprintf(stderr, "vcpu_reset: %d\n", err);
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
                uint32_t old_svr = lapic_state.fields[0xf].data;
                lapic_state.fields[0xf].data &= ~0x100; /* clear APIC_SVR_ENABLE */
                lapic_err = vm_lapic_set_state(qcpu->vcpu, &lapic_state);
                fprintf(stderr, "SVR disable: old=0x%x new=0x%x set_err=%d\n",
                        old_svr, lapic_state.fields[0xf].data, lapic_err);
            } else {
                fprintf(stderr, "SVR disable: get_state failed err=%d\n",
                        lapic_err);
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
        fprintf(stderr, "AP cpu_index=%d: halted, will activate on SIPI\n",
                cpu->cpu_index);
    }

    {
        /* Activate+suspend ALL vCPUs (BSP and APs).
         * Activate makes the vCPU visible in vm_active_cpus(),
         * which is needed for:
         *  - BSP: normal operation
         *  - APs: so vlapic_calcdest() includes them in IPI targets
         * Suspend sets debug_cpus so vm_resume_cpu works on first vm_run.
         */
        err = vm_activate_cpu(qcpu->vcpu);
        fprintf(stderr, "vm_activate_cpu[%d]: %d\n", cpu->cpu_index, err);
        err = vm_suspend_cpu(qcpu->vcpu);
        fprintf(stderr, "vm_suspend_cpu[%d]: %d\n", cpu->cpu_index, err);
    }

    // Sync registers on exec
    qcpu->dirty = true;
    cpu->accel = qcpu;


    return 0; // Return success
}

void bhyve_destroy_vcpu(CPUState *cpu) {
    struct bhyve_machine* mach = get_bhyve_mach();

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
    static int resume_debug = 2;  /* per-CPU debug */
    static int exec_enter_log = 0;

    if (exec_enter_log < 4) {
        fprintf(stderr, "bhyve_vcpu_exec[%d]: enter exception_index=%d halted=%d stopped=%d\n",
                cpu->cpu_index, cpu->exception_index, cpu->halted, cpu->stopped);
        fflush(stderr);
        exec_enter_log++;
    }

    while (1) {
        if (cpu->exception_index >= EXCP_INTERRUPT) {
            ret = cpu->exception_index;
            cpu->exception_index = -1;
            break;
        }

        ret = vm_resume_cpu(cpu->accel->vcpu);
        if (resume_debug > 0) {
            fprintf(stderr, "vm_resume_cpu[%d]: %d (errno=%d)\n",
                    cpu->cpu_index, ret, errno);
            fflush(stderr);
            resume_debug--;
        }
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
    int prot, ret;
    segoff = calc_segoff_from_vmap(mach->host_vmap, host_va);

    if (add) {
        prot = PROT_READ | PROT_EXEC;
        if (!rom) {
            prot |= PROT_WRITE;
        }
        ret = vm_mmap_memseg(mach->vm, start_pa, segoff.seg.segid, segoff.offset, size, prot);
    } else {
        ret = vm_munmap_memseg(mach->vm, start_pa, size);
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
        fprintf(stderr, "  vm_create_devmem(segid=%d, name='%s', size=%zu)\n",
                mach->segid_num, ram_memseg.name, mr_size);
        ram_memseg.seg_start = vm_create_devmem(mach->vm, mach->segid_num++, ram_memseg.name, mr_size);
        if (!ram_memseg.seg_start || ram_memseg.seg_start == (void*)SIZE_MAX) {
            fprintf(stderr, "  vm_create_devmem FAILED: errno=%d (%s)\n", errno, strerror(errno));
        }
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
    static long tick = 0;
    tick++;

    /* Lazy lookup of the chardev — try common names */
    if (!stdin_chardev) {
        stdin_chardev = qemu_chr_find("con0");      /* virtio-console */
        if (!stdin_chardev)
            stdin_chardev = qemu_chr_find("serial0"); /* -serial stdio */
        if (!stdin_chardev)
            stdin_chardev = qemu_chr_find("compat_monitor0");
        if (stdin_chardev && tick <= 3) {
            fprintf(stderr, "STDIN_POLL: found chardev '%s'\n",
                    stdin_chardev->label ? stdin_chardev->label : "?");
            fflush(stderr);
        }
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
            static long chars_injected = 0;
            chars_injected += n;
            if (chars_injected <= 20) {
                fprintf(stderr, "STDIN_POLL: injected %d bytes (total=%ld) first=0x%02x '%c'\n",
                        n, chars_injected, buf[0],
                        (buf[0] >= 0x20 && buf[0] < 0x7f) ? buf[0] : '.');
                fflush(stderr);
            }
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
