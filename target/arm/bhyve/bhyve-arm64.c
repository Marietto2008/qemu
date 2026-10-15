/*
 * QEMU bhyve accelerator — ARM64 backend
 *
 * Copyright 2026 Marietto (FreeBSD arm64 vmm port)
 *
 * VM lifecycle, memory management, vCPU threads, register sync,
 * exit dispatch, PSCI handling for FreeBSD arm64 vmm(4).
 *
 * This file is INDEPENDENT from the x86 bhyve accelerator.
 * The x86 code in accel/bhyve/ is not modified or shared.
 */

#include "qemu/osdep.h"
#include "qemu/accel.h"
#include "accel/accel-ops.h"
#include "accel/accel-cpu-ops.h"
#include "system/cpus.h"
#include "hw/core/boards.h"
#include "qemu/typedefs.h"
#include "system/runstate.h"
#include "system/bhyve.h"
#include "cpu.h"
#include "system/address-spaces.h"
#include "qemu/main-loop.h"
#include "qemu/timer.h"
#include "qemu/error-report.h"
#include "qapi/error.h"
#include "system/memory.h"
#include "system/cpu-timers.h"
#include "qapi/qapi-types-common.h"
#include "qapi/qapi-visit-common.h"
#include "target/arm/cpu.h"
#include "target/arm/internals.h"

#include "bhyve-arm64.h"

#include <signal.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/sched.h>
#include <vmmapi.h>
#include <machine/vmm.h>
#include <machine/vmm_dev.h>

#include "chardev/char.h"
#include "chardev/char-fe.h"
#include "hw/core/irq.h"
#include "hw/core/qdev.h"
#include "system/system.h"
#include "hw/pci/pci.h"
#include "hw/pci/pci_host.h"
#include "hw/pci/pci_bus.h"
#include "standard-headers/linux/pci_regs.h"

/*
 * ARM64-specific vmmapi wrappers.
 *
 * The host x86 libvmmapi.so does not contain these ARM64-only functions.
 * They are trivial ioctl wrappers, so we implement them inline here.
 * On native aarch64, libvmmapi.so already provides them.
 */
#ifndef __aarch64__
static inline int
vm_assert_irq(struct vmctx *ctx, uint32_t irq)
{
    struct vm_irq vi;
    int fd = vm_get_device_fd(ctx);
    bzero(&vi, sizeof(vi));
    vi.irq = irq;
    return (ioctl(fd, VM_ASSERT_IRQ, &vi));
}

static inline int
vm_deassert_irq(struct vmctx *ctx, uint32_t irq)
{
    struct vm_irq vi;
    int fd = vm_get_device_fd(ctx);
    bzero(&vi, sizeof(vi));
    vi.irq = irq;
    return (ioctl(fd, VM_DEASSERT_IRQ, &vi));
}

static inline int
vm_attach_vgic(struct vmctx *ctx, uint64_t dist_start, size_t dist_size,
    uint64_t redist_start, size_t redist_size)
{
    struct vm_vgic_descr vgic;
    int fd = vm_get_device_fd(ctx);
    int error;

    bzero(&vgic, sizeof(vgic));
    error = ioctl(fd, VM_GET_VGIC_VERSION, &vgic.ver);
    if (error)
        return (error);
    vgic.v3_regs.dist_start = dist_start;
    vgic.v3_regs.dist_size = dist_size;
    vgic.v3_regs.redist_start = redist_start;
    vgic.v3_regs.redist_size = redist_size;
    return (ioctl(fd, VM_ATTACH_VGIC, &vgic));
}
#endif /* !__aarch64__ */

/*
 * Debug output control.  Define BHYVE_ARM64_DEBUG=1 for verbose tracing.
 */
#ifndef BHYVE_ARM64_DEBUG
#define BHYVE_ARM64_DEBUG 0
#endif
#define DPRINTF(fmt, ...) \
    do { if (BHYVE_ARM64_DEBUG) fprintf(stderr, "bhyve-arm64: " fmt, \
         ## __VA_ARGS__); } while (0)

/* VM name for /dev/vmm/<name> */
#define VM_NAME "vm0"

/*
 * On arm64, VM_LOWMEM_LIMIT=0 so vm_setup_memory places ALL guest RAM
 * in the highmem region starting at GPA 4GB.  This constant must match
 * the value in lib/libvmmapi/vmmapi.c.
 */
#define VM_HIGHMEM_BASE  (4UL * 1024UL * 1024UL * 1024UL)  /* 0x100000000 */

/* ======================================================================== */
/*  Global state                                                            */
/* ======================================================================== */

static bool bhyve_allowed;

struct bhyve_arm64_machine bhyve_arm64_mach;

/* ======================================================================== */
/*  AccelCPUState — per-vCPU accelerator state                              */
/* ======================================================================== */

struct AccelCPUState {
    struct vcpu *vcpu;
    bool dirty;            /* QEMU registers need pushing to kernel */
    bool powered_on;       /* PSCI power state */
};

/* ======================================================================== */
/*  Public query functions                                                  */
/* ======================================================================== */

int bhyve_enabled(void)
{
    return bhyve_allowed;
}

struct vcpu *bhyve_get_vcpu(CPUState *cpu)
{
    return cpu->accel->vcpu;
}

bool bhyve_apic_in_platform(void)
{
    /* arm64: vGIC is always in-kernel */
    return true;
}

/* ======================================================================== */
/*  Register synchronization — arm64 vmm registers                          */
/* ======================================================================== */

/*
 * Push QEMU's CPUARMState into the kernel via vm_set_register.
 * Only the registers the arm64 vmm API exposes are synced.
 */
static int vmm_set_registers(CPUState *cpu)
{
    CPUARMState *env = cpu_env(cpu);
    struct vcpu *vcpu = cpu->accel->vcpu;
    int ret;

#define SET_REG(vmreg, val) do { \
    ret = vm_set_register(vcpu, (vmreg), (val)); \
    if (ret) DPRINTF("SET %d failed: %d\n", (vmreg), ret); \
} while (0)

    /* General purpose X0-X30 */
    for (int i = 0; i <= 30; i++) {
        SET_REG(VM_REG_GUEST_X0 + i, env->xregs[i]);
    }

    /* SP, PC, CPSR */
    SET_REG(VM_REG_GUEST_SP, env->xregs[31]);  /* SP is xregs[31] in QEMU */
    SET_REG(VM_REG_GUEST_PC, env->pc);
    SET_REG(VM_REG_GUEST_CPSR, pstate_read(env));

    /* EL1 system registers */
    SET_REG(VM_REG_GUEST_SCTLR_EL1, env->cp15.sctlr_el[1]);
    SET_REG(VM_REG_GUEST_TTBR0_EL1, env->cp15.ttbr0_el[1]);
    SET_REG(VM_REG_GUEST_TTBR1_EL1, env->cp15.ttbr1_el[1]);
    SET_REG(VM_REG_GUEST_TCR_EL1, env->cp15.tcr_el[1]);

#undef SET_REG
    return 0;
}

/*
 * Pull kernel register state into QEMU's CPUARMState.
 */
static int vmm_get_registers(CPUState *cpu)
{
    CPUARMState *env = cpu_env(cpu);
    struct vcpu *vcpu = cpu->accel->vcpu;
    uint64_t val;
    int ret;

#define GET_REG(vmreg, dest) do { \
    ret = vm_get_register(vcpu, (vmreg), &val); \
    if (ret == 0) (dest) = val; \
    else DPRINTF("GET %d failed: %d\n", (vmreg), ret); \
} while (0)

    /* General purpose X0-X30 */
    for (int i = 0; i <= 30; i++) {
        GET_REG(VM_REG_GUEST_X0 + i, env->xregs[i]);
    }

    /* SP, PC, CPSR */
    GET_REG(VM_REG_GUEST_SP, env->xregs[31]);
    GET_REG(VM_REG_GUEST_PC, env->pc);

    ret = vm_get_register(vcpu, VM_REG_GUEST_CPSR, &val);
    if (ret == 0) {
        pstate_write(env, val);
    }

    /* EL1 system registers */
    GET_REG(VM_REG_GUEST_SCTLR_EL1, env->cp15.sctlr_el[1]);
    GET_REG(VM_REG_GUEST_TTBR0_EL1, env->cp15.ttbr0_el[1]);
    GET_REG(VM_REG_GUEST_TTBR1_EL1, env->cp15.ttbr1_el[1]);
    GET_REG(VM_REG_GUEST_TCR_EL1, env->cp15.tcr_el[1]);

#undef GET_REG
    return 0;
}

/* ======================================================================== */
/*  PSCI (Power State Coordination Interface) handling                      */
/* ======================================================================== */

/* PSCI function IDs (SMCCC convention) */
#define PSCI_0_2_FN_BASE            0x84000000
#define PSCI_0_2_FN64_BASE          0xC4000000
#define PSCI_VERSION                (PSCI_0_2_FN_BASE + 0)
#define PSCI_CPU_OFF                (PSCI_0_2_FN_BASE + 2)
#define PSCI_CPU_ON_32              (PSCI_0_2_FN_BASE + 3)
#define PSCI_CPU_ON_64              (PSCI_0_2_FN64_BASE + 3)
#define PSCI_AFFINITY_INFO_32       (PSCI_0_2_FN_BASE + 4)
#define PSCI_AFFINITY_INFO_64       (PSCI_0_2_FN64_BASE + 4)
#define PSCI_SYSTEM_OFF             (PSCI_0_2_FN_BASE + 8)
#define PSCI_SYSTEM_RESET           (PSCI_0_2_FN_BASE + 9)
#define PSCI_FEATURES               (PSCI_0_2_FN_BASE + 10)

#define SMCCC_RET_NOT_SUPPORTED     ((uint64_t)-1)
#define SMCCC_RET_SUCCESS           0

/*
 * Find the vCPU matching an MPIDR value.
 * Returns NULL if no match found.
 */
static CPUState *find_cpu_by_mpidr(uint64_t mpidr)
{
    CPUState *cs;
    CPU_FOREACH(cs) {
        ARMCPU *arm_cpu = ARM_CPU(cs);
        if (arm_cpu->mp_affinity == (mpidr & 0xFFFFFF)) {
            return cs;
        }
    }
    return NULL;
}

/*
 * Handle PSCI/SMCCC call from the guest.
 * Returns the PSCI return value to place in X0.
 */
static uint64_t handle_psci(CPUState *cpu, struct vm_exit *vme)
{
    uint64_t func_id = vme->u.smccc_call.func_id;
    uint64_t *args = vme->u.smccc_call.args;

    switch (func_id) {
    case PSCI_VERSION:
        /* Report PSCI 1.0 */
        return (1 << 16) | 0;

    case PSCI_CPU_ON_32:
    case PSCI_CPU_ON_64: {
        uint64_t target_mpidr = args[0];
        uint64_t entry_point = args[1];
        uint64_t context_id = args[2];

        CPUState *target = find_cpu_by_mpidr(target_mpidr);
        if (!target) {
            fprintf(stderr, "bhyve-arm64: PSCI CPU_ON: unknown MPIDR 0x%lx\n",
                    (unsigned long)target_mpidr);
            return (uint64_t)-2;  /* INVALID_PARAMETERS */
        }

        AccelCPUState *target_accel = target->accel;
        if (target_accel->powered_on) {
            return (uint64_t)-4;  /* ALREADY_ON */
        }

        /* Set up target vCPU: PC = entry, X0 = context_id, EL1h, DAIF masked */
        vm_set_register(target_accel->vcpu, VM_REG_GUEST_PC, entry_point);
        vm_set_register(target_accel->vcpu, VM_REG_GUEST_X0, context_id);
        /* PSTATE: EL1h (0x5) with DAIF all masked (0x3c0) */
        vm_set_register(target_accel->vcpu, VM_REG_GUEST_CPSR, 0x3c5);

        /* Clear other GP regs */
        for (int i = 1; i <= 30; i++) {
            vm_set_register(target_accel->vcpu, VM_REG_GUEST_X0 + i, 0);
        }
        vm_set_register(target_accel->vcpu, VM_REG_GUEST_SP, 0);

        target_accel->powered_on = true;
        target->halted = false;
        target->stopped = false;

        /* Kick the target vCPU thread */
        cpu_interrupt(target, CPU_INTERRUPT_HARD);
        qemu_cpu_kick(target);

        DPRINTF("PSCI CPU_ON: mpidr=0x%lx entry=0x%lx ctx=0x%lx\n",
                (unsigned long)target_mpidr, (unsigned long)entry_point,
                (unsigned long)context_id);
        return SMCCC_RET_SUCCESS;
    }

    case PSCI_CPU_OFF:
        cpu->accel->powered_on = false;
        cpu->halted = true;
        cpu->exception_index = EXCP_HLT;
        DPRINTF("PSCI CPU_OFF: vcpu%d\n", cpu->cpu_index);
        return SMCCC_RET_SUCCESS;

    case PSCI_AFFINITY_INFO_32:
    case PSCI_AFFINITY_INFO_64: {
        CPUState *target = find_cpu_by_mpidr(args[0]);
        if (!target) return (uint64_t)-2;
        return target->accel->powered_on ? 0 : 1;  /* ON=0, OFF=1 */
    }

    case PSCI_SYSTEM_OFF:
        qemu_system_shutdown_request(SHUTDOWN_CAUSE_GUEST_SHUTDOWN);
        return SMCCC_RET_SUCCESS;

    case PSCI_SYSTEM_RESET:
        qemu_system_reset_request(SHUTDOWN_CAUSE_GUEST_RESET);
        return SMCCC_RET_SUCCESS;

    case PSCI_FEATURES:
        /* Report support for the requested function */
        switch (args[0]) {
        case PSCI_VERSION:
        case PSCI_CPU_ON_32:
        case PSCI_CPU_ON_64:
        case PSCI_CPU_OFF:
        case PSCI_AFFINITY_INFO_32:
        case PSCI_AFFINITY_INFO_64:
        case PSCI_SYSTEM_OFF:
        case PSCI_SYSTEM_RESET:
        case PSCI_FEATURES:
            return SMCCC_RET_SUCCESS;
        default:
            return SMCCC_RET_NOT_SUPPORTED;
        }

    default:
        DPRINTF("PSCI/SMCCC unknown func_id=0x%lx\n", (unsigned long)func_id);
        return SMCCC_RET_NOT_SUPPORTED;
    }
}

/* ======================================================================== */
/*  Run loop — exit dispatch                                                */
/* ======================================================================== */

static void bhyve_vcpu_pre_run(CPUState *cpu)
{
    /* arm64: no LAPIC/PIC injection needed.
     * The in-kernel vGIC handles all interrupt delivery.
     * Just ensure pending kicks are processed. */
    if (cpu->interrupt_request & CPU_INTERRUPT_HARD) {
        cpu_reset_interrupt(cpu, CPU_INTERRUPT_HARD);
        cpu->halted = false;
    }
}

static void bhyve_vcpu_post_run(CPUState *cpu, struct vm_exit *vme)
{
    CPUARMState *env = cpu_env(cpu);

    /* Always sync PC from the exit — kernel may have advanced it */
    env->pc = vme->pc;
}

/*
 * Main vCPU run function.
 * Handles a single vm_run + exit dispatch iteration.
 */
static int bhyve_vcpu_run(CPUState *cpu)
{
    AccelCPUState *qcpu = cpu->accel;
    struct vm_exit vme;
    struct vm_run vmrun;
    cpuset_t dmask;
    int error;

    vmrun.vm_exit = &vme;
    vmrun.cpuset = &dmask;
    vmrun.cpusetsize = sizeof(dmask);
    static uint64_t bogus_count = 0;

    bql_unlock();
    cpu_exec_start(cpu);

    while (1) {
        if (qcpu->dirty) {
            vmm_set_registers(cpu);
            qcpu->dirty = false;
        }

        bhyve_vcpu_pre_run(cpu);

        { static int vr_dbg=0; if(vr_dbg<5){write(2,"VMRUN\n",6);fprintf(stderr,"VMRUN %d\n",vr_dbg);vr_dbg++;} }
        error = vm_run(qcpu->vcpu, &vmrun);
        if (error) {
            fprintf(stderr, "bhyve-arm64: vm_run failed: %d (%s)\n",
                    errno, strerror(errno));
            break;
        }

        bhyve_vcpu_post_run(cpu, &vme);

        if (vme.exitcode == VM_EXITCODE_BOGUS) {
            bogus_count++;
            if (bogus_count <= 5 || (bogus_count % 100000) == 0) {
                fprintf(stderr, "bhyve-arm64: BOGUS #%lu PC=0x%lx inst_length=%d\n",
                        (unsigned long)bogus_count, (unsigned long)vme.pc,
                        vme.inst_length);
            }
        } else if (vme.exitcode != VM_EXITCODE_INST_EMUL) {
            static uint64_t other_count = 0;
            other_count++;
            if (other_count <= 20) {
                fprintf(stderr, "bhyve-arm64: EXIT-OTHER exitcode=%d PC=0x%lx inst_length=%d\n",
                        vme.exitcode, (unsigned long)vme.pc, vme.inst_length);
            }
        }

        /* Check for pending exit request (kick from another thread) */
        if (qatomic_read(&cpu->exit_request)) {
            qatomic_set(&cpu->exit_request, 0);
            break;
        }

        /* Debug: log all non-BOGUS exits with detail */
        {
            static uint64_t exit_count = 0;
            exit_count++;
            if (vme.exitcode != VM_EXITCODE_BOGUS) {
                static uint64_t non_bogus = 0;
                non_bogus++;
                int is_pci = (vme.exitcode == VM_EXITCODE_INST_EMUL &&
                    vme.u.inst_emul.gpa >= 0x10040000 && vme.u.inst_emul.gpa < 0x10044000) ||
                    (vme.exitcode == VM_EXITCODE_PAGING &&
                    vme.u.paging.gpa >= 0x10040000 && vme.u.paging.gpa < 0x10044000);
                if (non_bogus < 80 || (non_bogus % 100000) == 0 || (is_pci && non_bogus < 200000)) {
                    if (vme.exitcode == VM_EXITCODE_INST_EMUL) {
                        fprintf(stderr, "bhyve-arm64: EXIT #%lu INST_EMUL PC=0x%lx GPA=0x%lx dir=%d reg=%d size=%d\n",
                                (unsigned long)non_bogus,
                                (unsigned long)vme.pc,
                                (unsigned long)vme.u.inst_emul.gpa,
                                vme.u.inst_emul.vie.dir,
                                vme.u.inst_emul.vie.reg,
                                vme.u.inst_emul.vie.access_size);
                    } else if (vme.exitcode == VM_EXITCODE_PAGING) {
                        fprintf(stderr, "bhyve-arm64: EXIT #%lu PAGING PC=0x%lx GPA=0x%lx ESR=0x%lx\n",
                                (unsigned long)non_bogus,
                                (unsigned long)vme.pc,
                                (unsigned long)vme.u.paging.gpa,
                                (unsigned long)vme.u.paging.esr);
                    } else {
                        fprintf(stderr, "bhyve-arm64: EXIT #%lu code=%d PC=0x%lx\n",
                                (unsigned long)non_bogus, vme.exitcode,
                                (unsigned long)vme.pc);
                    }
                }
            }
        }

        switch (vme.exitcode) {
        case VM_EXITCODE_BOGUS:
            /* Spurious exit — re-enter after a brief yield.
             * Kernel handles most BOGUS internally, but some
             * leak to userspace via vcpu_should_yield. */
            usleep(100);
            break;

        case VM_EXITCODE_INST_EMUL: {
            /*
             * MMIO: guest accessed unmapped IPA.
             * Dispatch through QEMU's address_space_rw.
             */
            uint64_t gpa = vme.u.inst_emul.gpa;
            struct vie *vie = &vme.u.inst_emul.vie;
            uint8_t data[16];
            MemTxAttrs attrs = MEMTXATTRS_UNSPECIFIED;

            cpu_exec_end(cpu);
            bql_lock();

            if (vie->dir) {
                /* Write: read register value, write to device */
                uint64_t regval;
                if (vie->reg == 31) {
                    /* XZR: zero register in LDR/STR context */
                    regval = 0;
                } else {
                    vm_get_register(qcpu->vcpu, vie->reg, &regval);
                }
                memcpy(data, &regval, vie->access_size);
                address_space_rw(&address_space_memory, gpa, attrs,
                                 data, vie->access_size, true);
                /* Debug: trace GIC writes */
                if (gpa >= 0x8000000 && gpa < 0x80c0000) {
                    static unsigned long gic_wr;
                    if (gic_wr < 40) {
                        const char *region = (gpa < 0x8010000) ? "GICD" : "GICR";
                        fprintf(stderr, "bhyve-arm64: %s_WR off=0x%lx val=0x%lx size=%d #%lu\n",
                                region, (unsigned long)(gpa - 0x8000000),
                                (unsigned long)regval, vie->access_size, gic_wr);
                    }
                    gic_wr++;
                }
                /* Debug: trace PCI I/O and ECAM writes */
                if (gpa >= 0x3eff0000 && gpa < 0x3f000000) {
                    static unsigned long wr_cnt;
                    if (wr_cnt < 40 || (wr_cnt % 50000) == 0)
                        fprintf(stderr, "bhyve-arm64: MMIO_WR GPA=0x%lx val=0x%lx size=%d #%lu\n",
                                (unsigned long)gpa, (unsigned long)regval,
                                vie->access_size, wr_cnt);
                    wr_cnt++;
                }
                /* Trace ALL ECAM config writes (bus 0) */
                if (gpa >= 0x4010000000UL && gpa < 0x4010100000UL) {
                    static unsigned long ecam_wr;
                    unsigned long ecam_off = gpa - 0x4010000000UL;
                    int edev = (ecam_off >> 15) & 0x1f;
                    int efun = (ecam_off >> 12) & 0x7;
                    int ereg = ecam_off & 0xfff;
                    if (ecam_wr < 200)
                        fprintf(stderr, "bhyve-arm64: ECAM_WR dev=00:%02x.%x "
                                "off=0x%x val=0x%lx size=%d #%lu\n",
                                edev, efun, ereg,
                                (unsigned long)regval,
                                vie->access_size, ecam_wr);
                    ecam_wr++;
                }
            } else {
                /* Read: read from device, write to register */
                address_space_rw(&address_space_memory, gpa, attrs,
                                 data, vie->access_size, false);
                uint64_t regval = 0;
                memcpy(&regval, data, vie->access_size);
                if (vie->sign_extend) {
                    /* Sign-extend based on access size */
                    switch (vie->access_size) {
                    case 1: regval = (int64_t)(int8_t)regval; break;
                    case 2: regval = (int64_t)(int16_t)regval; break;
                    case 4: regval = (int64_t)(int32_t)regval; break;
                    }
                }
                /* Trace ALL ECAM config reads (bus 0) */
                if (gpa >= 0x4010000000UL && gpa < 0x4010100000UL) {
                    static unsigned long ecam_rd;
                    unsigned long ecam_off = gpa - 0x4010000000UL;
                    int edev = (ecam_off >> 15) & 0x1f;
                    int efun = (ecam_off >> 12) & 0x7;
                    int ereg = ecam_off & 0xfff;
                    if (ecam_rd < 200)
                        fprintf(stderr, "bhyve-arm64: ECAM_RD dev=00:%02x.%x "
                                "off=0x%x val=0x%lx size=%d #%lu\n",
                                edev, efun, ereg,
                                (unsigned long)regval,
                                vie->access_size, ecam_rd);
                    ecam_rd++;
                }
                /* Debug: trace GIC reads */
                if (gpa >= 0x8000000 && gpa < 0x80c0000) {
                    static unsigned long gic_rd;
                    if (gic_rd < 40) {
                        MemoryRegionSection mrs;
                        mrs = memory_region_find(
                            address_space_memory.root,
                            gpa, vie->access_size);
                        const char *region = (gpa < 0x8010000) ? "GICD" : "GICR";
                        fprintf(stderr, "bhyve-arm64: %s_RD off=0x%lx val=0x%lx "
                                "size=%d mr=%s #%lu\n",
                                region, (unsigned long)(gpa - 0x8000000),
                                (unsigned long)regval, vie->access_size,
                                mrs.mr ? mrs.mr->name : "(none)", gic_rd);
                    }
                    gic_rd++;
                }
                /* Debug: trace PCI I/O port reads with region info */
                if (gpa >= 0x3eff0000 && gpa < 0x3f000000) {
                    static unsigned long rd_cnt;
                    if (rd_cnt < 40 || (rd_cnt % 50000) == 0) {
                        MemoryRegionSection mrs;
                        mrs = memory_region_find(
                            address_space_memory.root,
                            gpa, vie->access_size);
                        fprintf(stderr, "bhyve-arm64: MMIO_RD GPA=0x%lx "
                                "val=0x%lx size=%d reg=x%d "
                                "mr=%s off=0x%lx #%lu\n",
                                (unsigned long)gpa, (unsigned long)regval,
                                vie->access_size, vie->reg,
                                mrs.mr ? mrs.mr->name : "(none)",
                                (unsigned long)mrs.offset_within_region,
                                rd_cnt);
                        if (mrs.mr)
                            memory_region_unref(mrs.mr);
                    }
                    rd_cnt++;
                }
                if (vie->reg != 31) {
                    vm_set_register(qcpu->vcpu, vie->reg, regval);
                }
                /* reg 31 = XZR: discard read value */
            }


            bql_unlock();
            cpu_exec_start(cpu);

            /*
             * PC advance: kernel does NOT advance PC for INST_EMUL
             * exits on arm64. We must do it here.
             */
            vm_set_register(qcpu->vcpu, VM_REG_GUEST_PC, vme.pc + 4);
            break;
        }

        case VM_EXITCODE_REG_EMUL: {
            /*
             * Trapped system register access (MSR/MRS equivalent).
             * For phase 1: log and RAZ/WI (read-as-zero, write-ignore).
             */
            struct vre *vre = &vme.u.reg_emul.vre;

            if (vre->dir == 0) {
                /* Guest read (MRS) — return zero */
                vm_set_register(qcpu->vcpu, vre->reg, 0);
                fprintf(stderr, "bhyve-arm64: REG_EMUL MRS iss=0x%x -> RAZ (reg=%d) PC=0x%lx\n",
                        vre->inst_syndrome, vre->reg, (unsigned long)vme.pc);
            } else {
                /* Guest write (MSR) — ignore */
                fprintf(stderr, "bhyve-arm64: REG_EMUL MSR iss=0x%x -> WI PC=0x%lx\n",
                        vre->inst_syndrome, (unsigned long)vme.pc);
            }
            /* PC is advanced by kernel for REG_EMUL */
            break;
        }

        case VM_EXITCODE_SMCCC:
        case VM_EXITCODE_HVC: {
            /*
             * PSCI / SMCCC call. Dispatch and write return value to X0.
             */
            cpu_exec_end(cpu);
            bql_lock();

            uint64_t psci_ret = handle_psci(cpu, &vme);
            vm_set_register(qcpu->vcpu, VM_REG_GUEST_X0, psci_ret);

            bql_unlock();
            cpu_exec_start(cpu);

            /* PC is advanced by kernel for SMCCC/HVC */
            break;
        }

        case VM_EXITCODE_WFI:
            /* Guest idle (Wait For Interrupt).
             * Set halted and return to thread loop which will
             * block until an interrupt arrives. */
            cpu_exec_end(cpu);
            bql_lock();
            cpu->halted = true;
            cpu->exception_index = EXCP_HLT;
            bql_unlock();
            goto out;

        case VM_EXITCODE_SUSPENDED: {
            cpu_exec_end(cpu);
            bql_lock();
            enum vm_suspend_how how = vme.u.suspended.how;
            if (how == VM_SUSPEND_POWEROFF) {
                qemu_system_shutdown_request(SHUTDOWN_CAUSE_GUEST_SHUTDOWN);
            } else if (how == VM_SUSPEND_RESET) {
                qemu_system_reset_request(SHUTDOWN_CAUSE_GUEST_RESET);
            }
            cpu->exception_index = EXCP_HLT;
            bql_unlock();
            goto out;
        }

        case VM_EXITCODE_PAGING: {
            /* PAGING should be handled in kernel; reaching here means
             * vm_handle_paging failed. Log but don't halt. */
            static uint64_t paging_count = 0;
            paging_count++;
            if (paging_count <= 20 || (paging_count % 10000) == 0) {
                fprintf(stderr, "bhyve-arm64: PAGING #%lu GPA=0x%lx PC=0x%lx ESR=0x%lx\n",
                    (unsigned long)paging_count,
                    (unsigned long)vme.u.paging.gpa,
                    (unsigned long)vme.pc,
                    (unsigned long)vme.u.paging.esr);
            }
            break;
        }

        case VM_EXITCODE_DEBUG:
            /* Debug exit — gdbstub use. Phase 1: just continue. */
            DPRINTF("DEBUG exit at PC=0x%lx\n", (unsigned long)vme.pc);
            break;

        case VM_EXITCODE_HYP:
            /* Raw exception from EL2 — should not happen normally */
            fprintf(stderr, "bhyve-arm64: HYP exception: ESR=0x%lx "
                    "FAR=0x%lx PC=0x%lx\n",
                    (unsigned long)vme.u.hyp.esr_el2,
                    (unsigned long)vme.u.hyp.far_el2,
                    (unsigned long)vme.pc);
            cpu_exec_end(cpu);
            bql_lock();
            cpu->exception_index = EXCP_HLT;
            bql_unlock();
            goto out;

        default:
            fprintf(stderr, "bhyve-arm64: unhandled exit code %d at PC=0x%lx\n",
                    vme.exitcode, (unsigned long)vme.pc);
            cpu_exec_end(cpu);
            bql_lock();
            cpu->exception_index = EXCP_HLT;
            bql_unlock();
            goto out;
        }
    }

    cpu_exec_end(cpu);
    bql_lock();

out:
    return 0;
}

/* ======================================================================== */
/*  vCPU lifecycle                                                          */
/* ======================================================================== */

static void bhyve_ipi_signal(int sigcpu)
{
    if (current_cpu) {
        vm_suspend_cpu(current_cpu->accel->vcpu);
    }
}

static void bhyve_init_cpu_signals(void)
{
    struct sigaction sigact;
    sigset_t set;

    memset(&sigact, 0, sizeof(sigact));
    sigact.sa_handler = bhyve_ipi_signal;
    sigaction(SIG_IPI, &sigact, NULL);

    sigprocmask(SIG_BLOCK, NULL, &set);
    sigdelset(&set, SIG_IPI);
    pthread_sigmask(SIG_SETMASK, &set, NULL);
}

int bhyve_init_vcpu(CPUState *cpu)
{
    struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;
    AccelCPUState *qcpu;

    qcpu = g_new0(AccelCPUState, 1);
    bhyve_init_cpu_signals();

    qcpu->vcpu = vm_vcpu_open(mach->vm, cpu->cpu_index);
    if (!qcpu->vcpu) {
        fprintf(stderr, "bhyve-arm64: vm_vcpu_open(%d) failed: %s\n",
                cpu->cpu_index, strerror(errno));
        g_free(qcpu);
        return -1;
    }

    /* Activate vCPU in the kernel */
    int err = vm_activate_cpu(qcpu->vcpu);
    if (err) {
        fprintf(stderr, "bhyve-arm64: vm_activate_cpu(%d) failed: %d\n",
                cpu->cpu_index, err);
    }

    /* Request WFI exits so we can properly halt the vCPU */
    err = vm_set_capability(qcpu->vcpu, VM_CAP_HALT_EXIT, 1);
    if (err) {
        fprintf(stderr, "bhyve-arm64: VM_CAP_HALT_EXIT(%d) failed: %d\n",
                cpu->cpu_index, err);
    }
    err = vm_suspend_cpu(qcpu->vcpu);
    if (err) {
        fprintf(stderr, "bhyve-arm64: vm_suspend_cpu(%d) failed: %d\n",
                cpu->cpu_index, err);
    }

    if (cpu->cpu_index == 0) {
        /* BSP: powered on, will run immediately */
        qcpu->powered_on = true;
    } else {
        /* Secondary CPUs: wait for PSCI CPU_ON */
        qcpu->powered_on = false;
        cpu->halted = true;
        cpu->stopped = true;
    }

    qcpu->dirty = true;
    cpu->accel = qcpu;

    return 0;
}

void bhyve_destroy_vcpu(CPUState *cpu)
{
    AccelCPUState *qcpu = cpu->accel;
    if (qcpu) {
        vm_vcpu_close(qcpu->vcpu);
        g_free(qcpu);
        cpu->accel = NULL;
    }
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

        if (cpu->halted) {
            cpu->exception_index = EXCP_HLT;
            ret = EXCP_HLT;
            break;
        }

        { static int exec_dbg=0; if(exec_dbg<5){write(2,"EXEC\n",5);exec_dbg++;} }
        vm_resume_cpu(cpu->accel->vcpu);
        ret = bhyve_vcpu_run(cpu);
        if (ret != 0) {
            break;
        }
    }

    return ret;
}

/* ======================================================================== */
/*  State synchronization                                                   */
/* ======================================================================== */

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

/* ======================================================================== */
/*  Memory management — vm_alloc_memseg / vm_mmap_memseg                    */
/* ======================================================================== */

#define SUPERPAGE_SIZE (1 << 21)

struct bhyve_host_seg {
    int segid;
    size_t size;
    void *seg_start;
    int mmap_flags;
    char *name;
};

#define IN_MEMRANGE(host, range, test) \
    ((test >= host) && (test < (host + range)))

struct bhyve_seg_and_off {
    struct bhyve_host_seg seg;
    size_t offset;
};

static struct bhyve_seg_and_off calc_segoff_from_vmap(GArray *host_vmap,
                                                       void *host_va)
{
    struct bhyve_seg_and_off ret;
    struct bhyve_host_seg seg;

    for (size_t i = 0; i < host_vmap->len; i++) {
        seg = g_array_index(host_vmap, struct bhyve_host_seg, i);
        if (IN_MEMRANGE((char *)seg.seg_start, seg.size, (char *)host_va)) {
            ret.offset = (char *)host_va - (char *)seg.seg_start;
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
    struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;
    struct bhyve_seg_and_off segoff;
    int prot;

    segoff = calc_segoff_from_vmap(mach->host_vmap, host_va);

    if (add) {
        if (segoff.offset == (size_t)-1) {
            /* Segment not found — create on demand */
            int segid = mach->segid_num++;
            char segname[64];
            struct bhyve_host_seg new_seg;

            snprintf(segname, sizeof(segname), "ram.%d", segid);
            fprintf(stderr, "bhyve-arm64: on-demand segment create segid=%d name=%s size=0x%lx\n",
                    segid, segname, (unsigned long)size);

            /* Create kernel memory segment via direct ioctl */
            struct vm_memseg ams;
            memset(&ams, 0, sizeof(ams));
            ams.segid = segid;
            ams.len = size;
            strlcpy(ams.name, segname, sizeof(ams.name));
            int err = ioctl(vm_get_device_fd(mach->vm), VM_ALLOC_MEMSEG, &ams);
            if (err != 0) {
                fprintf(stderr, "bhyve-arm64: vm_alloc_memseg FAILED: %s (errno=%d)\n",
                        strerror(errno), errno);
                return;
            }

            prot = PROT_READ | PROT_EXEC;
            if (!rom) prot |= PROT_WRITE;

            fprintf(stderr, "bhyve-arm64: mmap %s GPA=0x%lx size=0x%lx segid=%d (on-demand)\n",
                    name, (unsigned long)start_pa, (unsigned long)size, segid);
            int ret = vm_mmap_memseg(mach->vm, start_pa, segid, 0, size, prot);
            if (ret != 0) {
                fprintf(stderr, "bhyve-arm64: mmap FAILED ret=%d errno=%d (%s)\n",
                        ret, errno, strerror(errno));
                return;
            }

            /* Overlay host mmap via /dev/vmm.io/vm0.segname */
            {
                char devpath[128];
                snprintf(devpath, sizeof(devpath), "/dev/vmm.io/%s.%s", VM_NAME, segname);
                int fd = open(devpath, O_RDWR);
                if (fd < 0) {
                    fprintf(stderr, "bhyve-arm64: open(%s) FAILED: %s\n",
                            devpath, strerror(errno));
                    return;
                }
                void *mapped = mmap(host_va, size, PROT_READ | PROT_WRITE,
                                     MAP_SHARED | MAP_FIXED, fd, 0);
                close(fd);
                if (mapped == MAP_FAILED) {
                    fprintf(stderr, "bhyve-arm64: host overlay mmap FAILED: %s\n",
                            strerror(errno));
                    return;
                }
                fprintf(stderr, "bhyve-arm64: host overlay mmap OK at %p\n", mapped);
            }

            /* Register in host_vmap */
            new_seg.segid = segid;
            new_seg.size = size;
            new_seg.seg_start = host_va;
            new_seg.mmap_flags = MAP_SHARED | MAP_FIXED;
            new_seg.name = strdup(segname);
            g_array_append_val(mach->host_vmap, new_seg);
            return;
        }

        /* Known segment — just map it */
        prot = PROT_READ | PROT_EXEC;
        if (!rom) {
            prot |= PROT_WRITE;
        }
        fprintf(stderr, "bhyve-arm64: mmap %s GPA=0x%lx size=0x%lx segid=%d\n",
                name, (unsigned long)start_pa, (unsigned long)size,
                segoff.seg.segid);
        int ret = vm_mmap_memseg(mach->vm, start_pa, segoff.seg.segid,
                                  segoff.offset, size, prot);
        if (ret != 0) {
            fprintf(stderr, "bhyve-arm64: mmap FAILED ret=%d errno=%d (%s)\n",
                    ret, errno, strerror(errno));
        }
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

    if (!memory_region_is_ram(mr)) {
        DPRINTF("process_section SKIP (not RAM) name=%s GPA=0x%lx size=0x%lx add=%d\n",
                mr->name, (unsigned long)start_pa, (unsigned long)size, add);
        return;
    }
    fprintf(stderr, "bhyve-arm64: process_section RAM name=%s GPA=0x%lx size=0x%lx add=%d rom=%d\n",
            mr->name, (unsigned long)start_pa, (unsigned long)size, add,
            memory_region_is_rom(mr));

    delta = qemu_real_host_page_size() -
            (start_pa & ~qemu_real_host_page_mask());
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

    bhyve_update_mapping(start_pa, size, (void *)(uintptr_t)host_va, add,
                         memory_region_is_rom(mr), mr->name);
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

static void bhyve_transaction_begin(MemoryListener *listener) {}
static void bhyve_transaction_commit(MemoryListener *listener) {}

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
    .name = "bhyve-arm64",
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

static char *bhyve_serialize_name(const char *input, int segid)
{
    if (!input) return NULL;

    #define MAX_PREFIX 12
    char prefix[MAX_PREFIX + 1];
    size_t len = strlen(input);
    size_t j = 0;

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

    char *output = malloc(16);
    if (!output) return NULL;
    snprintf(output, 16, "%s_%d", prefix, segid);
    return output;
    #undef MAX_PREFIX
}

/*
 * Allocate guest RAM via vm_setup_memory (primary).
 * arm64 guest RAM starts at GPA 0x40000000 (virt machine convention).
 */
static void *bhyve_allocate_memory(size_t mr_size, const char *name, int segid)
{
    struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;
    int err;
    void *ptr;

    fprintf(stderr, "bhyve-arm64: vm_setup_memory size=0x%lx\n", (unsigned long)mr_size);
    err = vm_setup_memory(mach->vm, mr_size, VM_MMAP_ALL);
    fprintf(stderr, "bhyve-arm64: vm_setup_memory returned %d\n", err);
    if (err < 0) {
        fprintf(stderr, "bhyve-arm64: vm_setup_memory failed: %s\n", strerror(errno));
        exit(4);
    }

    /* vm_map_gpa returns the host-writable pointer for a GPA */
    ptr = vm_map_gpa(bhyve_arm64_mach.vm, VM_HIGHMEM_BASE, mr_size);
    fprintf(stderr, "bhyve-arm64: vm_map_gpa(0x%lx, 0x%lx) = %p\n", (unsigned long)VM_HIGHMEM_BASE, (unsigned long)mr_size, ptr);
    if (!ptr) {
        fprintf(stderr, "bhyve-arm64: vm_map_gpa failed (highmem)\n");
        exit(4);
    }

    /* Verify write access */
    volatile char *test = (volatile char *)ptr;
    *test = 0x42;
    fprintf(stderr, "bhyve-arm64: write test OK at %p\n", ptr);

    return ptr;
}

void *bhyve_ram_alloc(size_t mr_size, uint64_t *alignment, int flags,
                      const char *name)
{
    struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;
    struct bhyve_host_seg ram_memseg;

    ram_memseg.mmap_flags = MAP_SHARED | MAP_NORESERVE | MAP_FIXED;
    ram_memseg.segid = mach->segid_num;
    ram_memseg.size = mr_size;
    ram_memseg.name = bhyve_serialize_name(name, ram_memseg.segid);

    fprintf(stderr, "bhyve-arm64: ram_alloc name=%s size=0x%lx segid=%d\n",
            name, (unsigned long)mr_size, ram_memseg.segid);

    fprintf(stderr, "bhyve-arm64: ram_alloc about to allocate for '%s'\n", name);
    if (strcmp(name, "mach-virt.ram") == 0) {
        ram_memseg.seg_start = bhyve_allocate_memory(mr_size,
                                    ram_memseg.name, mach->segid_num++);
    } else {
        fprintf(stderr, "bhyve-arm64: calling vm_create_devmem segid=%d name=%s size=0x%lx\n",
                mach->segid_num, ram_memseg.name, (unsigned long)mr_size);
        ram_memseg.seg_start = vm_create_devmem(mach->vm,
                                    mach->segid_num++,
                                    ram_memseg.name, mr_size);
        fprintf(stderr, "bhyve-arm64: vm_create_devmem returned %p errno=%d\n",
                ram_memseg.seg_start, errno);
    }

    if (!ram_memseg.seg_start ||
        ram_memseg.seg_start == (void *)SIZE_MAX ||
        ram_memseg.seg_start == MAP_FAILED) {
        fprintf(stderr, "bhyve-arm64: could not allocate memory for %s (using fallback mmap)\n",
                name);
        /* Fallback: use anonymous mmap for non-critical regions */
        ram_memseg.seg_start = mmap(NULL, mr_size, PROT_READ | PROT_WRITE,
                                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (ram_memseg.seg_start == MAP_FAILED) {
            fprintf(stderr, "bhyve-arm64: fallback mmap also failed\n");
            exit(4);
        }
        ram_memseg.segid = -1;  /* mark as non-vmm segment */
    }

    *alignment = SUPERPAGE_SIZE;
    g_array_append_val(mach->host_vmap, ram_memseg);
    return ram_memseg.seg_start;
}

/* ======================================================================== */
/*  VM open / close                                                         */
/* ======================================================================== */

static int do_open(const char *vmname, MachineState *ms)
{
    struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;
    int err;

    /* Destroy stale VM with same name */
    if ((mach->vm = vm_open(vmname))) {
        vm_destroy(mach->vm);
        mach->vm = NULL;
    }

    mach->segid_num = 0;
    write(2,"BEFORE_OPENF\n",13);
    mach->vm = vm_openf(vmname, VMMAPI_OPEN_CREATE);
    write(2,"AFTER_OPENF\n",12);
    if (mach->vm == NULL) {
        fprintf(stderr, "bhyve-arm64: vm_openf('%s') failed: %s (errno=%d)\n"
                "  Hint: run as root, or destroy stale VM with: "
                "bhyvectl --vm=%s --destroy\n",
                vmname, strerror(errno), errno, vmname);
        return -1;
    }

    err = vm_set_topology(mach->vm, ms->smp.sockets, ms->smp.cores,
                           ms->smp.threads, 0);
    {char _b[64];int _n=snprintf(_b,64,"TOPO_RET=%d\n",err);write(2,_b,_n);}
    write(2,"AFTER_TOPO\n",11);
    if (err) {
        fprintf(stderr, "bhyve-arm64: vm_set_topology failed: %d\n", err);
    }

    vm_set_memflags(mach->vm, VM_MEM_F_WIRED);
    write(2,"DO_OPEN_DONE\n",13);

    return 0;
}

/* ======================================================================== */
/*  stdin workaround (same glib issue as x86)                               */
/* ======================================================================== */

static QEMUTimer *mainloop_diag_timer;
static Chardev *stdin_chardev = NULL;
static bool stdin_nonblock_set = false;

static void mainloop_diag_cb(void *opaque)
{
    if (!stdin_chardev) {
        stdin_chardev = qemu_chr_find("serial0");
        if (!stdin_chardev)
            stdin_chardev = qemu_chr_find("con0");
        if (!stdin_chardev)
            stdin_chardev = qemu_chr_find("compat_monitor0");
    }

    if (!stdin_nonblock_set) {
        int flags = fcntl(STDIN_FILENO, F_GETFL);
        if (flags >= 0) {
            fcntl(STDIN_FILENO, F_SETFL, flags | O_NONBLOCK);
            stdin_nonblock_set = true;
        }
    }

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

/* ======================================================================== */
/*  CPU "host" model for bhyve                                              */
/* ======================================================================== */

/*
 * Set CPU features for -cpu host.
 * With hardware acceleration, the real CPU executes instructions directly.
 * We set Cortex-A53 compatible features (closest to A55 in QEMU).
 * The kernel VMM handles the actual feature exposure to the guest.
 */
void bhyve_arm_set_cpu_features_from_host(ARMCPU *cpu)
{
    /* Mark as aarch64-capable */
    set_feature(&cpu->env, ARM_FEATURE_V8);
    set_feature(&cpu->env, ARM_FEATURE_NEON);
    set_feature(&cpu->env, ARM_FEATURE_AARCH64);
    set_feature(&cpu->env, ARM_FEATURE_PMU);
    set_feature(&cpu->env, ARM_FEATURE_GENERIC_TIMER);
    set_feature(&cpu->env, ARM_FEATURE_EL2);
    set_feature(&cpu->env, ARM_FEATURE_EL3);

    /* Cortex-A53 MIDR (close to A55) */
    cpu->midr = 0x410fd034;
    cpu->ctr = 0x84448004;
    cpu->reset_sctlr = 0x00c50838;

    cpu->gic_num_lrs = 4;
    cpu->gic_vpribits = 5;
    cpu->gic_vprebits = 5;
    cpu->gic_pribits = 5;

    /* DTB compatible string for device tree generation */
    cpu->dtb_compatible = "arm,cortex-a53";
}

/* ======================================================================== */
/*  GIC IRQ bridge — forward QEMU device IRQs to bhyve kernel vGIC          */
/* ======================================================================== */

/*
 * Bridge handler: called when QEMU device models assert/deassert an IRQ
 * via qemu_set_irq.  Forwards to the bhyve kernel vGIC via vm_assert_irq.
 *
 * The opaque pointer encodes the GIC INTID (SPI number + 32).
 */
static void bhyve_gic_bridge_handler(void *opaque, int n, int level)
{
    uint32_t intid = (uint32_t)(uintptr_t)opaque;
    struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;

    if (!mach->vm) return;

    if (level) {
        vm_assert_irq(mach->vm, intid);
    } else {
        vm_deassert_irq(mach->vm, intid);
    }
}

/* QOM child iterator callback: find a device of type "arm-gicv3" */
static int bhyve_find_gic_cb(Object *obj, void *opaque)
{
    if (object_dynamic_cast(obj, "arm-gicv3")) {
        *(DeviceState **)opaque = DEVICE(obj);
        return 1;  /* stop iteration */
    }
    return 0;
}

static Notifier bhyve_machine_done_notifier;

static void bhyve_machine_done(Notifier *notifier, void *data)
{
    DeviceState *gic_dev = NULL;
    int i, count = 0;

    /* Find the GIC device in the QOM tree */
    object_child_foreach_recursive(object_get_root(),
                                   bhyve_find_gic_cb, &gic_dev);
    if (!gic_dev) {
        fprintf(stderr, "bhyve-arm64: GIC bridge: no arm-gicv3 device found\n");
        return;
    }

    /*
     * Replace GIC SPI GPIO input handlers with our bridge.
     * The virt machine creates 160 SPIs (num_irq=192, SPIs=192-32=160).
     * GPIO input index 'i' corresponds to GIC INTID (i + 32).
     *
     * After this, any qemu_set_irq() on a GIC SPI input will call
     * vm_assert_irq/vm_deassert_irq instead of updating the emulated GIC.
     */
    for (i = 0; i < 160; i++) {
        qemu_irq irq = qdev_get_gpio_in(gic_dev, i);
        if (irq) {
            irq->handler = bhyve_gic_bridge_handler;
            irq->opaque = (void *)(uintptr_t)(i + 32);  /* INTID */
            irq->n = 0;
            count++;
        }
    }

    fprintf(stderr, "bhyve-arm64: GIC bridge: %d SPI handlers replaced "
            "(INTID 32..%d)\n", count, 32 + count - 1);

    /*
     * Firmware-style PCI BAR pre-assignment.
     *
     * Without UEFI firmware, PCI BARs are left at power-on defaults (0).
     * Linux on ARM64 may not reassign them, so MMIO/IO reads hit the wrong
     * address and return 0xff.  Emulate what firmware does: enumerate all
     * PCI devices, assign BARs to valid addresses, and enable I/O+MEM
     * in the command register.
     */
    {
        PCIHostState *pci_host = NULL;
        Object *obj;

        /* Find the PCI host bridge (gpex-pcihost) */
        obj = object_resolve_path_type("", TYPE_PCI_HOST_BRIDGE, NULL);
        if (obj) {
            pci_host = PCI_HOST_BRIDGE(obj);
        }

        if (pci_host && pci_host->bus) {
            PCIBus *bus = pci_host->bus;
            uint32_t io_next = 0x0000;    /* Next available I/O port */
            uint32_t mmio_next = 0x10000000; /* Next available MMIO addr */
            int devfn;

            for (devfn = 0; devfn < PCI_DEVFN_MAX; devfn++) {
                PCIDevice *dev = pci_find_device(bus, 0, devfn);
                uint16_t cmd;
                int bar;

                if (!dev) continue;

                cmd = pci_default_read_config(dev, PCI_COMMAND, 2);

                for (bar = 0; bar < 6; bar++) {
                    uint32_t bar_off = PCI_BASE_ADDRESS_0 + bar * 4;
                    uint32_t bar_val, bar_size, bar_addr;
                    int is_io, is_64bit;

                    /* Read current BAR value */
                    bar_val = pci_default_read_config(dev, bar_off, 4);

                    /* Size the BAR: write all-1s, read back, restore */
                    pci_default_write_config(dev, bar_off, 0xffffffff, 4);
                    bar_size = pci_default_read_config(dev, bar_off, 4);
                    pci_default_write_config(dev, bar_off, bar_val, 4);

                    if (bar_size == 0 || bar_size == 0xffffffff) {
                        continue; /* No BAR here */
                    }

                    is_io = (bar_size & 1);
                    is_64bit = (!is_io && (bar_size & 0x6) == 0x4);

                    if (is_io) {
                        /* I/O BAR */
                        bar_size &= ~0x3;
                        bar_size = (~bar_size) + 1; /* Size = ~mask + 1 */
                        /* Align io_next to bar_size */
                        io_next = (io_next + bar_size - 1) & ~(bar_size - 1);
                        bar_addr = io_next | 0x1; /* Set I/O bit */
                        pci_default_write_config(dev, bar_off, bar_addr, 4);
                        fprintf(stderr, "bhyve-arm64: FW_BAR dev=%02x:%02x.%x "
                                "BAR%d = IO 0x%04x (size=%u)\n",
                                0, PCI_SLOT(devfn), PCI_FUNC(devfn),
                                bar, io_next, bar_size);
                        io_next += bar_size;
                        cmd |= PCI_COMMAND_IO;
                    } else {
                        /* MMIO BAR */
                        bar_size &= ~0xf;
                        bar_size = (~bar_size) + 1;
                        /* Align mmio_next to bar_size */
                        mmio_next = (mmio_next + bar_size - 1) & ~(bar_size - 1);
                        bar_addr = mmio_next;
                        pci_default_write_config(dev, bar_off, bar_addr, 4);
                        if (is_64bit) {
                            pci_default_write_config(dev, bar_off + 4, 0, 4);
                            bar++; /* Skip next BAR (upper 32 bits) */
                        }
                        fprintf(stderr, "bhyve-arm64: FW_BAR dev=%02x:%02x.%x "
                                "BAR%d = MEM 0x%08x (size=%u%s)\n",
                                0, PCI_SLOT(devfn), PCI_FUNC(devfn),
                                bar - (is_64bit ? 1 : 0),
                                mmio_next, bar_size,
                                is_64bit ? " 64bit" : "");
                        mmio_next += bar_size;
                        cmd |= PCI_COMMAND_MEMORY;
                    }
                }

                /* Enable I/O + MEM + bus mastering */
                cmd |= PCI_COMMAND_MASTER;
                pci_default_write_config(dev, PCI_COMMAND, cmd, 2);
                fprintf(stderr, "bhyve-arm64: FW_CMD dev=%02x:%02x.%x cmd=0x%04x\n",
                        0, PCI_SLOT(devfn), PCI_FUNC(devfn), cmd);
            }
        } else {
            fprintf(stderr, "bhyve-arm64: FW_BAR: no PCI host bridge found\n");
        }
    }

    /* Diagnostic: test ECAM reads via address_space_rw */
    {
        MemTxAttrs attrs = MEMTXATTRS_UNSPECIFIED;
        MemTxResult res;
        uint8_t buf[4];
        memset(buf, 0xAA, sizeof(buf));

        /* Read vendor+device ID at ECAM offset 0 */
        res = address_space_rw(&address_space_memory, 0x3f000000,
                               attrs, buf, 4, false);
        fprintf(stderr, "bhyve-arm64: ECAM_DIAG 0x00: res=%d buf=%02x %02x %02x %02x\n",
                res, buf[0], buf[1], buf[2], buf[3]);

        /* Read interrupt pin at ECAM offset 0x3D */
        memset(buf, 0xAA, sizeof(buf));
        res = address_space_rw(&address_space_memory, 0x3f00003d,
                               attrs, buf, 1, false);
        fprintf(stderr, "bhyve-arm64: ECAM_DIAG 0x3D: res=%d buf=%02x (intpin)\n",
                res, buf[0]);

        /* Read class code at ECAM offset 0x08 */
        memset(buf, 0xAA, sizeof(buf));
        res = address_space_rw(&address_space_memory, 0x3f000008,
                               attrs, buf, 4, false);
        fprintf(stderr, "bhyve-arm64: ECAM_DIAG 0x08: res=%d buf=%02x %02x %02x %02x (class)\n",
                res, buf[0], buf[1], buf[2], buf[3]);

        /* Read subsystem vendor at ECAM offset 0x2C */
        memset(buf, 0xAA, sizeof(buf));
        res = address_space_rw(&address_space_memory, 0x3f00002c,
                               attrs, buf, 2, false);
        fprintf(stderr, "bhyve-arm64: ECAM_DIAG 0x2C: res=%d buf=%02x %02x (subvendor)\n",
                res, buf[0], buf[1]);

        /* Scan buses 0-3, all 32 devices each */
        for (int bus = 0; bus < 4; bus++) {
            for (int d = 0; d < 32; d++) {
                hwaddr dev_addr = 0x3f000000 + ((hwaddr)bus << 20) + ((hwaddr)d << 15);
                memset(buf, 0xAA, sizeof(buf));
                res = address_space_rw(&address_space_memory, dev_addr,
                                       attrs, buf, 4, false);
                uint32_t vid_did = buf[0] | (buf[1]<<8) | (buf[2]<<16) | (buf[3]<<24);
                if (vid_did != 0 && vid_did != 0xFFFFFFFF && vid_did != 0xAAAAAAAA) {
                    /* Read more config: interrupt pin, BAR0, class */
                    uint8_t ipin = 0xAA;
                    address_space_rw(&address_space_memory, dev_addr + 0x3d,
                                     attrs, &ipin, 1, false);
                    uint8_t ibar[4], cls[4];
                    address_space_rw(&address_space_memory, dev_addr + 0x10,
                                     attrs, ibar, 4, false);
                    address_space_rw(&address_space_memory, dev_addr + 0x08,
                                     attrs, cls, 4, false);
                    uint32_t bar0 = ibar[0]|(ibar[1]<<8)|(ibar[2]<<16)|(ibar[3]<<24);
                    uint32_t class = cls[0]|(cls[1]<<8)|(cls[2]<<16)|(cls[3]<<24);
                    fprintf(stderr, "bhyve-arm64: ECAM_SCAN bus=%d dev=%d "
                            "vid_did=0x%08x class=0x%08x intpin=%d BAR0=0x%08x\n",
                            bus, d, vid_did, class, ipin, bar0);
                }
            }
        }
    }
}

/* ======================================================================== */
/*  Accelerator init / class / type                                         */
/* ======================================================================== */

static int bhyve_accel_init(AccelState *as, MachineState *ms)
{
    int err;

    /* Unbuffered stderr for crash diagnosis */
    setbuf(stderr, NULL);

    fprintf(stderr, "bhyve-arm64: accelerator initialization\n");

    /* stdin workaround timer */
    mainloop_diag_timer = timer_new_ns(QEMU_CLOCK_REALTIME,
                                        mainloop_diag_cb, NULL);
    timer_mod_ns(mainloop_diag_timer,
                 qemu_clock_get_ns(QEMU_CLOCK_REALTIME) + 1000000000LL);

    err = do_open(VM_NAME, ms);
    if (err) {
        return -1;
    }

    write(2,"BEFORE_MEMINIT\n",15);
    bhyve_memory_init();
    write(2,"AFTER_MEMINIT\n",14);

    /*
     * Attach in-kernel vGIC.  Must match the GPA layout from hw/arm/virt.c:
     *   GICD at 0x08000000 (64KB), GICR at 0x080A0000 (1MB).
     * Without this, GIC MMIO exits to userspace as INST_EMUL and the
     * kernel never receives timer interrupts.
     */
    {
        struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;
        int gic_err = vm_attach_vgic(mach->vm,
            0x08000000, 0x10000,
            0x080A0000, 0x20000);   /* 1 vCPU * 2 * 64KB */
        if (gic_err) {
            fprintf(stderr, "bhyve-arm64: vm_attach_vgic failed: %d (%s)\n",
                    errno, strerror(errno));
        } else {
            fprintf(stderr, "bhyve-arm64: vGIC attached (GICD=0x8000000, GICR=0x80a0000)\n");
        }
    }

    /* Register machine_init_done notifier to bridge GIC IRQs */
    bhyve_machine_done_notifier.notify = bhyve_machine_done;
    qemu_add_machine_init_done_notifier(&bhyve_machine_done_notifier);

    cpu_enable_ticks();

    fprintf(stderr, "bhyve-arm64: accelerator ready (VM '%s')\n", VM_NAME);
    return 0;
}

static void bhyve_set_kernel_irqchip(Object *obj, Visitor *v,
                                     const char *name, void *opaque,
                                     Error **errp)
{
    OnOffSplit mode;
    if (!visit_type_OnOffSplit(v, name, &mode, errp)) {
        return;
    }
    /* arm64: vGIC is always in-kernel, only accept "on" */
    if (mode != ON_OFF_SPLIT_ON) {
        error_setg(errp, "bhyve arm64: kernel-irqchip must be 'on' "
                   "(vGIC is always in-kernel)");
    }
}

static void bhyve_accel_class_init(ObjectClass *oc, const void *data)
{
    AccelClass *ac = ACCEL_CLASS(oc);
    ac->name = "Bhyve";
    ac->init_machine = bhyve_accel_init;
    ac->allowed = &bhyve_allowed;

    object_class_property_add(oc, "kernel-irqchip", "on|off|split",
                              NULL, bhyve_set_kernel_irqchip, NULL, NULL);
    object_class_property_set_description(oc, "kernel-irqchip",
                              "Configure Bhyve in-kernel irqchip");
}

static void bhyve_accel_instance_init(Object *obj)
{
    struct bhyve_arm64_machine *mach = &bhyve_arm64_mach;
    memset(mach, 0, sizeof(*mach));
    mach->host_vmap = g_array_new(FALSE, FALSE, sizeof(struct bhyve_host_seg));
}

static const TypeInfo bhyve_accel_type = {
    .name = ACCEL_CLASS_NAME("bhyve"),
    .parent = TYPE_ACCEL,
    .instance_init = bhyve_accel_instance_init,
    .class_init = bhyve_accel_class_init,
};

static void bhyve_type_init(void)
{
    type_register_static(&bhyve_accel_type);
}

type_init(bhyve_type_init);

/* ======================================================================== */
/*  vCPU thread loop (AccelOpsClass)                                        */
/* ======================================================================== */

static void *qemu_bhyve_cpu_thread_fn(void *arg)
{
    CPUState *cpu = arg;
    int r;

    assert(bhyve_enabled());
    rcu_register_thread();
    bql_lock();

    qemu_thread_get_self(cpu->thread);
    cpu->thread_id = qemu_get_thread_id();
    current_cpu = cpu;

    fprintf(stderr, "bhyve-arm64: vCPU thread started for cpu %d\n", cpu->cpu_index);
    r = bhyve_init_vcpu(cpu);
    if (r < 0) {
        fprintf(stderr, "bhyve-arm64: bhyve_init_vcpu failed: %s\n",
                strerror(-r));
        exit(1);
    }

    cpu_thread_signal_created(cpu);
    qemu_guest_random_seed_thread_part2(cpu->random_seed);

    do {
        bql_unlock();
        sched_yield();
        bql_lock();
        { static int loop_dbg=0; if(loop_dbg<5){write(2,"LOOP\n",5);loop_dbg++;} }

        /* Halt polling for idle vCPUs */
        if (qatomic_read(&cpu->halted) && !cpu->stop
            && cpu_work_list_empty(cpu) && !cpu_has_work(cpu)) {
            int poll_iters = 0;
            while (qatomic_read(&cpu->halted) && !cpu->stop
                   && !qatomic_read(&cpu->exit_request)
                   && !cpu_has_work(cpu)
                   && poll_iters < 200) {
                poll_iters++;
                bql_unlock();
                usleep(1000);
                bql_lock();
            }
            if (poll_iters >= 200 && qatomic_read(&cpu->halted)) {
                qatomic_set(&cpu->halted, 0);
                cpu_interrupt(cpu, CPU_INTERRUPT_HARD);
            }
        }

        qemu_process_cpu_events(cpu);
        if (cpu_can_run(cpu)) {
            r = bhyve_vcpu_exec(cpu);
            if (r == EXCP_DEBUG) {
                cpu_handle_guest_debug(cpu);
            }
        }
    } while (!cpu->unplug || cpu_can_run(cpu));

    bhyve_destroy_vcpu(cpu);
    cpu_thread_signal_destroyed(cpu);
    bql_unlock();
    rcu_unregister_thread();
    return NULL;
}

static void bhyve_start_vcpu_thread(CPUState *cpu)
{
    write(2,"THREAD_CREATE\n",14);
    char thread_name[VCPU_THREAD_NAME_SIZE];
    snprintf(thread_name, VCPU_THREAD_NAME_SIZE, "CPU %d/Bhyve",
             cpu->cpu_index);
    qemu_thread_create(cpu->thread, thread_name, qemu_bhyve_cpu_thread_fn,
                       cpu, QEMU_THREAD_JOINABLE);
}

static void bhyve_kick_vcpu_thread(CPUState *cpu)
{
    cpu->exit_request = 1;
    cpus_kick_thread(cpu);
}

static bool bhyve_cpu_thread_is_idle(CPUState *cpu)
{
    return false;
}

static void bhyve_accel_ops_class_init(ObjectClass *oc, const void *data)
{
    AccelOpsClass *ops = ACCEL_OPS_CLASS(oc);
    ops->create_vcpu_thread = bhyve_start_vcpu_thread;
    ops->kick_vcpu_thread = bhyve_kick_vcpu_thread;
    ops->cpu_thread_is_idle = bhyve_cpu_thread_is_idle;
    ops->handle_interrupt = generic_handle_interrupt;
    ops->synchronize_post_reset = bhyve_cpu_synchronize_post_reset;
    ops->synchronize_post_init = bhyve_cpu_synchronize_post_init;
    ops->synchronize_state = bhyve_cpu_synchronize_state;
    ops->synchronize_pre_loadvm = bhyve_cpu_synchronize_pre_loadvm;
}

static const TypeInfo bhyve_accel_ops_type = {
    .name = ACCEL_OPS_NAME("bhyve"),
    .parent = TYPE_ACCEL_OPS,
    .class_init = bhyve_accel_ops_class_init,
    .abstract = true,
};

static void bhyve_accel_ops_register_types(void)
{
    type_register_static(&bhyve_accel_ops_type);
}

type_init(bhyve_accel_ops_register_types);
