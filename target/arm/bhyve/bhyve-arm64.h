/*
 * QEMU bhyve accelerator — ARM64 backend header
 *
 * Copyright 2026 Marietto
 */

#ifndef BHYVE_ARM64_H
#define BHYVE_ARM64_H

#include <stdbool.h>
#include <glib.h>
#include <vmmapi.h>

struct bhyve_arm64_machine {
    struct vmctx *vm;
    GArray *host_vmap;      /* Array of bhyve_host_seg */
    int segid_num;          /* Next segment ID */
};

extern struct bhyve_arm64_machine bhyve_arm64_mach;

/* From bhyve-arm64.c — vCPU lifecycle */
int bhyve_init_vcpu(CPUState *cpu);
void bhyve_destroy_vcpu(CPUState *cpu);
int bhyve_vcpu_exec(CPUState *cpu);

/* State synchronization */
void bhyve_cpu_synchronize_state(CPUState *cpu);
void bhyve_cpu_synchronize_post_reset(CPUState *cpu);
void bhyve_cpu_synchronize_post_init(CPUState *cpu);
void bhyve_cpu_synchronize_pre_loadvm(CPUState *cpu);

#endif /* BHYVE_ARM64_H */
