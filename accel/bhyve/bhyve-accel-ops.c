#include <string.h>
#include <unistd.h>
#include "qemu/osdep.h"
#include "qemu/thread.h"
#include "qemu/timer.h"
#include "qemu/aio.h"
#include "accel/accel-cpu-ops.h"
#include "qemu/main-loop.h"
#include "qemu/guest-random.h"
#include "cpu.h"

#include "system/bhyve.h"
#include "bhyve-accel-ops.h"

static void *qemu_bhyve_cpu_thread_fn(void *arg) {
    CPUState *cpu = arg;
    int r;

    // Verify Bhyve is enabled
    assert(bhyve_enabled());

    // RCU subsystem needs to be aware of all threads that can act as RCU readers
    rcu_register_thread();

    // Acquire Big Qemu Lock
    bql_lock();

    qemu_thread_get_self(cpu->thread);
    // Set the CPUState thread ID to the Posix TID
    cpu->thread_id = qemu_get_thread_id();
    current_cpu = cpu;

    /* TODO: Initialize vCPU */
    r = bhyve_init_vcpu(cpu);
    if (r < 0) {
        fprintf(stderr, "bhyve_init_vcpu failed: %s\n", strerror(-r));
        exit(1);
    }
    /* End Initialize */

    cpu_thread_signal_created(cpu);
    // Deterministic mode seed
    qemu_guest_random_seed_thread_part2(cpu->random_seed);

    /* vCPU Loop — mirrors KVM pattern.
     *
     * qemu_process_cpu_events() is the key: when cpu->halted is true
     * (set by the HLT exit handler), it blocks on cpu->halt_cond
     * while releasing the BQL. This allows the main event loop thread
     * to run QEMU timers (PIT fires → bhyve_pic_set_irq → IRQ0 →
     * cpu_interrupt(CPU_INTERRUPT_HARD) → qemu_cpu_kick → wakes us).
     */
    do {
        /*
         * BQL fairness: briefly release BQL and yield before processing
         * events, so other threads (AP, main loop) can acquire BQL.
         */
        bql_unlock();
        sched_yield();
        bql_lock();

        /*
         * Halted-vCPU wait loop.
         *
         * When halted, release BQL and sleep briefly, then re-check.
         * Timer dispatch and aio completion are handled by the main
         * loop thread (lapic_poll_timer is on main_loop_tlg, so the
         * main loop's poll timeout sees it and wakes up to dispatch).
         *
         * With SMP8, having all 7 APs dispatch timers + aio_poll
         * while holding BQL starved the main loop, preventing DMA
         * completion callbacks from firing (lost ATA interrupts).
         *
         * The wake path: timer/interrupt fires → cpu_interrupt(HARD)
         * → qemu_cpu_kick → exit_request=1 → this loop breaks.
         */
        if (qatomic_read(&cpu->halted) && !cpu->stop
            && cpu_work_list_empty(cpu) && !cpu_has_work(cpu)) {
            int poll_iters = 0;

            while (qatomic_read(&cpu->halted) && !cpu->stop
                   && !qatomic_read(&cpu->exit_request)
                   && !cpu_has_work(cpu)
                   && poll_iters < 200 /* max 200ms in halt poll */) {
                poll_iters++;
                bql_unlock();
                usleep(1000);
                bql_lock();
            }
            /*
             * If we hit the max iteration limit, force unhalt.
             * The guest may need a timer interrupt (PIT/LAPIC)
             * that was consumed by another vCPU thread or never
             * armed.  Force re-entry to vm_run so the kernel can
             * check for pending interrupts.
             */
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
    /* End vCPU Loop */


    bhyve_destroy_vcpu(cpu);
    cpu_thread_signal_destroyed(cpu);
    bql_unlock();
    rcu_unregister_thread();
    return NULL;
}

// Dummy implementations for demonstration
static void bhyve_start_vcpu_thread(CPUState *cpu) {
    char thread_name[VCPU_THREAD_NAME_SIZE];

    snprintf(thread_name, VCPU_THREAD_NAME_SIZE, "CPU %d/Bhyve",
             cpu->cpu_index);

    qemu_thread_create(cpu->thread, thread_name, qemu_bhyve_cpu_thread_fn,
                       cpu, QEMU_THREAD_JOINABLE);
}

static void bhyve_kick_vcpu_thread(CPUState *cpu) {
    cpu->exit_request = 1;
    cpus_kick_thread(cpu);
}

/*
 * Bhyve cpu_thread_is_idle: always returns false.
 *
 * This prevents qemu_process_cpu_events from blocking on halt_cond
 * via qemu_cond_wait.  Bhyve's halt handling is done in the thread
 * loop's halt polling loop instead, which dispatches timers while
 * waiting.  Without this, halted vCPUs sleep in qemu_cond_wait
 * forever because lapic_poll_timer is on the AioContext timer list,
 * not main_loop_tlg, so the main loop doesn't wake up to fire it.
 */
static bool bhyve_cpu_thread_is_idle(CPUState *cpu)
{
    return false;
}


static void bhyve_accel_ops_class_init(ObjectClass *oc, const void *data)
{
    AccelOpsClass *ops = ACCEL_OPS_CLASS(oc);

    // VCPU Thread Management
    ops->create_vcpu_thread = bhyve_start_vcpu_thread;
    ops->kick_vcpu_thread = bhyve_kick_vcpu_thread;
    ops->cpu_thread_is_idle = bhyve_cpu_thread_is_idle;
    ops->handle_interrupt = generic_handle_interrupt;

    // CPU State Synchronization
    ops->synchronize_post_reset = bhyve_cpu_synchronize_post_reset;
    ops->synchronize_post_init = bhyve_cpu_synchronize_post_init;
    ops->synchronize_state = bhyve_cpu_synchronize_state;
    ops->synchronize_pre_loadvm = bhyve_cpu_synchronize_pre_loadvm;
}

static const TypeInfo bhyve_accel_ops_type = {
    .name = ACCEL_OPS_NAME("bhyve"), // Changed to "bhyve"

    .parent = TYPE_ACCEL_OPS,
    .class_init = bhyve_accel_ops_class_init,
    .abstract = true,
};

static void bhyve_accel_ops_register_types(void)
{
    type_register_static(&bhyve_accel_ops_type);
}

type_init(bhyve_accel_ops_register_types);
