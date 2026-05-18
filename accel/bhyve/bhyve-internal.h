#ifndef TARGET_I386_BHYVE_INTERNAL_H
#define TARGET_I386_BHYVE_INTERNAL_H

#include <stdbool.h>
#include <glib.h>

#include <vmmapi.h>

/* Forward declaration — CPUState is typedef'd in qemu/typedefs.h */
struct CPUState;

#define SUPERPAGE_SIZE (1 << 21)

#define IN_MEMRANGE(host, range, test) ((test >= host) && (test < (host + range)))

enum host_vendor {
    VENDOR_UNKNOWN,
    VENDOR_INTEL,
    VENDOR_AMD,
};

struct bhyve_host_seg {
    int segid;  // VM Segid
    size_t size;
    void* seg_start;

    int mmap_flags;
    char* name;
};

struct bhyve_machine {
    struct vmctx* vm;

    GArray* host_vmap;
    bool kernel_irqchip_required;

    // Track CPU vendor for MSR support
    enum host_vendor cpu_vendor;

    /* Per-machine segment ID counter value (incremented on every vm_create_devmem)*/
    int segid_num;
};

extern struct bhyve_machine bhyve_mach;

/* Diagnostic counters from bhyve-i8259.c */
extern volatile long pic_irq0_assert;
extern volatile long pic_irq0_deassert;
extern volatile long pic_other_irq;

/* Pending ISA IRQ bitmask for userspace injection (bhyve-i8259.c) */
extern volatile uint32_t bhyve_pic_pending_irqs;

/* Pending IOAPIC IRQ bitmask for userspace injection (bhyve-ioapic.c) */
extern volatile uint32_t bhyve_ioapic_pending_irqs;

/* IOAPIC vector table — set by bhyve_ioapic_set_irq from QEMU's model */
extern volatile uint8_t bhyve_ioapic_vectors[24];

/*
 * Inject an interrupt vector directly into a vCPU's kernel vLAPIC.
 * Used by PIC/IOAPIC set_irq to wake vCPUs sleeping in-kernel HLT.
 * cpu must be a valid CPUState with accel state initialized.
 */
void bhyve_inject_lapic_irq(struct CPUState *cpu, int vector);

#endif /* TARGET_I386_BHYVE_INTERNAL_H */
