#include "qemu/osdep.h"
#include "hw/isa/i8259_internal.h"
#include "hw/intc/i8259.h"
#include "qemu/module.h"
#include "system/bhyve.h"
#include "hw/core/irq.h"
#include "hw/core/cpu.h"
#include "exec/cpu-interrupt.h"
#include "qom/object.h"
#include "bhyve-internal.h"

#ifndef BHYVE_DEBUG
#define BHYVE_DEBUG 0
#endif
#define BHYVE_DPRINTF(fmt, ...) \
    do { if (BHYVE_DEBUG) fprintf(stderr, fmt, ## __VA_ARGS__); } while (0)

/**
 * BhyvePICClass:
 * @parent_realize: The parent's realizefn.
 */
typedef struct {
    PICCommonClass parent_class;

    DeviceRealize parent_realize;
} BhyvePICClass;

#define TYPE_BHYVE_I8259 "bhyve-i8259"
DECLARE_CLASS_CHECKERS(BhyvePICClass, BHYVE_PIC,
                       TYPE_BHYVE_I8259)


static void bhyve_pic_get(PICCommonState *s)
{
}

static void bhyve_pic_put(PICCommonState *s)
{
}

static void bhyve_pic_reset(DeviceState *dev)
{
    PICCommonState *s = PIC_COMMON(dev);

    s->elcr = 0;
    pic_reset_common(s);

    bhyve_pic_put(s);
}

/*
 * Bitmask of pending ISA IRQs for userspace injection.
 * Set by bhyve_pic_set_irq when level=1, cleared by pre_run
 * after injecting the vector into the vLAPIC.
 */
volatile uint32_t bhyve_pic_pending_irqs = 0;

static void bhyve_pic_set_irq(void *opaque, int irq, int level)
{
    int err;
    pic_stat_update_irq(irq, level);

    /*
     * Map ISA IRQ to IOAPIC pin (IRQ0→pin2, others→same pin#).
     * Pass BOTH vatpic IRQ and vioapic pin so the kernel updates
     * both interrupt controllers. Critical for SCI (IRQ 9): the
     * BHYVE firmware asserts SCI via the kernel's vioapic directly,
     * so we must deassert in the vioapic too, not just vatpic.
     */
    {
        int ioapic_pin = (irq == 0) ? 2 : irq;
        if (level) {
            err = vm_isa_assert_irq(bhyve_mach.vm, irq, ioapic_pin);
            /* Track pending IRQ for userspace injection in pre_run */
            __atomic_or_fetch(&bhyve_pic_pending_irqs, (1u << irq), __ATOMIC_RELEASE);
        } else {
            err = vm_isa_deassert_irq(bhyve_mach.vm, irq, ioapic_pin);
        }
    }

    /*
     * Wake the target vCPU so it picks up the pending IRQ in pre_run.
     * The actual vLAPIC injection happens in pre_run via vm_lapic_msi.
     *
     * Also inject directly via bhyve_inject_lapic_irq (which uses
     * vm_lapic_msi — no vCPU locking) to wake vCPUs sleeping in the
     * kernel HLT handler.  vm_lapic_msi sets the IRR and calls
     * vcpu_notify_event to wake VCPU_SLEEPING vCPUs.
     */
    if (level) {
        int pic_pin = (irq == 0) ? 2 : irq;
        int vec = 0;
        if (pic_pin < 24) {
            vec = bhyve_ioapic_vectors[pic_pin];
        }
        if (vec < 0x10) {
            /* IOAPIC not configured yet — use PIC vector */
            vec = (irq < 8) ? (0x20 + irq) : (0x28 + irq - 8);
        }

        /* Find target CPU from IOAPIC destination cache */
        CPUState *target = first_cpu;
        if (pic_pin < 24) {
            uint8_t dest_id = bhyve_ioapic_destinations[pic_pin];
            if (dest_id != 0xFF) {
                CPUState *cs;
                CPU_FOREACH(cs) {
                    if (cs->cpu_index == dest_id) {
                        target = cs;
                        break;
                    }
                }
            }
        }
        if (target) {
            bhyve_inject_lapic_irq(target, vec);
            cpu_interrupt(target, CPU_INTERRUPT_HARD);
        }
    }

    if (err) {
        BHYVE_DPRINTF("bhyve: 8259 failed, irq (%d) err=%d errno=%d\n",
                      irq, err, errno);
    }
}

static void bhyve_pic_realize(DeviceState *dev, Error **errp)
{
    PICCommonState *s = PIC_COMMON(dev);
    BhyvePICClass *bpc = BHYVE_PIC_GET_CLASS(dev);

    memory_region_init_io(&s->base_io, OBJECT(dev), NULL, NULL, "bhyve-pic", 2);
    memory_region_init_io(&s->elcr_io, OBJECT(dev), NULL, NULL, "bhyve-elcr", 1);

    bpc->parent_realize(dev, errp);
}

qemu_irq *bhyve_i8259_init(ISABus *bus)
{
    i8259_init_chip(TYPE_BHYVE_I8259, bus, true);
    i8259_init_chip(TYPE_BHYVE_I8259, bus, false);

    return qemu_allocate_irqs(bhyve_pic_set_irq, NULL, ISA_NUM_IRQS);
}

static void bhyve_i8259_class_init(ObjectClass *klass, const void *data)
{
    BhyvePICClass *bpc = BHYVE_PIC_CLASS(klass);
    PICCommonClass *k = PIC_COMMON_CLASS(klass);
    DeviceClass *dc = DEVICE_CLASS(klass);

    device_class_set_legacy_reset(dc, bhyve_pic_reset);
    device_class_set_parent_realize(dc, bhyve_pic_realize, &bpc->parent_realize);
    k->pre_save   = bhyve_pic_get;
    k->post_load  = bhyve_pic_put;
}

static const TypeInfo bhyve_i8259_info = {
    .name = TYPE_BHYVE_I8259,
    .parent = TYPE_PIC_COMMON,
    .instance_size = sizeof(PICCommonState),
    .class_init = bhyve_i8259_class_init,
    .class_size = sizeof(BhyvePICClass),
};

static void bhyve_pic_register_types(void)
{
    type_register_static(&bhyve_i8259_info);
}

type_init(bhyve_pic_register_types)
