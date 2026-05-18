
#include "qemu/osdep.h"
#include "../../hw/intc/ioapic_internal.h"
#include "system/bhyve.h"
#include "hw/core/cpu.h"
#include "exec/cpu-interrupt.h"
#include "bhyve-internal.h"

typedef struct BhyveIOAPICState BhyveIOAPICState;

struct BhyveIOAPICState {
    IOAPICCommonState ioapic;
};

static void bhyve_ioapic_get(IOAPICCommonState *s)
{
}

static void bhyve_ioapic_put(IOAPICCommonState *s)
{
}

static void bhyve_ioapic_reset(DeviceState *dev)
{
    IOAPICCommonState *s = IOAPIC_COMMON(dev);

    ioapic_reset_common(dev);
    bhyve_ioapic_put(s);
}

static volatile long ioapic_irq_count = 0;

/*
 * Bitmask of pending IOAPIC IRQs for userspace injection.
 * Set by bhyve_ioapic_set_irq when level=1, cleared by pre_run
 * after injecting the vector into the vLAPIC.
 *
 * Bits 0-23 correspond to IOAPIC pins (not ISA IRQ numbers).
 * Pin mapping: IRQ0→pin2, all others→same pin number.
 */
volatile uint32_t bhyve_ioapic_pending_irqs = 0;

/* Vector table: stores the IOAPIC RTE vector for each pin.
 * Read from QEMU's own IOAPIC model (not the kernel's). */
volatile uint8_t bhyve_ioapic_vectors[24] = {0};

static void bhyve_ioapic_set_irq(void *opaque, int irq, int level)
{
    BhyveIOAPICState *s = opaque;
    IOAPICCommonState *common = IOAPIC_COMMON(s);
    int err;
    int pin = (irq == 0) ? 2 : irq;

    ioapic_stat_update_irq(common, irq, level);

    if (level) {
        err = vm_ioapic_assert_irq(bhyve_mach.vm, pin);
        /*
         * Read vector from QEMU's IOAPIC model redirection table.
         * This is the vector the guest programmed — the kernel's vioapic
         * doesn't have this info since QEMU handles the IOAPIC MMIO.
         */
        if (pin < 24) {
            uint64_t rte = common->ioredtbl[pin];
            uint8_t vec = rte & 0xFF;
            int masked = (rte >> 16) & 1;
            if (!masked && vec >= 0x10) {
                bhyve_ioapic_vectors[pin] = vec;
            }
        }
        /* Track pending IOAPIC pin for userspace injection in pre_run */
        __atomic_or_fetch(&bhyve_ioapic_pending_irqs, (1u << pin), __ATOMIC_RELEASE);
    } else {
        err = vm_ioapic_deassert_irq(bhyve_mach.vm, pin);
    }

    /* Log first few IOAPIC IRQ assertions */
    if (level && ioapic_irq_count < 20) {
        fprintf(stderr, "IOAPIC: IRQ%d→pin%d %s (#%ld) err=%d\n",
                irq, pin, level ? "assert" : "deassert",
                ++ioapic_irq_count, err);
        fflush(stderr);
    } else if (level) {
        ioapic_irq_count++;
    }

    /*
     * Wake the vCPU so it re-enters vm_run — pre_run will inject
     * the interrupt vector via vm_lapic_irq().
     */
    if (level) {
        CPUState *cpu = first_cpu;
        if (cpu) {
            cpu_interrupt(cpu, CPU_INTERRUPT_HARD);
        }
    }

    if (err) {
        fprintf(stderr, "IOAPIC: Could not assert IRQ %d (pin %d): err=%d errno=%d\n",
                irq, pin, err, errno);
    }
}

static uint64_t
bhyve_ioapic_mem_read(void *opaque, hwaddr addr, unsigned int size)
{
    IOAPICCommonState *s = opaque;
    int index;
    uint32_t val = 0;

    addr &= 0xff;

    switch (addr) {
    case IOAPIC_IOREGSEL:
        val = s->ioregsel;
        break;
    case IOAPIC_IOWIN:
        if (size != 4) {
            break;
        }
        switch (s->ioregsel) {
        case IOAPIC_REG_ID:
        case IOAPIC_REG_ARB:
            val = s->id << IOAPIC_ID_SHIFT;
            break;
        case IOAPIC_REG_VER:
            val = s->version |
                ((IOAPIC_NUM_PINS - 1) << IOAPIC_VER_ENTRIES_SHIFT);
            break;
        default:
            index = (s->ioregsel - IOAPIC_REG_REDTBL_BASE) >> 1;
            if (index >= 0 && index < IOAPIC_NUM_PINS) {
                if (s->ioregsel & 1) {
                    val = s->ioredtbl[index] >> 32;
                } else {
                    val = s->ioredtbl[index] & 0xffffffff;
                }
            }
        }
        break;
    }

    return val;
}

static void
bhyve_ioapic_mem_write(void *opaque, hwaddr addr, uint64_t val,
                       unsigned int size)
{
    IOAPICCommonState *s = opaque;
    int index;

    addr &= 0xff;

    switch (addr) {
    case IOAPIC_IOREGSEL:
        s->ioregsel = val;
        break;
    case IOAPIC_IOWIN:
        if (size != 4) {
            break;
        }
        switch (s->ioregsel) {
        case IOAPIC_REG_ID:
            s->id = (val >> IOAPIC_ID_SHIFT) & IOAPIC_ID_MASK;
            break;
        case IOAPIC_REG_VER:
        case IOAPIC_REG_ARB:
            break;
        default:
            index = (s->ioregsel - IOAPIC_REG_REDTBL_BASE) >> 1;
            if (index >= 0 && index < IOAPIC_NUM_PINS) {
                uint64_t ro_bits = s->ioredtbl[index] & IOAPIC_RO_BITS;
                if (s->ioregsel & 1) {
                    s->ioredtbl[index] &= 0xffffffff;
                    s->ioredtbl[index] |= (uint64_t)val << 32;
                } else {
                    s->ioredtbl[index] &= ~0xffffffffULL;
                    s->ioredtbl[index] |= val;
                }
                /* restore RO bits */
                s->ioredtbl[index] &= IOAPIC_RW_BITS;
                s->ioredtbl[index] |= ro_bits;

                /* Edge-triggered: clear Remote IRR */
                if (!(s->ioredtbl[index] & IOAPIC_LVT_TRIGGER_MODE)) {
                    s->ioredtbl[index] &= ~((uint64_t)IOAPIC_LVT_REMOTE_IRR);
                }

                /* Update vector cache for interrupt injection.
                 * Keep the vector even when masked — the PIC path needs
                 * it to inject at the correct vector regardless of mask state. */
                uint8_t vec = s->ioredtbl[index] & 0xFF;
                if (vec >= 0x10) {
                    bhyve_ioapic_vectors[index] = vec;
                    static int rte_log = 0;
                    if (rte_log < 20) {
                        int masked = (s->ioredtbl[index] >> IOAPIC_LVT_MASKED_SHIFT) & 1;
                        fprintf(stderr, "IOAPIC: RTE[%d] vec=0x%02x masked=%d\n",
                                index, vec, masked);
                        rte_log++;
                    }
                }
            }
        }
        break;
    }
}

static const MemoryRegionOps bhyve_ioapic_io_ops = {
    .read = bhyve_ioapic_mem_read,
    .write = bhyve_ioapic_mem_write,
    .endianness = DEVICE_NATIVE_ENDIAN,
};

static void bhyve_ioapic_realize(DeviceState *dev, Error **errp)
{
    IOAPICCommonState *s = IOAPIC_COMMON(dev);

    memory_region_init_io(&s->io_memory, OBJECT(dev), &bhyve_ioapic_io_ops, s,
                          "bhyve-ioapic", 0x1000);
    s->version = 0x11;

    qdev_init_gpio_in(dev, bhyve_ioapic_set_irq, IOAPIC_NUM_PINS);
}

static void bhyve_ioapic_class_init(ObjectClass *klass, const void *data)
{
    IOAPICCommonClass *k = IOAPIC_COMMON_CLASS(klass);
    DeviceClass *dc = DEVICE_CLASS(klass);

    k->realize   = bhyve_ioapic_realize;
    k->pre_save  = bhyve_ioapic_get;
    k->post_load = bhyve_ioapic_put;
    device_class_set_legacy_reset(dc, bhyve_ioapic_reset);
}

static const TypeInfo bhyve_ioapic_info = {
    .name  = TYPE_BHYVE_IOAPIC,
    .parent = TYPE_IOAPIC_COMMON,
    .instance_size = sizeof(BhyveIOAPICState),
    .class_init = bhyve_ioapic_class_init,
};

static void bhyve_ioapic_register_types(void)
{
    type_register_static(&bhyve_ioapic_info);
}

type_init(bhyve_ioapic_register_types)
