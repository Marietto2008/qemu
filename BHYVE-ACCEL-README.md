# QEMU bhyve accelerator — patch series

**Milestone: Full Debian 13 (trixie) boot with login shell via `-accel bhyve`**

Host: FreeBSD 16.0-CURRENT (dumrich's GSoC 2025 vmm.ko fork)  
QEMU: dumrich/qemu branch `accel-vmm`

## What works

- Debian GNU/Linux 13 boots to multi-user login in ~3 seconds
- systemd detects `virtualization bhyve`
- User login, cron, journald, udevd, logind, networking, getty all OK
- IDE disk (read+write), serial console, keyboard input, CDROM
- NIC detected (rtl8139, IO-APIC IRQ 10)

## Patch summary

### QEMU patches (apply to dumrich/qemu branch accel-vmm)

| # | File | Description |
|---|------|-------------|
| 0001 | accel/meson.build, target/i386/bhyve/meson.build, accel/bhyve/meson.build | Restructure meson build — move bhyve files to accel/bhyve/ |
| 0002 | accel/bhyve/bhyve-all.c | Full rewrite: segment descriptor VMX conversion, MMIO fallback, register sync |
| 0003 | accel/bhyve/bhyve-i8259.c | i8259 IRQ handling for legacy PIC mode |
| 0004 | accel/bhyve/bhyve-ioapic.c | IOAPIC MMIO emulation with RTE programming |
| 0005 | accel/bhyve/bhyve-internal.h | Internal header for bhyve accelerator |
| 0006 | accel/bhyve/bhyve-accel-ops.c | Accelerator ops (init, create vcpu, etc.) |
| 0007 | hw/ide/ | IDE IRQ delivery debug traces |
| 0008 | timer | Timer/clock debug traces |

### FreeBSD kernel patches (apply to dumrich's freebsd-src 16.0-CURRENT)

| # | File | Description |
|---|------|-------------|
| 0009 | sys/amd64/vmm/intel/vmx.c | Debug printf in vmx_inject_interrupts (timer race workaround) |
| 0010 | sys/amd64/vmm/io/vlapic.c | Debug printf in vlapic_pending_intr (PPR blocking trace) |
| 0011 | sys/amd64/vmm/vmm.c | IOAPIC MMIO → userspace fallback + HLT returns to userspace |
| 0012 | sys/amd64/vmm/vmm_lapic.c | lapic_set_intr debug trace |

## Known issues / workarounds

- `no_timer_check` required in guest kernel cmdline (IO-APIC timer verification fails)
- `acpi=off` required (ACPI tables incomplete in bhyve accelerator)
- q35 machine type doesn't work (AHCI uses MSI interrupts → not yet supported)
- Patches 0009/0010/0012 are debug printfs that accidentally fix a timer race condition
- TSC marked unstable (clocksource falls back to refined-jiffies)
- Many "Error Reading/Writing to MSR" messages (harmless, unhandled MSRs like RAPL)

## Boot command

```sh
/path/to/qemu-system-x86_64 \
  -accel bhyve \
  -machine pc,hpet=off \
  -m 1024 \
  -display none -vga none \
  -serial mon:stdio \
  -hda debian-disk.qcow2 \
  -nic user,model=rtl8139 \
  -no-reboot \
  -kernel debian-installed-vmlinuz \
  -initrd debian-installed-initrd.gz \
  -append "root=/dev/sda1 console=ttyS0,115200 earlyprintk=serial,ttyS0,115200 no_timer_check i8042.noprobe acpi=off" \
  2>/tmp/vmexit.log
```

## Prerequisites

- FreeBSD 16.0-CURRENT with dumrich's vmm.ko (github.com/dumrich/freebsd-src)
- Custom libvmmapi with QEMU support (vm_setup_qmemory, vm_set_flags, etc.)
- QEMU built from dumrich/qemu branch accel-vmm + these patches
- vmm.ko loaded (`kldload vmm`)

## How to apply

### QEMU patches
```sh
cd /path/to/qemu   # dumrich/qemu branch accel-vmm
git am 0001-qemu-accel-bhyve-meson-build.patch
git am 0002-qemu-accel-bhyve-all-rewrite.patch
git am 0003-qemu-accel-bhyve-i8259-irq.patch
git am 0004-qemu-accel-bhyve-ioapic-mmio.patch
git am 0005-qemu-accel-bhyve-internal-header.patch
git am 0006-qemu-accel-bhyve-accel-ops.patch
git am 0007-qemu-hw-ide-irq-debug.patch
git am 0008-qemu-timer-debug.patch
```

### Kernel patches
```sh
cd /path/to/freebsd-src   # dumrich's 16.0-CURRENT fork
git am 0009-vmm-kernel-vmx-inject-debug.patch
git am 0010-vmm-kernel-vlapic-ppr-debug.patch
git am 0011-vmm-kernel-vmm-ioapic-hlt-userspace.patch
git am 0012-vmm-kernel-lapic-debug.patch
# Rebuild vmm.ko:
make -j8 KERNCONF=GENERIC buildkernel MODULES_OVERRIDE=vmm
```

## Next steps

- Fix the timer race condition properly (replace debug printf with memory barrier or proper synchronization)
- Implement MSI interrupt delivery (enables q35/AHCI and reliable networking)
- Handle unimplemented MSRs gracefully
- Test network connectivity (ping, DHCP)
- ACPI table support
