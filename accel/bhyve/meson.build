bhyve_ss = ss.source_set()

bhyve_ss.add(files(
  'bhyve-all.c',
  'bhyve-accel-ops.c',
  'bhyve-apic.c',
  'bhyve-ioapic.c',
  'bhyve-i8259.c',
))

# Aggiungi la dipendenza da libvmmapi
vmmapi = dependency('', required: false)
if not vmmapi.found()
  vmmapi = cc.find_library('vmmapi', required: true)
endif

bhyve_ss.add(vmmapi)

specific_ss.add_all(when: 'CONFIG_BHYVE', if_true: bhyve_ss)
