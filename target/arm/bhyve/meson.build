vmmapi = dependency('', required: false)
if not vmmapi.found()
  vmmapi = cc.find_library('vmmapi', required: false)
endif

if vmmapi.found()
  # Override <machine/vmm.h> with ARM64 kernel headers for cross-compilation.
  bhyve_arm64_inc = include_directories('arm64-inc', is_system: true)
  bhyve_arm64_dep = declare_dependency(
    include_directories: bhyve_arm64_inc,
    dependencies: vmmapi,
  )

  arm_system_ss.add(when: 'CONFIG_BHYVE_ARM64', if_true: files(
    'bhyve-arm64.c',
  ))
  arm_system_ss.add(when: 'CONFIG_BHYVE_ARM64', if_true: bhyve_arm64_dep)
endif
