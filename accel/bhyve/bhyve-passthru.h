#ifndef BHYVE_PASSTHRU_H
#define BHYVE_PASSTHRU_H

#include "hw/pci/pci.h"
#include "system/memory.h"
#include <sys/pciio.h>

#define TYPE_BHYVE_PASSTHRU "bhyve-passthru"
OBJECT_DECLARE_SIMPLE_TYPE(BhyvePassthruState, BHYVE_PASSTHRU)

struct bhyve_passthru_bar {
    MemoryRegion mr;
    uint64_t size;
    uint64_t hpa;
    uint64_t gpa;
    bool mapped;
    uint8_t type;
};

struct BhyvePassthruState {
    PCIDevice parent_obj;

    /* Properties */
    char *host_str;

    /* Parsed BDF */
    struct pcisel sel;
    int host_bus;
    int host_slot;
    int host_func;

    /* Host /dev/pci handle */
    int pcifd;

    /* Physical BAR configurations */
    struct bhyve_passthru_bar bars[PCI_NUM_REGIONS];

    /* MSI / MSI-X info */
    bool msi_present_phys;
    uint32_t msi_cap_len;
    bool msix_present_phys;
    uint8_t msix_table_bar_nr;
    uint32_t msix_table_offset;
    uint8_t msix_pba_bar_nr;
    uint32_t msix_pba_offset;
    uint32_t msix_entries_nr;

    /* NVIDIA GPU quirk: PCI config space mirrored at BAR0+0x88000 */
    bool is_nvidia_gpu;

    /* Cached PCI config — read before PPT assignment.
     * Full 4KB PCIe extended config space (0x000-0xFFF).
     * NVIDIA driver reads extended caps through BAR0+0x88000 mirror. */
    uint8_t host_config[4096];

    /* Index into bhyve_passthru_msi_vectors[] for IRR scrub protection, or -1 */
    int msi_scrub_idx;

};

#endif /* BHYVE_PASSTHRU_H */
