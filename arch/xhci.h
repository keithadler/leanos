/* The machine layer's side of the xHCI controller (the VL805 behind the PCIe bridge, the
   Pi 4's USB-A ports): arch/xhci.c. It checks the controller's register layout at boot,
   stores the xHCI memory's boot content, resets the controller, and carries out each request
   the Lean kernel approved (`sysXhci`), exactly as ROADMAP.md (stage 7, USB part 2) says.

   arch/xhci.c touches the hardware only through the functions below, so the same file is
   compiled for the host by test/xhci-sim/, against a model of the controller, and for the Pi,
   where arch/pcie.c and arch/kmain.c provide them. */
#pragma once
#include <stdint.h>

/* ---- what arch/xhci.c needs ---- */
/* A 32-bit register at byte `off` of the controller's registers (its memory BAR). */
uint32_t xhci_mmio_r32(uint64_t off);
void xhci_mmio_w32(uint64_t off, uint32_t v);
/* The 32-bit word at physical address `pa`, as the kernel reaches it (identity-mapped). */
volatile uint32_t *xhci_phys32(uint64_t pa);
/* Clean (`xhci_clean`: DC CVAC), or clean and invalidate (`xhci_flush`: DC CIVAC), every cache
   line of `len` bytes from physical `pa` to the point of coherency, then DSB. */
void xhci_clean(uint64_t pa, uint64_t len);
void xhci_flush(uint64_t pa, uint64_t len);
void xhci_barrier(void);                  /* DSB SY */
void xhci_bus_master(int on);             /* the controller's PCI command register, bit 2 */
void xhci_udelay(uint64_t us);
uint64_t xhci_boot_word(uint64_t i);      /* `xhciBoot i`, from the Lean kernel */
void kputs(const char *s);
void kputhex(uint64_t v);
void kputdec(uint64_t v);
__attribute__((noreturn)) void kpanic(const char *msg);

/* ---- what arch/xhci.c does ---- */
/* The controller's registers are mapped (`bar` bytes of them), its PCI identity is `id`
   (vendor in the low 16 bits, device in the high) and `rev`: read its capabilities and keep it
   off, saying why on the console, unless the layout is one the kernel's checks were written
   for. 1 if it may be used. */
int xhci_probe(uint64_t bar, uint32_t id, uint32_t rev);
/* The USB driver's frames are about to be cleared and loaded: if the controller runs, stop it
   and turn its bus mastering off, so it does no DMA into frames being rewritten. */
void xhci_before_load(void);
/* They have been cleared: store the xHCI memory's boot content at `base` (`leanos_xhci_base`),
   clean it to memory, reset the controller, then turn bus mastering on. 1 if the controller
   came out of its reset; else it stays off. */
int xhci_after_load(uint64_t base);
/* Carry out what `sysXhci` approved (`xhciOp`, with `usbA` to `usbD`). 1 if done (for op 1,
   the register's value in *v), 0 if the controller is off (an I/O error for the driver). */
int xhci_request(uint64_t op, uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint32_t *v);
/* 1 once `xhci_probe` accepted the controller. */
int xhci_present(void);
