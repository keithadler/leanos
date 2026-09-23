/-!
# A model of the Armv8-A stage-1 translation walk, as user mode sees it

This file is trusted: it states what the MMU does with the table words the kernel
computes. It is small on purpose, so it can be checked by hand against the Arm
Architecture Reference Manual (DDI 0487, chapter D8, "The AArch64 Virtual Memory System
Architecture").

It covers exactly the configuration the machine layer sets up (`mmu_init` in
`arch/kmain.c`):

* EL1&0 stage-1 translation through TTBR0 only (TCR_EL1.EPD1 = 1: any address that would
  need TTBR1 faults),
* a 4 KiB granule (TG0 = 0) and 39-bit virtual addresses (T0SZ = 25), so the walk starts
  at level 1,
* SCTLR_EL1.WXN = 0 and no stage 2.

The model answers one question: for a virtual address, can code running at EL0 read,
write or execute it, and at which physical address? It can only claim *more* access than
the hardware grants, never less, wherever it simplifies. That is the safe direction for
the isolation theorems, which bound what user mode can reach. The simplifications:

* The hierarchical controls in table descriptors (APTable, UXNTable, PXNTable) can only
  take access away, so they are ignored. The kernel's table descriptors set them to zero
  anyway.
* Faults for output addresses beyond the configured physical address size are ignored.
* Memory attributes and shareability do not affect permission and are ignored.
* The TLB is not modelled: the machine layer invalidates it after every table change
  (`tlb_flush_all`), so a walk always reads the current words. That is part of what is
  trusted about the machine layer.
-/

namespace Arm

/-- What EL0 may do at an address. -/
structure Perm where
  r : Bool
  w : Bool
  x : Bool
deriving DecidableEq, Repr

/-- Bits `lo` to `lo + n - 1` of `d`. -/
def field (d lo n : Nat) : Nat := d / 2 ^ lo % 2 ^ n

/-- Physical memory as the MMU reads it: the 64-bit word at each address. -/
abbrev Mem := Nat → Nat

/-- The output address of a descriptor whose address field starts at bit `shift` (12 for a
table or page, 21 for a level-2 block, 30 for a level-1 block): bits `shift` to 47. -/
def outAddr (d shift : Nat) : Nat := field d shift (48 - shift) * 2 ^ shift

/-- A block or page descriptor `d` covering `2^shift` bytes, as EL0 sees it (D8.4 "Memory
access control"):
* the access flag (bit 10) clear means any access faults;
* AP[2:1] (bits 7:6): 01 gives EL0 read-write, 11 gives EL0 read-only, 00 and 10 give EL0
  no data access;
* UXN (bit 54) set means EL0 may not execute, whatever AP says.
EL0 can execute a page it cannot read if UXN is clear. The kernel's own entries set UXN
for exactly this reason. -/
def leaf (d shift va : Nat) : Option (Nat × Perm) :=
  if field d 10 1 = 0 then none
  else
    let ap := field d 6 2
    let r := ap == 1 || ap == 3
    let w := ap == 1
    let x := field d 54 1 == 0
    if r || x then some (outAddr d shift + va % 2 ^ shift, ⟨r, w, x⟩) else none

/-- The translation of `va` for EL0, starting from the level-1 table at `ttbr`.
Descriptor type is bits 1:0: at levels 1 and 2, `01` is a block and `11` a table; at
level 3, `11` is a page and anything else faults. `00` is invalid at every level. -/
def walkEL0 (mem : Mem) (ttbr va : Nat) : Option (Nat × Perm) :=
  if 2 ^ 39 ≤ va then none
  else
    let d1 := mem (ttbr + 8 * field va 30 9)
    if field d1 0 2 = 1 then leaf d1 30 va
    else if field d1 0 2 = 3 then
      let d2 := mem (outAddr d1 12 + 8 * field va 21 9)
      if field d2 0 2 = 1 then leaf d2 21 va
      else if field d2 0 2 = 3 then
        let d3 := mem (outAddr d2 12 + 8 * field va 12 9)
        if field d3 0 2 = 3 then leaf d3 12 va else none
      else none
    else none

end Arm
