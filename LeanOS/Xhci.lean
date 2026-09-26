import LeanOS.Proofs

/-!
# The xHCI controller only touches the USB driver's memory

The USB-A ports of a Raspberry Pi 4 are a VL805 xHCI controller behind the PCIe bridge,
and the Pi has no IOMMU: whatever address the controller finds, it reads or writes. An
xHCI controller finds its addresses in memory, in rings of TRBs and in contexts, so it is
not enough to check its registers, as `sysUsb` does for the DWC2. `sysXhci` in
`LeanOS/Kernel.lean` keeps all of those structures in the xHCI memory, 64 frames the USB
driver holds read-only, and writes them itself after checking every address in them.

This file proves that, against a model of the controller written from the xHCI
specification (Intel, eXtensible Host Controller Interface for USB, revision 1.2):

* `Model`: for a TRB on the command ring or on a transfer ring, 16 bytes of an input
  context, and a register write, what the controller then touches (`Access`): a data
  buffer, a ring of TRBs, an input context, the DCBAA and the tables it leads to, the event
  ring, or something the model cannot say (`unknown`: an address in a structure the kernel
  does not write, or a feature it does not allow). Where the specification says a TRB of
  the wrong type is an error, the model says it touches nothing.
* `XAllowed`: where the controller may go: a data buffer only in the USB driver's own
  frames, never in the xHCI memory; a ring, context or table only at its own part of the
  xHCI memory (`xhci_layout`: the parts do not overlap, and the parts the controller writes
  are apart from the parts it reads as structures).
* `xhci_dma_own_memory`: in every reachable state, everything a system call asks the
  machine layer to write for the controller makes it touch only what `XAllowed` allows;
  `xhci_boot_ok`: so does what the xHCI memory holds from boot; `xhci_guard_safe`: and so
  does a TRB half written.
* `xhci_region_readonly`: only the USB driver ever holds the xHCI memory, and never with
  the write right, so only the kernel writes it.
* `only_usb_driver_drives_xhci`, `xhci_writes_in_memory`, `xhci_sync_own_memory`: only the
  USB driver reaches the controller; the machine layer writes only the kernel's parts of
  the xHCI memory; cache maintenance only covers the driver's own frames.

What is trusted: that the model says what the VL805 does, and the machine layer's duties
(ROADMAP.md, stage 7, USB part 2; TRUST.md).
-/

namespace LeanOS

/-! ## The xHCI memory -/

/-- Byte `x` is in the xHCI memory. -/
def InXhci (x : Nat) : Prop := xhciBase ≤ x ∧ x < xhciBase + xhciPages * pageSize

/-- **The layout.** The xHCI memory is the last 64 of the USB driver's frames, 64 KiB
aligned, and its parts follow one another inside it without overlapping: the DCBAA, the
scratchpad array, the ERST, the event ring, the command ring, the scratchpad pages, the
device contexts, the input contexts and the transfer rings, the last in a 64 KiB block of
its own. The controller writes the event ring, the scratchpad pages and the device
contexts, and reads the others as structures. -/
theorem xhci_layout :
    xhciFirst = framesPerTask * usbTask + framesPerTask - xhciPages ∧
    xhciFirst + xhciPages = framesPerTask * (usbTask + 1) ∧
    xhciBase = frameBase + xhciFirst * pageSize ∧ xhciBase % 65536 = 0 ∧
    xDcbaa = xhciBase ∧ xDcbaa + 256 * 8 ≤ xScratchArr ∧ xScratchArr + 256 * 8 ≤ xErst ∧
    xErst + 16 ≤ xEvents ∧ xEvents + 16 * xEventTrbs ≤ xCmd ∧ xCmd + 16 * xCmdTrbs ≤ xScratch ∧
    xScratch + xScratchPages * pageSize ≤ xOut ∧ xOut + xSlots * pageSize ≤ xIn ∧
    xIn + xInputs * pageSize ≤ xRings ∧ xRings % 65536 = 0 ∧
    xRings + 16 * xRingTrbs = xhciBase + xhciPages * pageSize := by
  decide

/-! ## A model of the controller -/

/-- What the controller may touch in memory. -/
inductive Access where
  /-- bytes `a` to `a + n - 1`, which it reads (data going out) or writes (coming in) -/
  | data (a n : Nat)
  /-- TRBs of a transfer ring, from `a` on -/
  | ring (a : Nat)
  /-- TRBs of the command ring, from `a` on -/
  | cmdRing (a : Nat)
  /-- an input context at `a`, which it reads -/
  | input (a : Nat)
  /-- a device context at `a`, which it writes and reads -/
  | device (a : Nat)
  /-- a scratchpad page at `a`, which it writes and reads -/
  | scratch (a : Nat)
  /-- `n` bytes of an event ring at `a`, which it writes -/
  | events (a n : Nat)
  /-- `n` bytes of a table of addresses at `a` (the DCBAA, the scratchpad array, the ERST),
  which it reads and follows -/
  | table (a n : Nat)
  /-- something the model cannot bound -/
  | unknown

namespace Model

/-! The fields of a TRB and a context, as the specification lays them out (chapter 6),
written here apart from the kernel's own. -/

/-- TRB Type: control word, bits 10 to 15. -/
def trbType (control : Nat) : Nat := control / 2 ^ 10 % 2 ^ 6
/-- Immediate Data: control word, bit 6. -/
def idt (control : Nat) : Bool := control / 2 ^ 6 % 2 == 1
/-- TRB Transfer Length: status word, bits 0 to 16. -/
def trbLen (status : Nat) : Nat := status % 2 ^ 17
/-- Interrupter Target: status word, bits 22 to 31. -/
def intrTarget (status : Nat) : Nat := status / 2 ^ 22 % 2 ^ 10
/-- An address in bits 4 to 63 (a TRB, a context, a transfer ring dequeue pointer). -/
def ptr16 (p : Nat) : Nat := p / 16 * 16

/-- A TRB on a transfer ring (6.4.1, 6.4.4, 6.4.5). Its events go to its interrupter,
whose event ring the kernel set only for interrupter 0. Normal, Data Stage and Isoch TRBs
move data at their buffer, unless the data is in the TRB itself; so does a Setup Stage TRB
without it (the specification requires it); a Link TRB goes on to another TRB; Status
Stage, Event Data and No-Op TRBs touch no memory; any other type on a transfer ring is a
TRB Error. -/
def transferTrb (p status control : Nat) : List Access :=
  let ty := trbType control
  if intrTarget status ≠ 0 then .unknown :: .nil
  else if ty = 1 ∨ ty = 2 ∨ ty = 3 ∨ ty = 5 then
    (if idt control then .nil else .data p (trbLen status) :: .nil)
  else if ty = 6 then .ring (ptr16 p) :: .nil
  else .nil

/-- A TRB on the command ring (6.4.3): Address Device, Configure Endpoint and Evaluate
Context read an input context; Set TR Dequeue Pointer sets a transfer ring (or, with a
stream, a stream context array); Force Event, Get Port Bandwidth and the extended property
commands have addresses of their own; a Link TRB goes on to another TRB; the other commands
touch no memory, and any other type on the command ring is a TRB Error. -/
def commandTrb (p status control : Nat) : List Access :=
  let ty := trbType control
  if ty = 6 then (if intrTarget status ≠ 0 then .unknown :: .nil else .cmdRing (ptr16 p) :: .nil)
  else if ty = 11 ∨ ty = 12 ∨ ty = 13 then .input (ptr16 p) :: .nil
  else if ty = 16 then
    (if p / 2 % 8 ≠ 0 ∨ status / 2 ^ 16 ≠ 0 then .unknown :: .nil else .ring (ptr16 p) :: .nil)
  else if ty = 18 ∨ ty = 21 ∨ ty = 24 ∨ ty = 25 then .unknown :: .nil
  else .nil

/-- A TRB at address `a`: a command if `a` is in the command ring, a transfer TRB if it is in
the transfer rings (the only rings the controller is ever given: `run`, the checked CRCR,
input contexts and Link TRBs point nowhere else), and otherwise unknown. -/
def trbAt (a p status control : Nat) : List Access :=
  if xCmd ≤ a ∧ a < xCmd + 16 * xCmdTrbs then commandTrb p status control
  else if xRings ≤ a ∧ a < xRings + 16 * xRingTrbs then transferTrb p status control
  else .unknown :: .nil

/-- 16 bytes at byte `z` of the input contexts, placed as if each context took 64 bytes:
context `c` (0 the input control context, 1 the slot context, 2 to 32 the endpoint
contexts), bytes `16u` on (6.2.2, 6.2.3, 6.2.5). The slot context's Interrupter Target is
in word 2, bits 22 to 31; an endpoint context's MaxPStreams in word 0, bits 10 to 14 (not
0: its dequeue pointer is a stream context array), its TR Dequeue Pointer in words 2 and 3,
bits 4 to 63. Past the first 32 bytes of a context, the bytes would belong to another
context when contexts take 32 bytes. -/
def inputUnit (z lo hi : Nat) : List Access :=
  let c := z % 4096 / 64
  let u := z % 64 / 16
  if z ≥ xInputs * 4096 ∨ z % 16 ≠ 0 ∨ u ≥ 2 ∨ c ≥ 33 then .unknown :: .nil
  else if c = 1 ∧ u = 0 then (if intrTarget (hi % 2 ^ 32) ≠ 0 then .unknown :: .nil else .nil)
  else if 2 ≤ c ∧ u = 0 then
    (if lo / 2 ^ 10 % 2 ^ 5 ≠ 0 then .unknown :: .nil else .ring (ptr16 hi) :: .nil)
  else .nil

/-- A register write (chapter 5), register `reg` as `sysXhci` numbers them. USBCMD: Run/Stop
runs the controller with whatever DMA bases it has; save and restore state, the light
reset and the newer bits are left unknown; reset and the enables touch no memory. CRCR sets
the command ring; DCBAAP the DCBAA. The ports' registers, USBSTS, DNCTRL and CONFIG touch
no memory. Interrupter 0's ERDP is claimed as a place in the event ring (the controller
only compares it); every other runtime register but IMAN and IMOD (ERSTSZ, ERSTBA, the
other interrupters') is unknown. A doorbell makes the controller read rings it has already
been given, but with a stream it reads a stream context array. The capability registers,
and the extended capabilities after them, are unknown. -/
def regWrite (reg v : Nat) : List Access :=
  let sp := reg / 2 ^ 16
  let o := reg % 2 ^ 16
  if o % 4 ≠ 0 then .unknown :: .nil
  else if sp = 1 then
    if o = 0 then (if v % 2 = 1 ∨ v / 2 ^ 4 % 2 ^ 6 ≠ 0 ∨ v ≥ 2 ^ 11 then .unknown :: .nil else .nil)
    else if o = 4 ∨ o = 8 ∨ o = 0x14 ∨ o = 0x38 then .nil
    else if o = 0x18 then .cmdRing (v / 64 * 64) :: .nil
    else if o = 0x30 then .table (v / 64 * 64) 2048 :: .nil
    else if 1024 ≤ o ∧ o < 1024 + 16 * xPorts then .nil
    else .unknown :: .nil
  else if sp = 2 then
    if o = 0x20 ∨ o = 0x24 then .nil
    else if o = 0x38 then .events (ptr16 v) 16 :: .nil
    else .unknown :: .nil
  else if sp = 3 then
    if o = 0 then (if v = 0 then .nil else .unknown :: .nil)
    else if o ≤ 4 * 255 ∧ v % 2 ^ 8 ≥ 1 ∧ v % 2 ^ 8 ≤ 31 ∧ v / 2 ^ 16 = 0 then .nil
    else .unknown :: .nil
  else .unknown :: .nil

end Model

/-- What the controller may touch because of what a reply asks the machine layer to write
(ROADMAP.md says how it writes it): op 2, register `usbA` := `usbB`; op 3, `run`: DCBAAP :=
`usbA`, CRCR := `usbB`, ERSTSZ := 1, ERSTBA := `usbC`, ERDP := `usbD`, then Run; op 4, a TRB
at `usbA` (parameter `usbB`, status `usbC`, control word the low 32 bits of `usbD`), whose
control word is first the guard (the high 32 bits, `xGuard`); op 5, 16 bytes of an input
context at `usbA`. A register read (op 1) and cache maintenance (op 6) touch nothing. -/
def xAccessesOf (op a b c d : Nat) : List Access :=
  if op = 2 then Model.regWrite a b
  else if op = 3 then
    .table a 2048 :: .cmdRing (b / 64 * 64) :: .table c 16 :: .events (Model.ptr16 d) 16 :: .nil
  else if op = 4 then app (Model.trbAt a b c (d % 2 ^ 32)) (Model.trbAt a b c (d / 2 ^ 32))
  else if op = 5 then (if xIn ≤ a then Model.inputUnit (a - xIn) b c else .unknown :: .nil)
  else .nil

def xAccesses (r : Reply) : List Access := xAccessesOf r.xhciOp r.usbA r.usbB r.usbC r.usbD

/-- Where the controller may go. A data buffer: bytes of the USB driver's own frames,
outside the xHCI memory. Anything else: its own part of the xHCI memory. -/
def XAllowed : Access → Prop
  | .data a n => ∀ x, a ≤ x → x < a + n →
      frameBase ≤ x ∧ owner ((x - frameBase) / pageSize) = usbTask ∧ ¬ InXhci x
  | .ring a => a % 16 = 0 ∧ xRings ≤ a ∧ a < xRings + 16 * xRingTrbs
  | .cmdRing a => a % 16 = 0 ∧ xCmd ≤ a ∧ a < xCmd + 16 * xCmdTrbs
  | .input a => ∃ k, k < xInputs ∧ a = xIn + k * pageSize
  | .device a => ∃ i, i < xSlots ∧ a = xOut + i * pageSize
  | .scratch a => ∃ k, k < xScratchPages ∧ a = xScratch + k * pageSize
  | .events a n => xEvents ≤ a ∧ a + n ≤ xEvents + 16 * xEventTrbs
  | .table a n => (a = xDcbaa ∧ n ≤ 256 * 8) ∨ (a = xScratchArr ∧ n ≤ 256 * 8) ∨ (a = xErst ∧ n ≤ 16)
  | .unknown => False

/-- One step's version: a data buffer is in a run of task `j`'s own frames that `cs` holds
with the write right, and in one it holds with the read right. -/
def XOk (j : Nat) (cs : List Cap) : Access → Prop
  | .data a n => (∃ c ∈ cs, ∃ b k, c.obj = .frames b k ∧ framesPerTask * j ≤ b ∧
        b + k ≤ framesPerTask * (j + 1) ∧ b + k ≤ poolFrames ∧ frameBase + b * pageSize ≤ a ∧
        a + n ≤ frameBase + (b + k) * pageSize ∧ c.rights.w = true) ∧
      (∃ c ∈ cs, ∃ b k, c.obj = .frames b k ∧ framesPerTask * j ≤ b ∧
        b + k ≤ framesPerTask * (j + 1) ∧ b + k ≤ poolFrames ∧ frameBase + b * pageSize ≤ a ∧
        a + n ≤ frameBase + (b + k) * pageSize ∧ c.rights.r = true)
  | a => XAllowed a

/-! ## Facts the proofs use -/

theorem xhciBase_eq : xhciBase = 85721088 := by decide
theorem xDcbaa_eq : xDcbaa = 85721088 := by decide
theorem xScratchArr_eq : xScratchArr = 85723136 := by decide
theorem xErst_eq : xErst = 85725184 := by decide
theorem xEvents_eq : xEvents = 85729280 := by decide
theorem xCmd_eq : xCmd = 85733376 := by decide
theorem xScratch_eq : xScratch = 85737472 := by decide
theorem xOut_eq : xOut = 85786624 := by decide
theorem xIn_eq : xIn = 85852160 := by decide
theorem xRings_eq : xRings = 85917696 := by decide

/-- Every constant of the layout, as a number. -/
macro "xlits" : tactic => `(tactic| try simp only [xhciBase_eq, xDcbaa_eq, xScratchArr_eq, xErst_eq,
  xEvents_eq, xCmd_eq, xScratch_eq, xOut_eq, xIn_eq, xRings_eq, xSlots, xInputs, xScratchPages,
  xEventTrbs, xCmdTrbs, xRingTrbs, xTrbs, xPorts, pageSize, tNormal, tSetup, tData, tStatus,
  tLink, tEventData, tNoOp, tEnableSlot, tDisableSlot, tAddress, tConfigure, tEvaluate,
  tResetEp, tStopEp, tSetDeq, tResetDevice, tNoOpCmd] at *)

@[simp] theorem ltB_eq (a b : Nat) : ltB a b = decide (a < b) := by
  unfold ltB
  by_cases h : a < b
  · have : Nat.ble b a = false := by
      cases e : Nat.ble b a
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true e) (by omega)
    simp [this, h]
  · simp [Nat.ble_eq.mpr (by omega : b ≤ a), h]

theorem type_eq (c : Nat) : Model.trbType c = xType c := by simp [Model.trbType, xType]
theorem intr_eq (s : Nat) : Model.intrTarget s = xIntr s := by simp [Model.intrTarget, xIntr]
theorem idt_eq (c : Nat) : Model.idt c = xIdt c := by simp [Model.idt, xIdt, bit]
theorem len_eq (s : Nat) : Model.trbLen s = xLen s := by simp [Model.trbLen, xLen]

theorem xDataOk_spec {j : Nat} {cs : List Cap} {a n : Nat} (h : xDataOk j cs a n = true) :
    XOk j cs (.data a n) := by
  simp only [xDataOk, Bool.and_eq_true] at h
  obtain ⟨⟨-, hw⟩, hr⟩ := h
  obtain ⟨c, hc, b, k, ho, h1, h2, h3, h4, h5, h6⟩ := dmaOk_spec hw
  obtain ⟨c', hc', b', k', ho', h1', h2', h3', h4', h5', h6'⟩ := dmaOk_spec hr
  exact ⟨⟨c, hc, b, k, ho, h1, h2, h3, h4, h5, by simpa using h6⟩,
    ⟨c', hc', b', k', ho', h1', h2', h3', h4', h5', by simpa using h6'⟩⟩

/-- A TRB in the command ring is read as a command. -/
theorem trbAt_cmd {z : Nat} (hz : z < xCmdTrbs) (p st ctl : Nat) :
    Model.trbAt (xTrbAddr z) p st ctl = Model.commandTrb p st ctl := by
  unfold Model.trbAt xTrbAddr
  rw [if_pos hz, if_pos (by xlits; omega)]

/-- A TRB in the transfer rings is read as a transfer TRB. -/
theorem trbAt_ring {z : Nat} (hz : ¬ z < xCmdTrbs) (hz' : z < xTrbs) (p st ctl : Nat) :
    Model.trbAt (xTrbAddr z) p st ctl = Model.transferTrb p st ctl := by
  unfold Model.trbAt xTrbAddr
  rw [if_neg hz, if_neg (by xlits; omega), if_pos (by xlits; omega)]

/-- A Link TRB the kernel allows goes to its own ring. -/
theorem link_ok {j : Nat} {cs : List Cap} {cmd : Bool} {p st ctl : Nat}
    (ht : xType ctl = tLink) (h : xLinkOk cmd p st = true) :
    ∀ a ∈ (if cmd then Model.commandTrb p st ctl else Model.transferTrb p st ctl), XOk j cs a := by
  simp only [xLinkOk, xInCmd, xInRings, Bool.and_eq_true, beq_iff_eq, ltB_eq] at h
  obtain ⟨⟨hp, hin⟩, hi⟩ := h
  have hp16 : Model.ptr16 p = p := by simp only [Model.ptr16]; omega
  cases cmd
  · simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hin ⊢
    simp only [Model.transferTrb, type_eq, intr_eq, ht, hi, hp16]
    intro a ha; simp [tLink] at ha; subst ha
    exact ⟨hp, by xlits; omega, by xlits; omega⟩
  · simp only [if_true, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hin ⊢
    simp only [Model.commandTrb, type_eq, intr_eq, ht, hi, hp16]
    intro a ha; simp [tLink] at ha; subst ha
    exact ⟨hp, by xlits; omega, by xlits; omega⟩

/-- Membership in a list of at most one access. -/
theorem mem_one {a b : Access} : a ∈ (b :: .nil : List Access) ↔ a = b := by simp
theorem not_mem_nil' {a : Access} : ¬ a ∈ (.nil : List Access) := by simp

/-- A command the kernel allows touches only an input context or a transfer ring. -/
theorem cmd_ok {j : Nat} {cs : List Cap} {p st ctl : Nat} (h : xCmdOk (xType ctl) p st = true) :
    ∀ a ∈ Model.commandTrb p st ctl, XOk j cs a := by
  simp only [xCmdOk, xIsInput, xInRings, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Nat.ble_eq, ltB_eq, decide_eq_true_eq] at h
  simp only [Model.commandTrb, type_eq, Model.ptr16]
  generalize xType ctl = ty at h ⊢
  xlits
  intro a ha
  repeat' split at ha
  all_goals first
    | exact absurd ha not_mem_nil'
    | (rw [mem_one] at ha; subst ha
       simp only [XOk, XAllowed]; xlits
       first
        | (exfalso; omega)
        | exact ⟨(p / 16 * 16 - 85852160) / 4096, by omega, by omega⟩
        | exact ⟨by omega, by omega, by omega⟩)

/-- A transfer TRB the kernel allows touches only a buffer of the driver's, readable and
writable. -/
theorem xfer_ok {j : Nat} {cs : List Cap} {p st ctl : Nat}
    (h : xXferOk j cs (xType ctl) p st ctl = true) : ∀ a ∈ Model.transferTrb p st ctl, XOk j cs a := by
  simp only [xXferOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨hi, h⟩ := h
  simp only [Model.transferTrb, type_eq, intr_eq, idt_eq, len_eq, hi]
  intro a ha
  rcases h with ((((⟨⟨hty, hidt⟩, hd⟩ | ⟨⟨hty, hidt⟩, hl⟩) | hty) | hty) | hty) <;>
    simp only [tNormal, tData, tSetup, tStatus, tEventData, tNoOp] at hty
  · have h13 : xType ctl = 1 ∨ xType ctl = 2 ∨ xType ctl = 3 ∨ xType ctl = 5 := by omega
    simp only [h13, hidt, ne_eq, not_true_eq_false, if_false, if_true, Bool.false_eq_true] at ha
    rw [mem_one] at ha; subst ha; exact xDataOk_spec hd
  · simp [hty, hidt] at ha
  all_goals simp [hty] at ha

theorem link_cmd_last : xLinkOk true xCmd 0 = true := by decide
theorem link_ring_last : xLinkOk false xRings 0 = true := by decide

/-- A TRB the kernel writes at slot `z` touches only what `XOk` allows. -/
theorem trb_ok {j : Nat} {cs : List Cap} {z p st ctl : Nat} (hz : z < xTrbs)
    (h : xTrbOk j cs z p st ctl = true) : ∀ a ∈ Model.trbAt (xTrbAddr z) p st ctl, XOk j cs a := by
  unfold xTrbOk at h
  dsimp only at h
  by_cases hc : z < xCmdTrbs
  · rw [trbAt_cmd hc]
    have hcb : ltB z xCmdTrbs = true := by simp [hc]
    rw [hcb] at h
    split at h
    · simp only [Bool.and_eq_true, beq_iff_eq, if_true] at h
      obtain ⟨⟨ht, rfl⟩, rfl⟩ := h
      simpa using link_ok (j := j) (cs := cs) (cmd := true) (ctl := ctl) ht link_cmd_last
    · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, if_true] at h
      rcases h with ⟨ht, hl⟩ | h
      · simpa using link_ok (j := j) (cs := cs) (cmd := true) ht hl
      · exact cmd_ok h
  · rw [trbAt_ring hc hz]
    have hcb : ltB z xCmdTrbs = false := by simp [hc]
    rw [hcb] at h
    split at h
    · simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, if_false] at h
      obtain ⟨⟨ht, rfl⟩, rfl⟩ := h
      simpa using link_ok (j := j) (cs := cs) (cmd := false) (ctl := ctl) ht link_ring_last
    · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, if_false] at h
      rcases h with ⟨ht, hl⟩ | h
      · simpa using link_ok (j := j) (cs := cs) (cmd := false) ht hl
      · exact xfer_ok h

/-- Away from the last slot of a ring, the guard is a No-Op: on the command ring a No-Op
command, which touches nothing whatever the rest of the TRB holds; on a transfer ring a
No-Op TRB, which touches nothing as long as it reports to interrupter 0, as every TRB the
kernel writes there does. -/
theorem guard_noop {z ctl p st : Nat} (hz : z < xTrbs) (hl : xLast z = false)
    (hi : z < xCmdTrbs ∨ Model.intrTarget st = 0) :
    Model.trbAt (xTrbAddr z) p st (xGuard z ctl) = .nil := by
  have hb : ctl % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hc : z < xCmdTrbs
  · rw [trbAt_cmd hc]
    have : Model.trbType (xGuard z ctl) = 23 := by
      simp only [xGuard, hl, ltB_eq, hc, decide_true, if_true, Bool.false_eq_true, if_false,
        Model.trbType, tNoOpCmd]
      omega
    simp [Model.commandTrb, this]
  · rw [trbAt_ring hc hz]
    have : Model.trbType (xGuard z ctl) = 8 := by
      simp only [xGuard, hl, ltB_eq, hc, decide_false, Bool.false_eq_true, if_false,
        Model.trbType, tNoOp]
      omega
    simp [Model.transferTrb, this, hi.resolve_left hc]

/-- The guard the kernel returns with a TRB touches only what `XOk` allows, with the TRB's
own parameter and status. -/
theorem guard_ok {j : Nat} {cs : List Cap} {z p st ctl : Nat} (hz : z < xTrbs)
    (h : xTrbOk j cs z p st ctl = true) :
    ∀ a ∈ Model.trbAt (xTrbAddr z) p st (xGuard z ctl), XOk j cs a := by
  cases hl : xLast z
  · rw [guard_noop hz hl]
    · intro a ha; exact absurd ha not_mem_nil'
    · by_cases hc : z < xCmdTrbs
      · exact Or.inl hc
      · right
        rw [intr_eq]
        unfold xTrbOk at h
        dsimp only at h
        have hcb : ltB z xCmdTrbs = false := by simp [hc]
        simp only [hl, hcb, Bool.false_eq_true, if_false, Bool.or_eq_true, Bool.and_eq_true,
          xLinkOk, xXferOk, beq_iff_eq] at h
        rcases h with ⟨-, -, h⟩ | ⟨h, -⟩ <;> exact h
  · have : xGuard z ctl = ctl := by simp [xGuard, hl]
    rw [this]; exact trb_ok hz h

/-- 16 bytes of an input context the kernel writes touch only a transfer ring. -/
theorem ctx_ok {j : Nat} {cs : List Cap} {z lo hi : Nat} (h : xCtxOk z lo hi = true) :
    ∀ a ∈ Model.inputUnit z lo hi, XOk j cs a := by
  unfold xCtxOk at h
  dsimp only at h
  obtain ⟨h14, h5⟩ := Bool.and_eq_true_iff.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, ltB_eq, decide_eq_true_eq, xInputs, pageSize] at h14
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h14
  intro a ha
  unfold Model.inputUnit at ha
  dsimp only at ha
  rw [if_neg (by simp only [xInputs]; omega)] at ha
  split at h5
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, pageSize] at hc
    rw [if_pos hc, intr_eq] at ha
    simp only [beq_iff_eq] at h5
    rw [h5] at ha
    exact absurd ha (by simp)
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, pageSize] at hc
    rw [if_neg hc] at ha
    split at h5
    · rename_i hc2
      simp only [Bool.and_eq_true, beq_iff_eq, pageSize, Nat.ble_eq] at hc2
      rw [if_pos hc2] at ha
      simp only [Bool.and_eq_true, beq_iff_eq, ltB_eq, decide_eq_true_eq, xInRings, Nat.ble_eq] at h5
      obtain ⟨⟨hs, hd⟩, hlo, hhi⟩ := h5
      rw [if_neg (by simp only [ne_eq, Decidable.not_not]; omega)] at ha
      rw [mem_one] at ha; subst ha
      simp only [XOk, XAllowed, Model.ptr16]
      xlits
      omega
    · rename_i hc2
      simp only [Bool.and_eq_true, beq_iff_eq, pageSize, Nat.ble_eq] at hc2
      rw [if_neg hc2] at ha
      exact absurd ha not_mem_nil'

/-- A register write the kernel passes on touches only the command ring (CRCR) or the event
ring (ERDP). -/
theorem reg_ok {j : Nat} {cs : List Cap} {reg v : Nat} (h : xWriteOk reg v = true) :
    ∀ a ∈ Model.regWrite reg v, XOk j cs a := by
  unfold xWriteOk at h
  dsimp only at h
  simp only [xSpace, xOff, ltB_eq, xInCmd, xInEvents, xPorts, xSlots] at h
  intro a ha
  unfold Model.regWrite at ha
  simp only [Nat.reducePow] at ha
  repeat' split at h
  all_goals (try (exfalso; simp at h; done))
  all_goals (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    Nat.ble_eq] at *)
  all_goals (repeat' split at ha)
  all_goals first
    | exact absurd ha not_mem_nil'
    | (rw [mem_one] at ha; subst ha
       simp only [XOk, XAllowed, Model.ptr16]
       xlits
       first
        | (exfalso; omega)
        | exact ⟨by omega, by omega, by omega⟩
        | exact ⟨by omega, by omega⟩
        | (exfalso; revert h; split <;> (try split) <;> simp_all <;> omega))

theorem acc_ret (s : KState) (t : Task) (r : List Nat) : xAccesses (ret s t r) = .nil := rfl
theorem acc_xReply (s : KState) (t : Task) (op a b c d : Nat) :
    xAccesses (xReply s t op a b c d) = xAccessesOf op a b c d := rfl

/-- `run` points the controller at the DCBAA, the start of the command ring, the ERST and the
start of the event ring. -/
theorem run_ok {j : Nat} {cs : List Cap} :
    ∀ a ∈ xAccessesOf 3 xDcbaa (xCmd + 1) xErst xEvents, XOk j cs a := by
  intro a ha
  simp only [xAccessesOf, Nat.reduceEqDiff, if_false, if_true, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp only [XOk, XAllowed, Model.ptr16] <;> xlits <;>
    first | omega | decide

/-- **What `xhci` asks of the controller.** Every system call `xhci` makes the machine layer
write for the controller makes it touch only what `XOk` allows for the caller: a data buffer
in a run of the caller's own frames it holds writable and in one it holds readable, or the
right part of the xHCI memory. -/
theorem sysXhci_ok (s : KState) (t : Task) (ci op x y z : Nat) :
    ∀ a ∈ xAccesses (sysXhci s t ci op x y z), XOk s.cur t.caps a := by
  unfold sysXhci
  split
  · simp [acc_ret]
  split
  · split
    · split
      · rw [acc_xReply]; simp [xAccessesOf]
      · simp [acc_ret]
    split
    · simp [acc_ret]
    split
    · split
      · rename_i hw; rw [acc_xReply]; simpa [xAccessesOf] using reg_ok hw
      · simp [acc_ret]
    split
    · rw [acc_xReply]; exact run_ok
    split
    · dsimp only
      split
      · rename_i hok
        simp only [Bool.and_eq_true, ltB_eq, decide_eq_true_eq] at hok
        obtain ⟨hz, hok⟩ := hok
        rw [acc_xReply]
        have hc : y / 4294967296 % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
        have hg : xGuard z (y / 4294967296 % 4294967296) < 4294967296 := by
          unfold xGuard; split
          · exact hc
          · split <;> simp only [tNoOpCmd, tNoOp] <;> omega
        have e1 : (y / 4294967296 % 4294967296 + xGuard z (y / 4294967296 % 4294967296) * 4294967296)
            % 2 ^ 32 = y / 4294967296 % 4294967296 := by omega
        have e2 : (y / 4294967296 % 4294967296 + xGuard z (y / 4294967296 % 4294967296) * 4294967296)
            / 2 ^ 32 = xGuard z (y / 4294967296 % 4294967296) := by omega
        simp only [xAccessesOf, Nat.reduceEqDiff, if_false, if_true, e1, e2]
        intro a ha
        rcases mem_app.1 ha with ha | ha
        · exact trb_ok hz hok a ha
        · exact guard_ok hz hok a ha
      · simp [acc_ret]
    split
    · split
      · rename_i hok
        rw [acc_xReply]
        simp only [xAccessesOf, Nat.reduceEqDiff, if_false, if_true, Nat.le_add_right,
          Nat.add_sub_cancel_left]
        exact ctx_ok hok
      · simp [acc_ret]
    split
    · split
      · rw [acc_xReply]; simp [xAccessesOf]
      · simp [acc_ret]
    · simp [acc_ret]
  · simp [acc_ret]

/-! ## Every step -/

/-- Only `xhci` asks anything of the xHCI controller. -/
theorem runCall_xhci {s : KState} {t : Task} {num a0 a1 a2 a3 a4 : Nat}
    (h : (runCall s t num a0 a1 a2 a3 a4).xhciOp ≠ 0) :
    runCall s t num a0 a1 a2 a3 a4 = sysXhci s t a0 a1 a2 a3 a4 := by
  unfold runCall at h ⊢
  split at h
  all_goals first
    | rfl
    | (exfalso; apply h
       first
        | rfl
        | (first
            | unfold sysWrite | unfold sysMap | unfold sysUnmap | unfold sysDerive
            | unfold sysCapInfo | unfold sysSend | unfold sysRecv | unfold sysReply
            | unfold sysIrqWait | unfold sysIrqAck | unfold sysBootInfo | unfold sysStart
            | unfold sysDrop | unfold sysBlock | unfold sysSleep | unfold sysPower
            | unfold sysBoard | unfold sysStop | unfold sysSetWall | unfold sysTime
           repeat' (first | split | dsimp only)
           all_goals rfl)
        | (unfold sysUsb usbReply
           split
           · rfl
           · split
             all_goals first
               | rfl
               | simp only [apply_ite Reply.xhciOp, ret, ite_self]))

theorem xhci_pos {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).xhciOp ≠ 0) :
    ∃ t, nth? s.tasks s.cur = some t ∧ syscall s num a0 a1 a2 a3 a4 = sysXhci s t a0 a1 a2 a3 a4 := by
  unfold syscall at *
  split at *
  · exact absurd rfl h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    split at *
    · exact runCall_xhci h
    · exact absurd rfl h

/-- **Only the USB driver reaches the xHCI controller**, through the USB capability that
only it holds. -/
theorem only_usb_driver_drives_xhci {s : KState} (hr : Reachable s) {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).xhciOp ≠ 0) : s.cur = usbTask := by
  obtain ⟨t, ht, heq⟩ := xhci_pos h
  rw [heq] at h
  unfold sysXhci at h
  split at h
  · exact absurd rfl h
  · rename_i c hc
    split at h
    · rename_i hu
      obtain ⟨c0, hc0, ho⟩ := ((reachable_inv hr).tasks _ t ht).caps c (nth?_mem hc) |>.usb hu
      have hj := (reachable_inv hr).lt ht
      have := manifestAll_spec (p := fun j c => match c.obj with
        | .usbHost => j == usbTask
        | _ => true) (by decide) hj hc0
      simpa [ho] using this
    · exact absurd rfl h

/-! ## The xHCI memory is the driver's, and read-only to it -/

/-- A frame of the xHCI memory. -/
def XhciFrame (f : Nat) : Prop := xhciFirst ≤ f ∧ f < xhciFirst + xhciPages

/-- **Only the kernel writes the xHCI memory.** In every reachable state, a task that holds
a capability to a frame of the xHCI memory is the USB driver, and holds it without the write
right: the manifest gives only the driver those frames, and only read-only (`xhciCap`);
nobody can pass memory to it that it did not have, and derive never adds a right. -/
theorem xhci_region_readonly {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f)
    (hx : XhciFrame f) : j = usbTask ∧ c.rights.w = false := by
  obtain ⟨hr, c0, hc0, hcov, hle⟩ := frame_flow h ht hc hf
  have ho : owner f = usbTask := by
    unfold XhciFrame at hx
    simp only [xhciFirst, xhciPages, framesPerTask, usbTask] at hx
    have hp : f < poolFrames := by simp only [poolFrames, framesPerTask, maxTasks]; omega
    unfold owner; rw [if_pos hp]
    simp only [framesPerTask, usbTask]; omega
  rw [ho] at hr hc0
  refine ⟨?_, ?_⟩
  · rcases reach_iff hr with h' | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩
    · exact h'.symm
    all_goals simp [App, FsClient, NetClient, usbTask] at h'
  · obtain ⟨b, n, hbn, h1, h2⟩ := hcov
    have := manifestAll_spec (p := fun _ c => match c.obj with
      | .frames b n => !c.rights.w || Nat.ble (b + n) xhciFirst || Nat.ble (xhciFirst + xhciPages) b
      | _ => true) (by decide) (by decide : usbTask < numTasks) hc0
    simp only [hbn, Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq] at this
    unfold XhciFrame at hx
    cases hw : c.rights.w
    · rfl
    · have := hle.2.1 hw
      simp only [this, Bool.true_eq_false, false_or] at *
      omega

/-- So the USB driver maps the xHCI memory only read-only, and nobody else maps it at all. -/
theorem xhci_maps_readonly {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {m : Mapping} (hm : m ∈ t.maps) (hx : XhciFrame m.frame) :
    j = usbTask ∧ m.rights.w = false := by
  obtain ⟨c, hc, hf, hr⟩ := maps_backed h ht m hm
  rw [← hr]
  exact xhci_region_readonly h ht hc hf hx

/-! ## The theorems -/

theorem xAccessesOf_zero (a b c d : Nat) : xAccessesOf 0 a b c d = .nil := rfl

/-- A data buffer the kernel checked, in a run of the USB driver's own frames that it holds
writable, is the driver's own memory, outside the xHCI memory. -/
theorem data_allowed {s : KState} (hr : Reachable s) {t : Task} (ht : nth? s.tasks usbTask = some t)
    {a n : Nat} (h : XOk usbTask t.caps (.data a n)) : XAllowed (.data a n) := by
  obtain ⟨⟨c, hc, b, k, ho, hown1, hown2, hpool, hlo, hhi, hw⟩, -⟩ := h
  intro x hx1 hx2
  have hf : Covers c ((x - frameBase) / pageSize) :=
    ⟨b, k, ho, by simp only [pageSize, frameBase] at *; omega, by simp only [pageSize, frameBase] at *; omega⟩
  refine ⟨by simp only [pageSize, frameBase] at *; omega, ?_, ?_⟩
  · have hf1 : framesPerTask * usbTask ≤ (x - frameBase) / pageSize := by
      simp only [pageSize, frameBase, framesPerTask, usbTask] at *; omega
    have hf2 : (x - frameBase) / pageSize < framesPerTask * (usbTask + 1) := by
      simp only [pageSize, frameBase, framesPerTask, usbTask] at *; omega
    unfold owner
    rw [if_pos (by simp only [pageSize, frameBase, framesPerTask, usbTask, poolFrames, maxTasks] at *; omega)]
    simp only [framesPerTask, usbTask] at hf1 hf2 ⊢
    omega
  · intro hin
    have hx : XhciFrame ((x - frameBase) / pageSize) := by
      unfold InXhci at hin; unfold XhciFrame
      simp only [xhciBase, xhciFirst, xhciPages, pageSize, frameBase, framesPerTask, usbTask] at *
      omega
    have := (xhci_region_readonly hr ht hc hf hx).2
    rw [hw] at this; exact absurd this (by decide)

/-- **The xHCI controller only ever touches the USB driver's own memory.** In every
reachable state, whatever system call a task makes, everything it asks the machine layer
to write for the xHCI controller (a TRB and the guard written before it, 16 bytes of an
input context, a register, the DMA bases of `run`) makes the controller touch, by the
specification's model, only a data buffer in the USB driver's own frames outside the xHCI
memory, or the part of the xHCI memory where that structure belongs. -/
theorem xhci_dma_own_memory {s : KState} (hr : Reachable s) (num a0 a1 a2 a3 a4 : Nat) :
    ∀ a ∈ xAccesses (syscall s num a0 a1 a2 a3 a4), XAllowed a := by
  by_cases h0 : (syscall s num a0 a1 a2 a3 a4).xhciOp = 0
  · intro a ha
    unfold xAccesses at ha
    rw [h0, xAccessesOf_zero] at ha
    exact absurd ha not_mem_nil'
  · have hcur := only_usb_driver_drives_xhci hr h0
    obtain ⟨t, ht, heq⟩ := xhci_pos h0
    rw [heq]
    intro a ha
    have hok := sysXhci_ok s t a0 a1 a2 a3 a4 a ha
    rw [hcur] at hok ht
    cases a with
    | data a n => exact data_allowed hr ht hok
    | _ => exact hok

/-- What each kind of xHCI request carries, as the kernel checked it. -/
def XReq (j : Nat) (cs : List Cap) (op a b c d : Nat) : Prop :=
  op = 0 ∨ op = 1 ∨ (op = 2 ∧ xWriteOk a b = true) ∨
    (op = 3 ∧ a = xDcbaa ∧ b = xCmd + 1 ∧ c = xErst ∧ d = xEvents) ∨
    (op = 4 ∧ ∃ z, z < xTrbs ∧ a = xTrbAddr z ∧ c < 2 ^ 32 ∧ xTrbOk j cs z b c (d % 2 ^ 32) = true ∧
      d / 2 ^ 32 = xGuard z (d % 2 ^ 32)) ∨
    (op = 5 ∧ ∃ z, xCtxOk z b c = true ∧ a = xIn + z) ∨
    (op = 6 ∧ b ≤ 2 ^ 20 ∧ xDataOk j cs a b = true)

theorem sysXhci_req (s : KState) (t : Task) (ci op x y z : Nat) :
    let r := sysXhci s t ci op x y z
    XReq s.cur t.caps r.xhciOp r.usbA r.usbB r.usbC r.usbD := by
  unfold sysXhci
  split
  · exact Or.inl rfl
  split
  · split
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    split
    · exact Or.inl rfl
    split
    · split
      · rename_i hw; exact Or.inr (Or.inr (Or.inl ⟨rfl, hw⟩))
      · exact Or.inl rfl
    split
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    split
    · dsimp only
      split
      · rename_i hok
        simp only [Bool.and_eq_true, ltB_eq, decide_eq_true_eq] at hok
        obtain ⟨hz, hok⟩ := hok
        have hc : y / 4294967296 % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
        have hg : xGuard z (y / 4294967296 % 4294967296) < 4294967296 := by
          unfold xGuard; split
          · exact hc
          · split <;> simp only [tNoOpCmd, tNoOp] <;> omega
        have e1 : (y / 4294967296 % 4294967296 + xGuard z (y / 4294967296 % 4294967296) * 4294967296)
            % 2 ^ 32 = y / 4294967296 % 4294967296 := by omega
        have e2 : (y / 4294967296 % 4294967296 + xGuard z (y / 4294967296 % 4294967296) * 4294967296)
            / 2 ^ 32 = xGuard z (y / 4294967296 % 4294967296) := by omega
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, z, hz, rfl, ?_, ?_, ?_⟩))))
        · exact Nat.mod_lt _ (by decide)
        · show xTrbOk _ _ z x _ ((y / 4294967296 % 4294967296 + _ * 4294967296) % 2 ^ 32) = true
          rw [e1]; exact hok
        · show (y / 4294967296 % 4294967296 + _ * 4294967296) / 2 ^ 32 =
            xGuard z ((y / 4294967296 % 4294967296 + _ * 4294967296) % 2 ^ 32)
          rw [e2, e1]
      · exact Or.inl rfl
    split
    · split
      · rename_i hok; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, z, hok, rfl⟩)))))
      · exact Or.inl rfl
    split
    · split
      · rename_i hok
        simp only [Bool.and_eq_true, ltB_eq, decide_eq_true_eq] at hok
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, show y ≤ 2 ^ 20 by omega, hok.2⟩)))))
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **The machine layer writes only the kernel's parts of the xHCI memory.** A TRB goes to a
slot of the command ring or of the transfer rings, and 16 bytes of an input context to the
input contexts, 16-byte aligned: never to the DCBAA, the scratchpad array, the ERST, the
event ring, the device contexts or the scratchpad pages, and never outside the xHCI
memory. -/
theorem xhci_writes_in_memory (s : KState) (num a0 a1 a2 a3 a4 : Nat)
    (h : (syscall s num a0 a1 a2 a3 a4).xhciOp = 4 ∨ (syscall s num a0 a1 a2 a3 a4).xhciOp = 5) :
    let a := (syscall s num a0 a1 a2 a3 a4).usbA
    a % 16 = 0 ∧ ((xCmd ≤ a ∧ a < xCmd + 16 * xCmdTrbs) ∨ (xRings ≤ a ∧ a < xRings + 16 * xRingTrbs) ∨
      (xIn ≤ a ∧ a < xIn + xInputs * pageSize)) := by
  have h0 : (syscall s num a0 a1 a2 a3 a4).xhciOp ≠ 0 := by omega
  obtain ⟨t, _, heq⟩ := xhci_pos h0
  rw [heq] at h ⊢
  have hq := sysXhci_req s t a0 a1 a2 a3 a4
  dsimp only at hq ⊢
  generalize sysXhci s t a0 a1 a2 a3 a4 = r at h hq ⊢
  rcases hq with h' | h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, z, hz, ha, -⟩ | ⟨-, z, hok, ha⟩ | ⟨h', -⟩ <;>
    try (rw [h'] at h; simp at h)
  · rw [ha]; unfold xTrbAddr; xlits
    split <;> omega
  · rw [ha]
    unfold xCtxOk at hok; dsimp only at hok
    obtain ⟨h14, -⟩ := Bool.and_eq_true_iff.mp hok
    simp only [Bool.and_eq_true, beq_iff_eq, ltB_eq, decide_eq_true_eq] at h14
    xlits; omega

/-- **Cache maintenance only covers the driver's own memory.** When `xhci` asks the machine
layer to clean and invalidate a range of memory (before a transfer, and after one before
the driver reads what came in), the range is at most 1 MiB of the USB driver's own frames,
outside the xHCI memory. -/
theorem xhci_sync_own_memory {s : KState} (hr : Reachable s) {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).xhciOp = 6) :
    (syscall s num a0 a1 a2 a3 a4).usbB ≤ 2 ^ 20 ∧
      XAllowed (.data (syscall s num a0 a1 a2 a3 a4).usbA (syscall s num a0 a1 a2 a3 a4).usbB) := by
  have h0 : (syscall s num a0 a1 a2 a3 a4).xhciOp ≠ 0 := by omega
  have hcur := only_usb_driver_drives_xhci hr h0
  obtain ⟨t, ht, heq⟩ := xhci_pos h0
  rw [heq] at h ⊢
  have hq := sysXhci_req s t a0 a1 a2 a3 a4
  dsimp only at hq
  rw [hcur] at hq ht
  rcases hq with h' | h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, hb, hok⟩ <;>
    try (rw [h'] at h; simp at h)
  exact ⟨hb, data_allowed hr ht (xDataOk_spec hok)⟩

/-- **A TRB half written touches nothing.** The machine layer writes a TRB's control word
last, and first the guard the kernel returns with it. Away from the last slot of each
ring, the guard is a No-Op, so whatever the controller reads in the slot meanwhile (the old
TRB's parameter and status, the new one's, or a mix of the two) touches nothing, as long as
a transfer TRB reports to interrupter 0, as every one the kernel writes does. The last slot
of each ring only ever holds the Link TRB back to its ring's start (as from boot): only its
control word changes. -/
theorem xhci_guard_safe (s : KState) (num a0 a1 a2 a3 a4 : Nat)
    (h : (syscall s num a0 a1 a2 a3 a4).xhciOp = 4) :
    let r := syscall s num a0 a1 a2 a3 a4
    (r.usbA = xCmd + 16 * (xCmdTrbs - 1) ∧ r.usbB = xCmd ∧ r.usbC = 0) ∨
    (r.usbA = xRings + 16 * (xRingTrbs - 1) ∧ r.usbB = xRings ∧ r.usbC = 0) ∨
    (∀ p st, (r.usbA < xCmd + 16 * xCmdTrbs ∨ Model.intrTarget st = 0) →
      Model.trbAt r.usbA p st (r.usbD / 2 ^ 32) = .nil) := by
  have h0 : (syscall s num a0 a1 a2 a3 a4).xhciOp ≠ 0 := by omega
  obtain ⟨t, _, heq⟩ := xhci_pos h0
  rw [heq] at h ⊢
  have hq := sysXhci_req s t a0 a1 a2 a3 a4
  dsimp only at hq ⊢
  generalize sysXhci s t a0 a1 a2 a3 a4 = r at h hq ⊢
  rcases hq with h' | h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, z, hz, ha, -, hok, hg⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;>
    try (rw [h'] at h; simp at h)
  rw [ha, hg]
  cases hl : xLast z
  · right; right
    intro p st hi
    apply guard_noop hz hl
    rcases hi with hi | hi
    · left; unfold xTrbAddr at hi; xlits; split at hi <;> omega
    · exact Or.inr hi
  · unfold xTrbOk at hok; dsimp only at hok
    rw [hl, if_pos rfl] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨-, hp⟩, hs⟩ := hok
    simp only [xLast, Bool.or_eq_true, beq_iff_eq] at hl
    unfold xTrbAddr
    xlits
    rcases hl with hl | hl
    · left; refine ⟨by rw [if_pos (by omega)]; omega, ?_, hs⟩
      rw [hp]; simp only [ltB_eq, decide_eq_true_eq]; rw [if_pos (by omega)]
    · right; left; refine ⟨by rw [if_neg (by omega)]; omega, ?_, hs⟩
      rw [hp]; simp only [ltB_eq, decide_eq_true_eq]; rw [if_neg (by omega)]

/-! ## What the xHCI memory holds from boot -/

/-- Evaluates `xhciBoot` at an index given as arithmetic: every condition that does not hold
is refuted, and the one that does is taken. -/
macro "boot_eval" : tactic => `(tactic| ((unfold xhciBoot) <;> (repeat' split) <;>
  first | (exfalso; simp only [xCmdTrbs, xRingTrbs, xInputs] at *; omega) | rfl))

theorem boot_cmd {k : Nat} (hk : k + 1 < xCmdTrbs) :
    xhciBoot (3 * 512 + 2 * k) = 0 ∧ xhciBoot (3 * 512 + 2 * k + 1) = 0 := by
  exact ⟨by boot_eval, by boot_eval⟩

theorem boot_ring {m : Nat} (hm : m + 1 < xRingTrbs) :
    xhciBoot (48 * 512 + 2 * m) = 0 ∧ xhciBoot (48 * 512 + 2 * m + 1) = 0 := by
  exact ⟨by boot_eval, by boot_eval⟩

theorem boot_input_lo {q c u : Nat} (hq : q < xInputs) (hc : c < 33) (hu : u < 2) :
    xhciBoot (32 * 512 + q * 512 + c * 8 + u * 2) = 0 := by
  boot_eval

theorem boot_input_hi {q c u : Nat} (hq : q < xInputs) (hc : c < 33) (hu : u < 2) :
    xhciBoot (32 * 512 + q * 512 + c * 8 + u * 2 + 1) = if 2 ≤ c ∧ u = 0 then xRings else 0 := by
  split
  · boot_eval
  · boot_eval

/-- **What the xHCI memory holds from boot is safe.** Every entry of the DCBAA leads to the
scratchpad array (entry 0) or to a device context; every entry of the scratchpad array to
a scratchpad page; the ERST's entry to the event ring, all of it; every TRB slot of the
command ring and the transfer rings, as it is from boot (0, but for the Link TRB at the end
of each ring), touches nothing but its own ring; and every 16 bytes of every input context
touch at most the transfer rings. So the controller, pointed at these by `run`, finds only
what `XAllowed` allows even where nothing has been written yet. -/
theorem xhci_boot_ok :
    XAllowed (.table (xhciBoot 0) (256 * 8)) ∧
    (∀ i, 1 ≤ i → i < 256 → XAllowed (.device (xhciBoot i))) ∧
    (∀ k, k < 256 → XAllowed (.scratch (xhciBoot (256 + k)))) ∧
    XAllowed (.events (xhciBoot 512) (16 * (xhciBoot 513 % 2 ^ 16))) ∧
    (∀ k, k < xCmdTrbs → ∀ a ∈ Model.trbAt (xCmd + 16 * k) (xhciBoot (3 * 512 + 2 * k))
        (xhciBoot (3 * 512 + 2 * k + 1) % 2 ^ 32) (xhciBoot (3 * 512 + 2 * k + 1) / 2 ^ 32), XAllowed a) ∧
    (∀ m, m < xRingTrbs → ∀ a ∈ Model.trbAt (xRings + 16 * m) (xhciBoot (48 * 512 + 2 * m))
        (xhciBoot (48 * 512 + 2 * m + 1) % 2 ^ 32) (xhciBoot (48 * 512 + 2 * m + 1) / 2 ^ 32), XAllowed a) ∧
    (∀ q c u, q < xInputs → c < 33 → u < 2 →
      ∀ a ∈ Model.inputUnit (q * 4096 + c * 64 + u * 16) (xhciBoot (32 * 512 + q * 512 + c * 8 + u * 2))
        (xhciBoot (32 * 512 + q * 512 + c * 8 + u * 2 + 1)), XAllowed a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · right; left; exact ⟨by decide, by decide⟩
  · intro i h1 h2
    have : xhciBoot i = xOut + (i - 1) % xSlots * pageSize := by
      unfold xhciBoot; rw [if_pos h2, if_neg (by omega)]
    rw [this]; exact ⟨(i - 1) % xSlots, Nat.mod_lt _ (by decide), rfl⟩
  · intro k hk
    have : xhciBoot (256 + k) = xScratch + k % xScratchPages * pageSize := by
      unfold xhciBoot; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    rw [this]; exact ⟨k % xScratchPages, Nat.mod_lt _ (by decide), rfl⟩
  · have e1 : xhciBoot 512 = xEvents := by unfold xhciBoot; simp
    have e2 : xhciBoot 513 = xEventTrbs := by unfold xhciBoot; simp
    rw [e1, e2]; exact ⟨Nat.le_refl _, by decide⟩
  · intro k hk a ha
    have hA : xCmd + 16 * k = xTrbAddr k := by simp [xTrbAddr, hk]
    rw [hA, trbAt_cmd hk] at ha
    by_cases hl : k + 1 < xCmdTrbs
    · obtain ⟨e1, e2⟩ := boot_cmd hl
      rw [e1, e2] at ha
      simp [Model.commandTrb, Model.trbType] at ha
    · have hk' : k = 255 := by simp only [xCmdTrbs] at hk hl; omega
      subst hk'
      have e1 : xhciBoot (3 * 512 + 2 * 255) = xCmd := by unfold xhciBoot; simp [xCmdTrbs]
      have e2 : xhciBoot (3 * 512 + 2 * 255 + 1) = (tLink * 1024 + 2) * 4294967296 := by
        unfold xhciBoot; simp [xCmdTrbs]
      have e3 : (tLink * 1024 + 2) * 4294967296 % 2 ^ 32 = 0 := by decide
      have e4 : (tLink * 1024 + 2) * 4294967296 / 2 ^ 32 = 6146 := by decide
      have e5 : Model.trbType 6146 = 6 := by decide
      rw [e1, e2, e3, e4] at ha
      simp only [Model.commandTrb, e5, if_true, Model.intrTarget, Nat.zero_div, Nat.zero_mod,
        ne_eq, not_true_eq_false, if_false, mem_one] at ha
      subst ha
      simp only [XAllowed]; decide
  · intro m hm a ha
    have hm2 : m + xCmdTrbs < xTrbs := by simp only [xTrbs, xCmdTrbs, xRingTrbs] at hm ⊢; omega
    have hA : xRings + 16 * m = xTrbAddr (m + xCmdTrbs) := by
      unfold xTrbAddr; rw [if_neg (by omega), Nat.add_sub_cancel]
    rw [hA, trbAt_ring (by omega) hm2] at ha
    by_cases hl : m + 1 < xRingTrbs
    · obtain ⟨e1, e2⟩ := boot_ring hl
      rw [e1, e2] at ha
      simp [Model.transferTrb, Model.trbType, Model.intrTarget] at ha
    · have hm' : m = 4095 := by simp only [xRingTrbs] at hm hl; omega
      subst hm'
      have e1 : xhciBoot (48 * 512 + 2 * 4095) = xRings := by unfold xhciBoot; simp [xCmdTrbs, xRingTrbs]
      have e2 : xhciBoot (48 * 512 + 2 * 4095 + 1) = (tLink * 1024 + 2) * 4294967296 := by
        unfold xhciBoot; simp [xCmdTrbs, xRingTrbs]
      have e3 : (tLink * 1024 + 2) * 4294967296 % 2 ^ 32 = 0 := by decide
      have e4 : (tLink * 1024 + 2) * 4294967296 / 2 ^ 32 = 6146 := by decide
      have e5 : Model.trbType 6146 = 6 := by decide
      rw [e1, e2, e3, e4] at ha
      simp only [Model.transferTrb, e5, Model.intrTarget, Nat.zero_div, Nat.zero_mod,
        ne_eq, not_true_eq_false, if_false, if_true] at ha
      simp at ha
      subst ha
      simp only [XAllowed]; decide
  · intro q c u hq hc hu a ha
    have hi := boot_input_hi hq hc hu
    rw [boot_input_lo hq hc hu] at ha
    unfold Model.inputUnit at ha
    dsimp only at ha
    have hcz : (q * 4096 + c * 64 + u * 16) % 4096 / 64 = c := by omega
    have huz : (q * 4096 + c * 64 + u * 16) % 64 / 16 = u := by omega
    have hin : ¬ (q * 4096 + c * 64 + u * 16 ≥ xInputs * 4096 ∨ (q * 4096 + c * 64 + u * 16) % 16 ≠ 0 ∨
        (q * 4096 + c * 64 + u * 16) % 64 / 16 ≥ 2 ∨ (q * 4096 + c * 64 + u * 16) % 4096 / 64 ≥ 33) := by
      simp only [xInputs] at hq ⊢; omega
    rw [if_neg hin, hcz, huz] at ha
    by_cases h2 : 2 ≤ c ∧ u = 0
    · rw [if_pos h2] at hi
      rw [hi, if_neg (by omega), if_pos h2] at ha
      simp only [Nat.zero_div, Nat.zero_mod, ne_eq, not_true_eq_false, if_false, mem_one] at ha
      subst ha
      simp only [XAllowed]; decide
    · rw [if_neg h2] at hi
      rw [hi] at ha
      by_cases h1 : c = 1 ∧ u = 0
      · rw [if_pos h1] at ha
        simp [Model.intrTarget] at ha
      · rw [if_neg h1, if_neg h2] at ha
        exact absurd ha not_mem_nil'

/-! ## The checks let a driver do its work

The theorems say what the kernel refuses; these say that what a keyboard driver needs gets
through: a transfer into its spare run, a control transfer's Setup Stage, the commands that
address and configure a device, an endpoint context, the command ring, the event ring and a
doorbell. And that a buffer in the xHCI memory itself, Run/Stop, DCBAAP and a stream are
refused. -/

/-- A buffer in the USB driver's spare run, 4 KiB in (frame 256 × 17 + 29). -/
def exampleBuf : Nat := frameBase + (256 * 17 + 29) * pageSize

example : xTrbOk usbTask (initCaps usbTask) 300 exampleBuf 8 (tNormal * 1024 + 1) = true := rfl
example : xTrbOk usbTask (initCaps usbTask) 300 0x0100000680 8 (tSetup * 1024 + 64 + 1) = true := rfl
example : xTrbOk usbTask (initCaps usbTask) 301 exampleBuf 18 (tData * 1024 + 65536 + 1) = true := rfl
example : xTrbOk usbTask (initCaps usbTask) 3 xIn 0 (tAddress * 1024 + 1 * 16777216 + 1) = true := rfl
example : xTrbOk usbTask (initCaps usbTask) 4 (xIn + pageSize) 0 (tConfigure * 1024 + 1 * 16777216 + 1) = true := rfl
example : xTrbOk usbTask (initCaps usbTask) 255 xCmd 0 (tLink * 1024 + 2 + 1) = true := rfl
example : xCtxOk (2 * 64) 0 (xRings + 1) = true := rfl
example : xWriteOk (1 * 65536 + 0x18) (xCmd + 1) = true := rfl
example : xWriteOk (2 * 65536 + 0x38) (xEvents + 16 + 8) = true := rfl
example : xWriteOk (3 * 65536 + 4) 3 = true := rfl
example : xTrbOk usbTask (initCaps usbTask) 300 xRings 8 (tNormal * 1024 + 1) = false := rfl
example : xWriteOk (1 * 65536) 1 = false := rfl
example : xWriteOk (1 * 65536 + 0x30) xDcbaa = false := rfl
example : xWriteOk (3 * 65536 + 4) (65536 + 3) = false := rfl

end LeanOS
