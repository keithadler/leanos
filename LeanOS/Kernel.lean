/-
The kernel's decisions, written in Lean and compiled into the running kernel.

Everything that decides *who may touch what* lives here: capabilities, address-space
mappings, system calls, and the scheduler. The C and assembly underneath (arch/) only
carry out what this file returns: they write page tables, switch registers, and print
bytes. The theorems about these definitions are in `LeanOS/Proofs.lean`, and they are
about exactly this code, because this code is what runs.

This module is a `prelude` module that imports only `Init.Core`, so the compiled kernel
carries six small pieces of Lean's standard library and nothing that needs an operating
system underneath it.
-/
prelude
import Init.Core

namespace LeanOS

/-! ## Rights and capabilities -/

/-- What a capability allows: read, write, execute. -/
structure Rights where
  r : Bool
  w : Bool
  x : Bool

namespace Rights

/-- The rights both `a` and `b` allow. Deriving a capability goes through this, so a
derived capability can never allow more than its parent. -/
def meet (a b : Rights) : Rights := ⟨a.r && b.r, a.w && b.w, a.x && b.x⟩

/-- Rights from the bits a user program passes: 1 = read, 2 = write, 4 = execute. -/
def ofBits (n : Nat) : Rights := ⟨n % 2 == 1, n / 2 % 2 == 1, n / 4 % 2 == 1⟩

def toBits (a : Rights) : Nat :=
  (if a.r then 1 else 0) + (if a.w then 2 else 0) + (if a.x then 4 else 0)

def rx : Rights := ⟨true, false, true⟩
def rw : Rights := ⟨true, true, false⟩

end Rights

/-- A capability names one physical 4 KiB frame and what its holder may do with it. -/
structure Cap where
  frame : Nat
  rights : Rights

/-- One page of a task's address space: virtual page `vpn` shows physical `frame`. -/
structure Mapping where
  vpn : Nat
  frame : Nat
  rights : Rights

structure Task where
  caps : List Cap
  maps : List Mapping
  alive : Bool

structure KState where
  tasks : List Task
  cur : Nat

/-! ## List helpers

Written out here instead of taken from the standard library (which also brings the `[a, b]`
list notation this module goes without), so the compiled kernel stays small and the proofs reason about definitions that are visible in this file. -/

def nth? {α : Type} : List α → Nat → Option α
  | .nil, _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nth? l n

def setNth {α : Type} : List α → Nat → α → List α
  | .nil, _, _ => .nil
  | _ :: l, 0, v => v :: l
  | a :: l, n + 1, v => a :: setNth l n v

def snoc {α : Type} : List α → α → List α
  | .nil, v => v :: .nil
  | a :: l, v => a :: snoc l v

def len {α : Type} : List α → Nat
  | .nil => 0
  | _ :: l => len l + 1

/-- Remove every mapping of virtual page `v`. -/
def dropVpn (v : Nat) : List Mapping → List Mapping
  | .nil => .nil
  | m :: ms => if m.vpn == v then dropVpn v ms else m :: dropVpn v ms

/-! ## The initial state -/

/-- Each task's user window is 512 pages (2 MiB) starting at virtual address `userBase`. -/
def userPages : Nat := 512
def userBase : Nat := 0x80000000
def pageSize : Nat := 4096

/-- The most a single `write` may print. -/
def maxWrite : Nat := 256

/-- A task may hold at most this many capabilities, so no task can grow kernel memory
without bound by deriving. -/
def maxCaps : Nat := 64

/-- Task `i` starts with four frames, `4i` to `4i+3`: code (read/execute), data, stack,
and a spare frame it holds a capability to but has not mapped. -/
def mkTask (i : Nat) : Task :=
  { caps := ⟨4 * i, Rights.rx⟩ :: ⟨4 * i + 1, Rights.rw⟩ :: ⟨4 * i + 2, Rights.rw⟩ ::
             ⟨4 * i + 3, Rights.rw⟩ :: .nil,
    maps := ⟨0, 4 * i, Rights.rx⟩ :: ⟨1, 4 * i + 1, Rights.rw⟩ :: ⟨511, 4 * i + 2, Rights.rw⟩ :: .nil,
    alive := true }

def mkTasksFrom (i : Nat) : Nat → List Task
  | 0 => .nil
  | k + 1 => mkTask i :: mkTasksFrom (i + 1) k

/-- At most this many tasks: the frame pool holds four frames for each. -/
def maxTasks : Nat := 4

def init (n : Nat) : KState := ⟨mkTasksFrom 0 (if n ≤ maxTasks then n else maxTasks), 0⟩

/-! ## Scheduling -/

def isAlive (ts : List Task) (i : Nat) : Bool :=
  match nth? ts i with
  | some t => t.alive
  | none => false

/-- The first live task at or after `i`, wrapping around, looking at most `fuel` tasks. -/
def findAlive (ts : List Task) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    let j := i % len ts
    if isAlive ts j then some j else findAlive ts (j + 1) fuel

/-- Round robin: the next live task after the current one, or the current one if it is the
only one alive. If none is alive, the state is unchanged and the machine idles. -/
def schedule (s : KState) : KState :=
  match findAlive s.tasks (s.cur + 1) (len s.tasks) with
  | some j => { s with cur := j }
  | none => s

/-- Stop the current task (it exited or faulted) and move on. -/
def killCurrent (s : KState) : KState :=
  match nth? s.tasks s.cur with
  | some t => schedule { s with tasks := setNth s.tasks s.cur { t with alive := false } }
  | none => schedule s

/-! ## System calls -/

/-- What the machine layer must do after a system call. -/
structure Reply where
  state : KState
  /-- 0 ok, 1 no such capability, 2 bad argument, 3 unknown call, 4 too many capabilities -/
  status : Nat
  value : Nat
  /-- print `outLen` bytes starting at user address `outVa` of the current task (0 = none).
  Only returned after checking every page of that range is mapped readable, so the machine
  layer can read it without faulting and without reading memory the task cannot. -/
  outVa : Nat
  outLen : Nat
  /-- the current task's mappings changed, so its page tables must be rebuilt -/
  remap : Bool
  /-- switch to the task `state.cur` names before returning to user mode -/
  resched : Bool

def okR (s : KState) (v : Nat) : Reply := ⟨s, 0, v, 0, 0, false, false⟩
def errR (s : KState) (code : Nat) : Reply := ⟨s, code, 0, 0, 0, false, false⟩
/-- Success; the current task's page tables must be rebuilt. -/
def okRemap (s : KState) : Reply := ⟨s, 0, 0, 0, 0, true, false⟩
/-- Success; `s.cur` may now name a different task. -/
def okSwitch (s : KState) : Reply := ⟨s, 0, 0, 0, 0, false, true⟩
/-- Success; print `n` bytes of the current task's memory starting at `va`. -/
def okPrint (s : KState) (va n : Nat) : Reply := ⟨s, 0, n, va, n, false, false⟩

def withTask (s : KState) (t : Task) : KState := { s with tasks := setNth s.tasks s.cur t }

/-- Map the frame named by capability `ci` at virtual page `vpn`, with that capability's
rights. The only way a task gains a mapping. -/
def sysMap (s : KState) (t : Task) (ci vpn : Nat) : Reply :=
  match nth? t.caps ci with
  | none => errR s 1
  | some c =>
    if vpn < userPages && c.rights.r then
      okRemap (withTask s { t with maps := ⟨vpn, c.frame, c.rights⟩ :: dropVpn vpn t.maps })
    else errR s 2

def sysUnmap (s : KState) (t : Task) (vpn : Nat) : Reply :=
  okRemap (withTask s { t with maps := dropVpn vpn t.maps })

/-- A new capability to the same frame with at most the rights asked for. Returns its index. -/
def sysDerive (s : KState) (t : Task) (ci bits : Nat) : Reply :=
  match nth? t.caps ci with
  | none => errR s 1
  | some c =>
    if len t.caps < maxCaps then
      okR (withTask s { t with caps := snoc t.caps ⟨c.frame, c.rights.meet (Rights.ofBits bits)⟩ })
        (len t.caps)
    else errR s 4

/-- Virtual page `v` is mapped with read rights. -/
def readableAt : List Mapping → Nat → Bool
  | .nil, _ => false
  | m :: ms, v => (m.vpn == v && m.rights.r) || readableAt ms v

/-- Pages `first` to `first + count - 1` are all mapped with read rights. -/
def allReadable (ms : List Mapping) (first : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => readableAt ms first && allReadable ms (first + 1) k

/-- Print `n` bytes from the task's own memory at `va`, if every page they touch is mapped
readable in the task's address space. -/
def sysWrite (s : KState) (t : Task) (va n : Nat) : Reply :=
  if n = 0 then okR s 0
  else if n ≤ maxWrite ∧ userBase ≤ va ∧
      allReadable t.maps ((va - userBase) / pageSize)
        ((va + n - 1 - userBase) / pageSize + 1 - (va - userBase) / pageSize) = true then
    okPrint s va n
  else errR s 2

def sysCapInfo (s : KState) (t : Task) (ci : Nat) : Reply :=
  match nth? t.caps ci with
  | none => errR s 1
  | some c => okR s c.rights.toBits

/-- System call `num` from the current task with arguments `a0`, `a1`.
  0 write(va, len) · 1 yield · 2 map(cap, vpn) · 3 unmap(vpn) · 4 derive(cap, rights)
  5 exit · 6 capinfo(cap) → rights · 7 whoami → task number -/
def syscall (s : KState) (num a0 a1 : Nat) : Reply :=
  match nth? s.tasks s.cur with
  | none => errR s 3
  | some t =>
    match num with
    | 0 => sysWrite s t a0 a1
    | 1 => okSwitch (schedule s)
    | 2 => sysMap s t a0 a1
    | 3 => sysUnmap s t a0
    | 4 => sysDerive s t a0 a1
    | 5 => okSwitch (killCurrent s)
    | 6 => sysCapInfo s t a0
    | 7 => okR s s.cur
    | _ => errR s 3

/-! ## The interface the machine layer calls

Exported functions take every argument owned (Lean does not allow borrowed arguments on
`@[export]`), so the C caller increments the reference count of anything it wants to keep
before passing it in. See `arch/lean_iface.h`. -/

@[export leanos_init] def exInit (n : Nat) : KState := init n
@[export leanos_syscall] def exSyscall (s : KState) (num a0 a1 : Nat) : Reply :=
  syscall s num a0 a1
@[export leanos_tick] def exTick (s : KState) : KState := schedule s
@[export leanos_fault] def exFault (s : KState) : KState := killCurrent s

@[export leanos_cur] def exCur (s : KState) : Nat := s.cur
@[export leanos_alive] def exAlive (s : KState) (i : Nat) : Bool := isAlive s.tasks i
@[export leanos_ntasks] def exNTasks (s : KState) : Nat := len s.tasks

def mapsOf (s : KState) (i : Nat) : List Mapping :=
  match nth? s.tasks i with
  | some t => t.maps
  | none => .nil

/-! ## Hardware translation tables

The kernel computes every word of every translation table the MMU reads; the machine
layer only stores them. The format is Armv8-A stage 1 with a 4 KiB granule and 39-bit
virtual addresses, so a walk reads one word from each of three levels: level 1 (1 GiB
per entry), level 2 (2 MiB) and level 3 (4 KiB pages). `LeanOS/Arm.lean` models how the
MMU reads these words, and `LeanOS/Tables.lean` proves what user mode can then reach.

Physical memory on the Pi 4: the first GiB of RAM holds the kernel, its heap and the
frame pool; the peripherals sit in the fourth GiB. -/

/-- Where the frame pool starts: frame `f` is at `framePA f`. -/
def frameBase : Nat := 0x04000000
def framePA (f : Nat) : Nat := frameBase + f * pageSize

/-- Descriptor fields. Every descriptor is a sum of these, each in its own bits. -/
def dValid : Nat := 1                   -- bit 0
def dTableOrPage : Nat := 2             -- bit 1: a table (levels 1–2) or a page (level 3)
def attrNormal : Nat := 1 * 4           -- AttrIndx = 1: normal write-back memory
def attrDevice : Nat := 0 * 4           -- AttrIndx = 0: device memory
def apUserRW : Nat := 1 * 64            -- AP = 01: user read-write
def apUserRO : Nat := 3 * 64            -- AP = 11: user read-only
def shInner : Nat := 3 * 256            -- inner shareable
def accessFlag : Nat := 1024            -- AF
def notGlobal : Nat := 2048             -- nG: the entry belongs to one address space
def privNoExec : Nat := 9007199254740992   -- PXN, bit 53: the kernel never runs it
def userNoExec : Nat := 18014398509481984  -- UXN, bit 54: user mode never runs it

/-- The page descriptor for a mapping. A mapping without read rights is left unmapped:
the MMU cannot give user mode write or execute access without read. -/
def pageDesc (m : Mapping) : Nat :=
  if m.rights.r then
    framePA m.frame + dValid + dTableOrPage + attrNormal +
      (if m.rights.w then apUserRW else apUserRO) + shInner + accessFlag + notGlobal +
      privNoExec + (if m.rights.x then 0 else userNoExec)
  else 0

/-- The first mapping of virtual page `v`. -/
def findVpn : List Mapping → Nat → Option Mapping
  | .nil, _ => none
  | m :: ms, v => if m.vpn == v then some m else findVpn ms v

/-- Entry `k` of task `i`'s level-3 table: its user pages. -/
def l3Word (s : KState) (i k : Nat) : Nat :=
  match findVpn (mapsOf s i) k with
  | some m => pageDesc m
  | none => 0

/-- Entry `k` of a task's level-2 table: only entry 0, pointing at the level-3 table at
physical address `l3`. -/
def l2Word (l3 k : Nat) : Nat := if k = 0 then l3 + dValid + dTableOrPage else 0

/-- The kernel's own level-1 entries, the same in every address space: the first GiB of
RAM (kernel only, never run from user mode) and the peripherals (kernel only, never run). -/
def kernelL1Word (k : Nat) : Nat :=
  if k = 0 then 0 + dValid + attrNormal + shInner + accessFlag + userNoExec
  else if k = 3 then 0xC0000000 + dValid + attrDevice + accessFlag + privNoExec + userNoExec
  else 0

/-- Entry `k` of a task's level-1 table: the kernel's entries, and entry 2 (virtual
0x8000_0000, the user window) pointing at the level-2 table at physical address `l2`. -/
def l1Word (l2 k : Nat) : Nat := if k = 2 then l2 + dValid + dTableOrPage else kernelL1Word k

@[export leanos_kernel_l1] def exKernelL1 (k : Nat) : Nat := kernelL1Word k
@[export leanos_l1] def exL1 (l2 k : Nat) : Nat := l1Word l2 k
@[export leanos_l2] def exL2 (l3 k : Nat) : Nat := l2Word l3 k
@[export leanos_l3] def exL3 (s : KState) (i k : Nat) : Nat := l3Word s i k

@[export leanos_reply_status] def exRStatus (r : Reply) : Nat := r.status
@[export leanos_reply_value] def exRValue (r : Reply) : Nat := r.value
@[export leanos_reply_out_va] def exROutVa (r : Reply) : Nat := r.outVa
@[export leanos_reply_out_len] def exROutLen (r : Reply) : Nat := r.outLen
@[export leanos_reply_remap] def exRRemap (r : Reply) : Bool := r.remap
@[export leanos_reply_resched] def exRResched (r : Reply) : Bool := r.resched
@[export leanos_reply_state] def exRState (r : Reply) : KState := r.state

end LeanOS
