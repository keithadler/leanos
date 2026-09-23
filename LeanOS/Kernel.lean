/-
The kernel's decisions, written in Lean and compiled into the running kernel.

Everything that decides *who may touch what* lives here: capabilities, address-space
mappings, messages between tasks, system calls, and the scheduler. The C and assembly
underneath (arch/) only carry out what this file returns: they write page tables, copy
registers, and print bytes. The theorems about these definitions are in
`LeanOS/Proofs.lean` and `LeanOS/Tables.lean`, and they are about exactly this code,
because this code is what runs.

This module is a `prelude` module that imports only `Init.Core`, so the compiled kernel
carries six small pieces of Lean's standard library and nothing that needs an operating
system underneath it.
-/
prelude
import Init.Core

namespace LeanOS

/-! ## Rights and capabilities -/

/-- What a capability allows. For a frame: read, write, execute. For an endpoint the same
three bits mean receive (`r`), send (`w`) and grant (`x`): whether a send may carry a
capability along. -/
structure Rights where
  r : Bool
  w : Bool
  x : Bool

namespace Rights

/-- The rights both `a` and `b` allow. Deriving a capability goes through this, so a
derived capability can never allow more than its parent. -/
def meet (a b : Rights) : Rights := ⟨a.r && b.r, a.w && b.w, a.x && b.x⟩

/-- Rights from the bits a user program passes: 1 = r, 2 = w, 4 = x. -/
def ofBits (n : Nat) : Rights := ⟨n % 2 == 1, n / 2 % 2 == 1, n / 4 % 2 == 1⟩

def toBits (a : Rights) : Nat :=
  (if a.r then 1 else 0) + (if a.w then 2 else 0) + (if a.x then 4 else 0)

def rx : Rights := ⟨true, false, true⟩
def rw : Rights := ⟨true, true, false⟩

end Rights

/-- What a capability names: a physical 4 KiB frame, or an endpoint messages pass through. -/
inductive Obj where
  | frame (f : Nat)
  | endpoint (e : Nat)

/-- A capability: an object, what its holder may do with it, and a badge. The badge of an
endpoint capability is delivered with every message sent through it, so a receiver knows
who is talking. Frames carry badge 0. -/
structure Cap where
  obj : Obj
  rights : Rights
  badge : Nat

/-- One page of a task's address space: virtual page `vpn` shows physical `frame`. -/
structure Mapping where
  vpn : Nat
  frame : Nat
  rights : Rights

/-- A message: the sender's badge, three words, and at most one frame capability. -/
structure Msg where
  badge : Nat
  w0 : Nat
  w1 : Nat
  w2 : Nat
  grant : Option Cap

inductive Status where
  | ready
  /-- blocked until a task receives this message from endpoint `e` -/
  | sending (e : Nat) (m : Msg)
  /-- blocked until a task sends to endpoint `e` -/
  | receiving (e : Nat)
  | dead

structure Task where
  caps : List Cap
  maps : List Mapping
  status : Status
  /-- Values for registers x0, x1, … to load the next time the task runs: the result of its
  last system call. Empty when there is nothing to load. -/
  result : List Nat

structure KState where
  tasks : List Task
  cur : Nat

/-! ## List helpers

Written out here instead of taken from the standard library (which also brings the `[a, b]`
list notation this module goes without), so the compiled kernel stays small and the proofs
reason about definitions that are visible in this file. -/

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

/-! ## The boot manifest

The tasks the system starts with and the capabilities each one holds. Endpoint
capabilities are fixed here: tasks can pass frames to each other, but not endpoints, so
the ways authority can flow are set by this manifest (see `Proofs.lean`, `Reach`). -/

/-- Each task's user window is 512 pages (2 MiB) starting at virtual address `userBase`. -/
def userPages : Nat := 512
def userBase : Nat := 0x80000000
def pageSize : Nat := 4096

/-- The most a single `write` may print. -/
def maxWrite : Nat := 256

/-- A task may hold at most this many capabilities, so no task can grow kernel memory
without bound by deriving or being granted capabilities. -/
def maxCaps : Nat := 64

/-- The number of tasks. The frame pool holds four frames for each. -/
def numTasks : Nat := 4
def maxTasks : Nat := 4
def poolFrames : Nat := 4 * maxTasks

def frameCap (f : Nat) (r : Rights) : Cap := ⟨.frame f, r, 0⟩
def epCap (e : Nat) (recv send grant : Bool) (badge : Nat) : Cap := ⟨.endpoint e, ⟨recv, send, grant⟩, badge⟩

/-- Task `i` owns frames `4i` to `4i+3`: code (read/execute), data, stack, and a spare
frame it holds a capability to but has not mapped. -/
def frameCaps (i : Nat) : List Cap :=
  frameCap (4 * i) Rights.rx :: frameCap (4 * i + 1) Rights.rw :: frameCap (4 * i + 2) Rights.rw ::
    frameCap (4 * i + 3) Rights.rw :: .nil

/-- Endpoint 0 is the server's inbox. Task 0 (alice) may send to it and grant frames, with
badge 1. Task 1 (the server) receives from it. Task 2 (mallory) may send to it, without
grant, with badge 2. Task 3 (carol) holds no endpoint. Each endpoint capability is
capability 4 of its task. -/
def initCaps : Nat → List Cap
  | 0 => snoc (frameCaps 0) (epCap 0 false true true 1)
  | 1 => snoc (frameCaps 1) (epCap 0 true false false 0)
  | 2 => snoc (frameCaps 2) (epCap 0 false true false 2)
  | i => frameCaps i

def initMaps (i : Nat) : List Mapping :=
  ⟨0, 4 * i, Rights.rx⟩ :: ⟨1, 4 * i + 1, Rights.rw⟩ :: ⟨511, 4 * i + 2, Rights.rw⟩ :: .nil

def mkTask (i : Nat) : Task := ⟨initCaps i, initMaps i, .ready, .nil⟩

def mkTasksFrom (i : Nat) : Nat → List Task
  | 0 => .nil
  | k + 1 => mkTask i :: mkTasksFrom (i + 1) k

def init : KState := ⟨mkTasksFrom 0 numTasks, 0⟩

/-! ## Scheduling -/

def isReady (ts : List Task) (i : Nat) : Bool :=
  match nth? ts i with
  | some t => match t.status with
    | .ready => true
    | _ => false
  | none => false

/-- The first ready task at or after `i`, wrapping around, looking at most `fuel` tasks. -/
def findReady (ts : List Task) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    let j := i % len ts
    if isReady ts j then some j else findReady ts (j + 1) fuel

/-- Round robin: the next ready task after the current one, or the current one if it is the
only one ready. If none is ready, the state is unchanged and the machine layer stops. -/
def schedule (s : KState) : KState :=
  match findReady s.tasks (s.cur + 1) (len s.tasks) with
  | some j => { s with cur := j }
  | none => s

def setTask (s : KState) (j : Nat) (t : Task) : KState := { s with tasks := setNth s.tasks j t }

/-- Stop the current task (it exited or faulted) and move on. -/
def killCurrent (s : KState) : KState :=
  match nth? s.tasks s.cur with
  | some t => schedule (setTask s s.cur { t with status := .dead, result := .nil })
  | none => schedule s

/-! ## Messages -/

def isReceiving (e : Nat) : Status → Bool
  | .receiving e' => e' == e
  | _ => false

def sendingMsg (e : Nat) : Status → Option Msg
  | .sending e' m => if e' == e then some m else none
  | _ => none

/-- The first task (from index `j` on) blocked receiving from endpoint `e`. -/
def findReceiver (e : Nat) : List Task → Nat → Option Nat
  | .nil, _ => none
  | t :: ts, j => if isReceiving e t.status then some j else findReceiver e ts (j + 1)

/-- The first task (from index `j` on) blocked sending to endpoint `e`, with its message. -/
def findSender (e : Nat) : List Task → Nat → Option (Nat × Msg)
  | .nil, _ => none
  | t :: ts, j =>
    match sendingMsg e t.status with
    | some m => some (j, m)
    | none => findSender e ts (j + 1)

/-- Task `u` receives message `m`: it becomes ready with the message in its registers
(x0 = 0, x1 = badge, x2–x4 = words, x5 = 1 + index of a granted capability, or 0). A
granted capability goes at the end of its list; if the list is full the delivery fails. -/
def deliver (u : Task) (m : Msg) : Option Task :=
  match m.grant with
  | none => some { u with status := .ready,
                          result := 0 :: m.badge :: m.w0 :: m.w1 :: m.w2 :: 0 :: .nil }
  | some c =>
    if len u.caps < maxCaps then
      some { u with caps := snoc u.caps c, status := .ready,
                    result := 0 :: m.badge :: m.w0 :: m.w1 :: m.w2 :: (len u.caps + 1) :: .nil }
    else none

/-! ## System calls -/

/-- What the machine layer must do after a system call, beyond loading the result registers
of whichever task runs next. -/
structure Reply where
  state : KState
  /-- print `outLen` bytes starting at user address `outVa` of the calling task (0 = none).
  Only returned after checking every page of that range is mapped readable, so the machine
  layer can read it without faulting and without reading memory the task cannot. -/
  outVa : Nat
  outLen : Nat
  /-- the calling task's mappings changed, so its page tables must be rebuilt -/
  remap : Bool

/-- The call returns to the caller with result registers `r`. -/
def ret (s : KState) (t : Task) (r : List Nat) : Reply :=
  ⟨setTask s s.cur { t with result := r }, 0, 0, false⟩

/-- Status codes in x0. -/
def eNoCap : Nat := 1        -- no such capability
def eBadArg : Nat := 2       -- wrong kind of capability, missing right, or bad argument
def eNoCall : Nat := 3       -- no such system call
def eFull : Nat := 4         -- too many capabilities

/-- Map the frame named by capability `ci` at virtual page `vpn`, with that capability's
rights. The only way a task gains a mapping. -/
def sysMap (s : KState) (t : Task) (ci vpn : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .endpoint _ => ret s t (eBadArg :: .nil)
    | .frame f =>
      if vpn < userPages && c.rights.r then
        ⟨setTask s s.cur { t with maps := ⟨vpn, f, c.rights⟩ :: dropVpn vpn t.maps,
                                  result := 0 :: .nil }, 0, 0, true⟩
      else ret s t (eBadArg :: .nil)

def sysUnmap (s : KState) (t : Task) (vpn : Nat) : Reply :=
  ⟨setTask s s.cur { t with maps := dropVpn vpn t.maps, result := 0 :: .nil }, 0, 0, true⟩

/-- A new capability to the same object with at most the rights asked for, and the same
badge. Returns its index in x1. -/
def sysDerive (s : KState) (t : Task) (ci bits : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    if len t.caps < maxCaps then
      ret s { t with caps := snoc t.caps ⟨c.obj, c.rights.meet (Rights.ofBits bits), c.badge⟩ }
        (0 :: len t.caps :: .nil)
    else ret s t (eFull :: .nil)

/-- x1 = rights bits, x2 = kind (0 frame, 1 endpoint). -/
def sysCapInfo (s : KState) (t : Task) (ci : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    ret s t (0 :: c.rights.toBits :: (match c.obj with | .frame _ => 0 | .endpoint _ => 1) :: .nil)

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
  if n = 0 then ret s t (0 :: 0 :: .nil)
  else if n ≤ maxWrite ∧ userBase ≤ va ∧
      allReadable t.maps ((va - userBase) / pageSize)
        ((va + n - 1 - userBase) / pageSize + 1 - (va - userBase) / pageSize) = true then
    ⟨setTask s s.cur { t with result := 0 :: n :: .nil }, va, n, false⟩
  else ret s t (eBadArg :: .nil)

/-- The capability a send carries: none if `gi = 0`, else capability `gi - 1`, which must be
a frame, through an endpoint capability with the grant right. `none` means the grant is
not allowed. -/
def grantOf (t : Task) (ep : Cap) (gi : Nat) : Option (Option Cap) :=
  if gi = 0 then some none
  else if ep.rights.x then
    match nth? t.caps (gi - 1) with
    | some g =>
      match g.obj with
      | .frame _ => some (some g)
      | .endpoint _ => none
    | none => none
  else none

/-- Send three words, and optionally a frame capability, through endpoint capability `ci`.
If a task is waiting to receive, it gets the message now and the sender carries on;
otherwise the sender waits. -/
def sysSend (s : KState) (t : Task) (ci w0 w1 w2 gi : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .frame _ => ret s t (eBadArg :: .nil)
    | .endpoint e =>
      if c.rights.w then
        match grantOf t c gi with
        | none => ret s t (eBadArg :: .nil)
        | some g =>
          let m : Msg := ⟨c.badge, w0, w1, w2, g⟩
          match findReceiver e s.tasks 0 with
          | some j =>
            match nth? s.tasks j with
            | some u =>
              match deliver u m with
              | some u' => ret (setTask s j u') t (0 :: .nil)
              | none => ret s t (eFull :: .nil)
            | none => ret s t (eBadArg :: .nil)
          | none =>
            ⟨schedule (setTask s s.cur { t with status := .sending e m, result := .nil }), 0, 0, false⟩
      else ret s t (eBadArg :: .nil)

/-- Receive through endpoint capability `ci`: take a waiting sender's message, or wait for
one. The sender, if it was waiting, carries on with x0 = 0. -/
def sysRecv (s : KState) (t : Task) (ci : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .frame _ => ret s t (eBadArg :: .nil)
    | .endpoint e =>
      if c.rights.r then
        match findSender e s.tasks 0 with
        | some (j, m) =>
          match nth? s.tasks j with
          | some u =>
            match deliver t m with
            | some t' =>
              ⟨setTask (setTask s j { u with status := .ready, result := 0 :: .nil }) s.cur t',
                0, 0, false⟩
            | none => ret s t (eFull :: .nil)
          | none => ret s t (eBadArg :: .nil)
        | none =>
          ⟨schedule (setTask s s.cur { t with status := .receiving e, result := .nil }), 0, 0, false⟩
      else ret s t (eBadArg :: .nil)

/-- System call `num` from the current task with arguments `a0` to `a4`:
  0 write(va, len) · 1 yield · 2 map(cap, vpn) · 3 unmap(vpn) · 4 derive(cap, rights)
  5 exit · 6 capinfo(cap) · 7 whoami · 8 send(cap, w0, w1, w2, grant) · 9 recv(cap) -/
def syscall (s : KState) (num a0 a1 a2 a3 a4 : Nat) : Reply :=
  match nth? s.tasks s.cur with
  | none => ⟨s, 0, 0, false⟩
  | some t =>
    match num with
    | 0 => sysWrite s t a0 a1
    | 1 => ⟨schedule (setTask s s.cur { t with result := 0 :: .nil }), 0, 0, false⟩
    | 2 => sysMap s t a0 a1
    | 3 => sysUnmap s t a0
    | 4 => sysDerive s t a0 a1
    | 5 => ⟨killCurrent s, 0, 0, false⟩
    | 6 => sysCapInfo s t a0
    | 7 => ret s t (0 :: s.cur :: .nil)
    | 8 => sysSend s t a0 a1 a2 a3 a4
    | 9 => sysRecv s t a0
    | _ => ret s t (eNoCall :: .nil)

/-- The machine layer has loaded task `j`'s result registers; forget them. -/
def clearResult (s : KState) (j : Nat) : KState :=
  match nth? s.tasks j with
  | some t => setTask s j { t with result := .nil }
  | none => s

/-! ## The interface the machine layer calls

Exported functions take every argument owned (Lean does not allow borrowed arguments on
`@[export]`), so the C caller increments the reference count of anything it wants to keep
before passing it in. -/

@[export leanos_init] def exInit (u : Nat) : KState := if u = 0 then init else init
@[export leanos_syscall] def exSyscall (s : KState) (num a0 a1 a2 a3 a4 : Nat) : Reply :=
  syscall s num a0 a1 a2 a3 a4
@[export leanos_tick] def exTick (s : KState) : KState := schedule s
@[export leanos_fault] def exFault (s : KState) : KState := killCurrent s
@[export leanos_clear_result] def exClearResult (s : KState) (j : Nat) : KState := clearResult s j

@[export leanos_cur] def exCur (s : KState) : Nat := s.cur
@[export leanos_ready] def exReady (s : KState) (i : Nat) : Bool := isReady s.tasks i
@[export leanos_ntasks] def exNTasks (s : KState) : Nat := len s.tasks

def resultOf (s : KState) (j : Nat) : List Nat :=
  match nth? s.tasks j with
  | some t => t.result
  | none => .nil

@[export leanos_result_len] def exResultLen (s : KState) (j : Nat) : Nat := len (resultOf s j)
@[export leanos_result] def exResult (s : KState) (j k : Nat) : Nat :=
  match nth? (resultOf s j) k with
  | some v => v
  | none => 0

/-- Whether task `j` has stopped for good (for the machine layer's final report). -/
@[export leanos_dead] def exDead (s : KState) (j : Nat) : Bool :=
  match nth? s.tasks j with
  | some t => match t.status with
    | .dead => true
    | _ => false
  | none => true

@[export leanos_reply_out_va] def exROutVa (r : Reply) : Nat := r.outVa
@[export leanos_reply_out_len] def exROutLen (r : Reply) : Nat := r.outLen
@[export leanos_reply_remap] def exRRemap (r : Reply) : Bool := r.remap
@[export leanos_reply_state] def exRState (r : Reply) : KState := r.state

/-- Task `i`'s mappings. -/
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


end LeanOS
