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
import LeanOS.Manifest

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

/-- What a capability names: a run of `count` physical 4 KiB frames starting at frame
`base`, an endpoint messages pass through, interrupt line `n`, the right to start (and
restart) the program in slot `k`, a run of `count` 512-byte blocks of the SD card
starting at block `base`, or the right to switch the machine off or restart it. -/
inductive Obj where
  | frames (base count : Nat)
  | endpoint (e : Nat)
  | irq (n : Nat)
  | launch (k : Nat)
  | blocks (base count : Nat)
  | power
  | board
  | usbHost

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

/-- A message: the sender's badge, three words, and at most one frame-run capability. -/
structure Msg where
  badge : Nat
  w0 : Nat
  w1 : Nat
  w2 : Nat
  grant : Option Cap
  /-- a call: the sender waits for the receiver's reply -/
  call : Bool

inductive Status where
  /-- loaded, not yet checked against the manifest: never runs -/
  | unverified
  | ready
  /-- blocked until a task receives this message from endpoint `e` -/
  | sending (e : Nat) (m : Msg)
  /-- blocked until a task sends to endpoint `e`, or (`deadline` ≠ 0) until the timer has
  ticked `deadline` times since boot, whichever comes first -/
  | receiving (e : Nat) (deadline : Nat)
  /-- blocked after a call, until task `server` replies -/
  | awaiting (server : Nat)
  /-- asleep until the timer has ticked `wake` times since boot -/
  | sleeping (wake : Nat)
  /-- blocked until interrupt line `n` fires -/
  | waitingIrq (n : Nat)
  | dead

structure Task where
  caps : List Cap
  maps : List Mapping
  status : Status
  /-- Values for registers x0, x1, … to load the next time the task runs: the result of its
  last system call. Empty when there is nothing to load. -/
  result : List Nat
  /-- Tasks that called this one and wait for its reply, oldest first. A reply names one by
  its position here. -/
  callers : List Nat
  /-- The SHA-256 the machine layer measured over what the task was loaded with, as eight
  32-bit words; empty until measured. -/
  hash : List Nat

structure KState where
  tasks : List Task
  cur : Nat
  /-- The physical address of the framebuffer the firmware allocated at boot. It never
  changes. Framebuffer frames can only be mapped if it is sane (`fbSane`). -/
  fbBase : Nat
  /-- Interrupt lines that fired while no task was waiting for them. -/
  pending : List Nat
  /-- Timer ticks since boot (one every `tickMs` milliseconds). -/
  now : Nat
  /-- The USB host channels' DMA addresses and transfer sizes, as the driver last wrote them.
  They reach the controller only when a transfer starts, and only after the kernel checked
  them against the driver's memory (`sysUsb`). -/
  usbDma : List Nat
  usbSize : List Nat

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

def app {α : Type} : List α → List α → List α
  | .nil, l => l
  | a :: l, l' => a :: app l l'

/-- Remove every mapping of virtual page `v`. -/
def dropVpn (v : Nat) : List Mapping → List Mapping
  | .nil => .nil
  | m :: ms => if m.vpn == v then dropVpn v ms else m :: dropVpn v ms

/-- Remove every mapping of pages `vpn` to `vpn + count - 1`. One pass over the task's
mappings, however large `count` is: a task may ask to unmap 2^40 pages, and the kernel must
not spend 2^40 steps saying yes. -/
def dropRange (vpn count : Nat) : List Mapping → List Mapping
  | .nil => .nil
  | m :: ms => if vpn ≤ m.vpn && m.vpn < vpn + count then dropRange vpn count ms
               else m :: dropRange vpn count ms

/-- `count` pages: virtual page `vpn + k` shows frame `base + k`. -/
def runMaps (vpn base : Nat) (r : Rights) : Nat → List Mapping
  | 0 => .nil
  | k + 1 => ⟨vpn, base, r⟩ :: runMaps (vpn + 1) (base + 1) r k

/-! ## The boot manifest

The tasks the system starts with and the capabilities each one holds. Endpoint
capabilities are fixed here: tasks can pass frames to each other, but not endpoints, so
the ways authority can flow are set by this manifest (see `Proofs.lean`, `Reach`). -/

/-- Each task's user window is 8192 pages (32 MiB) starting at virtual address `userBase`. -/
def userPages : Nat := 8192
def userBase : Nat := 0x80000000
def pageSize : Nat := 4096

/-- The most a single `write` may print. -/
def maxWrite : Nat := 256

/-- A task may hold at most this many capabilities, so no task can grow kernel memory
without bound by deriving or being granted capabilities. -/
def maxCaps : Nat := 64

/-- The number of program slots in the manifest, and the most the frame pool has room for. -/
def numTasks : Nat := 18
def maxTasks : Nat := 20

/-- Each task owns 256 frames (1 MiB) of the pool: task `i` owns frames `256i` to `256i+255`. -/
def framesPerTask : Nat := 256
def poolFrames : Nat := framesPerTask * maxTasks

def runCap (base count : Nat) (r : Rights) : Cap := ⟨.frames base count, r, 0⟩

/-- The framebuffer: 1024 × 600 pixels of 4 bytes, 600 pages. Its pages are frames
`poolFrames` to `poolFrames + fbPages - 1`. -/
def fbWidth : Nat := 1024
def fbHeight : Nat := 600
def fbPages : Nat := 600

/-- The task that owns the framebuffer at boot: the display server. -/
def displayTask : Nat := 1
/-- Settings: the only task that holds the board's settings (`boardCap`). -/
def settingsTask : Nat := 6

/-- Device register pages, after the framebuffer: frame `devBase + k` is device page `k`.
Page 0 is the PL011 UART. -/
def devBase : Nat := poolFrames + fbPages
def devPages : Nat := 1
def devicePA (k : Nat) : Nat := if k = 0 then 0xFE201000 else 0xFE201000

/-- The UART's receive interrupt (GIC INTID 153, SPI 121). -/
def uartIrq : Nat := 153

/-- The task that owns the UART at boot: the input driver. -/
def inputTask : Nat := 4
/-- The USB driver: the only task that holds the USB host controller (`usbCap`). -/
def usbTask : Nat := 17
/-- The USB host controller's interrupt (the DWC2's, VideoCore IRQ 9: GIC INTID 105). -/
def usbIrq : Nat := 105
/-- The DWC2 has eight host channels; each has a DMA address and a transfer size register. -/
def usbZeros : List Nat := 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: .nil
/-- The file server: it receives on endpoint 1. -/
def fileServer : Nat := 8

/-- Who owns frame `f` at boot: pool frames belong to task `f / 64`, framebuffer frames to
the display server, device pages to the input driver. -/
def owner (f : Nat) : Nat :=
  if f < poolFrames then f / framesPerTask else if f < devBase then displayTask else inputTask
def epCap (e : Nat) (recv send grant : Bool) (badge : Nat) : Cap := ⟨.endpoint e, ⟨recv, send, grant⟩, badge⟩
def irqCap (n : Nat) : Cap := ⟨.irq n, ⟨true, true, false⟩, 0⟩
def launchCap (k : Nat) : Cap := ⟨.launch k, ⟨true, true, false⟩, 0⟩

/-- How much of the SD card the file server may use: blocks 0 to 2047 (1 MiB). -/
def diskBlocks : Nat := 1048576
def blocksCap (base count : Nat) : Cap := ⟨.blocks base count, ⟨true, true, false⟩, 0⟩
def powerCap : Cap := ⟨.power, ⟨true, true, false⟩, 0⟩
/-- The Raspberry Pi's own settings: read the board and its sensors (read right), change the
CPU clock and the activity light (write right). Settings' capability 5. -/
def boardCap : Cap := ⟨.board, ⟨true, true, false⟩, 0⟩
/-- The USB host controller (the Pi 4's DWC2): its registers, read and written only through
the kernel, which starts a DMA transfer only into memory the holder owns (`sysUsb`). -/
def usbCap : Cap := ⟨.usbHost, ⟨true, true, false⟩, 0⟩

/-- Task `i`'s frames, as four runs: 16 pages of code (read/execute), 8 of data, 4 of
stack, and 228 spare pages it holds a capability to but has not mapped. The machine layer
loads the task's assets (fonts, icons, pictures), if it has any, at the start of the spare
run. -/
def frameCaps (i : Nat) : List Cap :=
  runCap (256 * i) 16 Rights.rx :: runCap (256 * i + 16) 8 Rights.rw ::
    runCap (256 * i + 24) 4 Rights.rw :: runCap (256 * i + 28) 228 Rights.rw :: .nil

/-- Endpoint 0 is the display server's inbox. Task 0 (alice's Notes) may send to it and
grant frames, with badge 1. Task 1 (the display server) receives from it, holds the
framebuffer as capability 5, may start Notes and the four apps (capabilities 6 to 10), and
may switch the machine off or restart it (capability 11), and may start the Apps launcher
(capability 12).
Task 2 (mallory) may send to it, without grant, with badge 2. Task 3 (carol) holds no
endpoint. Task 4 (the input driver) may send to it with badge 3, and holds the UART's
registers (capability 5) and its interrupt (capability 6). Tasks 5 (Terminal), 6
(Settings), 7 (Security) and 9 (Files) may send and grant with badges 5, 6, 7 and 9.
Each of these endpoint capabilities is capability 4 of its task.

Terminal also holds the launch capabilities for the open slots, 10 to 15 (its
capabilities 6 to 11), which run programs from the SD card; they may send and grant to the
display server with badges 10 to 15. Task 16, the Apps launcher, holds the same: a window
(badge 16), the file server (badge 16, its capability 5, to read programs and their icons),
and the open slots' launch capabilities (its capabilities 6 to 11).

Endpoint 1 is the file server's inbox. Task 8 (the file server) receives from it, and
Notes, Terminal and Files may send to it and grant (a buffer, for one request), with
badges 1, 5 and 9, as their capability 5. The file server alone holds the SD card's first
`diskBlocks` blocks, as its capability 5. -/
def initCaps : Nat → List Cap
  | 0 => snoc (snoc (frameCaps 0) (epCap 0 false true true 1)) (epCap 1 false true true 1)
  | 1 => snoc (snoc (snoc (snoc (snoc (snoc (snoc (snoc (snoc (frameCaps 1) (epCap 0 true false false 0))
           (runCap poolFrames fbPages Rights.rw)) (launchCap 0)) (launchCap 5)) (launchCap 6)) (launchCap 7))
           (launchCap 9)) powerCap) (launchCap 16)
  | 2 => snoc (frameCaps 2) (epCap 0 false true false 2)
  | 4 => snoc (snoc (snoc (frameCaps 4) (epCap 0 false true false 3)) (runCap devBase devPages Rights.rw))
           (irqCap uartIrq)
  | 5 => snoc (snoc (snoc (snoc (snoc (snoc (snoc (snoc (snoc (frameCaps 5) (epCap 0 false true true 5))
           (epCap 1 false true true 5)) (launchCap 10)) (launchCap 11)) (launchCap 12)) (launchCap 13))
           (launchCap 14)) (launchCap 15)) (epCap 2 false true true 5)
  | 6 => snoc (snoc (frameCaps 6) (epCap 0 false true true 6)) boardCap
  | 7 => snoc (frameCaps 7) (epCap 0 false true true 7)
  | 8 => snoc (snoc (frameCaps 8) (epCap 1 true false false 0)) (blocksCap 0 diskBlocks)
  | 9 => snoc (snoc (frameCaps 9) (epCap 0 false true true 9)) (epCap 1 false true true 9)
  | 10 => snoc (snoc (frameCaps 10) (epCap 0 false true true 10)) (epCap 1 false true true 10)
  | 11 => snoc (snoc (frameCaps 11) (epCap 0 false true true 11)) (epCap 1 false true true 11)
  | 12 => snoc (snoc (frameCaps 12) (epCap 0 false true true 12)) (epCap 1 false true true 12)
  | 13 => snoc (snoc (frameCaps 13) (epCap 0 false true true 13)) (epCap 1 false true true 13)
  | 14 => snoc (snoc (frameCaps 14) (epCap 0 false true true 14)) (epCap 1 false true true 14)
  | 15 => snoc (snoc (frameCaps 15) (epCap 0 false true true 15)) (epCap 1 false true true 15)
  | 17 => snoc (snoc (snoc (snoc (frameCaps 17) (epCap 0 false true false 17)) (irqCap usbIrq)) usbCap)
           (epCap 2 true false false 0)
  | 16 => snoc (snoc (snoc (snoc (snoc (snoc (snoc (snoc (frameCaps 16) (epCap 0 false true true 16))
           (epCap 1 false true true 16)) (launchCap 10)) (launchCap 11)) (launchCap 12)) (launchCap 13))
           (launchCap 14)) (launchCap 15)
  | i => frameCaps i

/-- The open slots, 10 to 15: they run whatever program they are started with (Terminal
loads one from the SD card), not a program the manifest names. What such a program may do
is fixed here all the same: its own frames, and a window from the display server. -/
def openSlot (i : Nat) : Bool := Nat.ble 10 i && Nat.ble i 15

/-- The largest program an open slot can be started with: its code run. -/
def maxImage : Nat := 16 * 4096

/-- The programs the machine layer loads and checks at boot. The apps in slots 5 (Terminal),
6 (Settings), 7 (Security), 9 (Files) and 16 (Apps) wait until the display server launches
them. -/
def autostart (i : Nat) : Bool := i < 5 || i == 8 || i == 17

/-- Code at pages 0–15, data at 16–23, the stack in the last four pages of the window. -/
def initMaps (i : Nat) : List Mapping :=
  app (runMaps 0 (256 * i) Rights.rx 16)
    (app (runMaps 16 (256 * i + 16) Rights.rw 8) (runMaps (userPages - 4) (256 * i + 24) Rights.rw 4))

/-- Every task starts unverified: it cannot run until `verify` has checked it. -/
def mkTask (i : Nat) : Task := ⟨initCaps i, initMaps i, .unverified, .nil, .nil, .nil⟩

def mkTasksFrom (i : Nat) : Nat → List Task
  | 0 => .nil
  | k + 1 => mkTask i :: mkTasksFrom (i + 1) k

def init (fbBase : Nat) : KState := ⟨mkTasksFrom 0 numTasks, 0, fbBase, .nil, 0, usbZeros, usbZeros⟩

def setTask (s : KState) (j : Nat) (t : Task) : KState := { s with tasks := setNth s.tasks j t }

/-! ## Verified boot -/

def eqList : List Nat → List Nat → Bool
  | .nil, .nil => true
  | a :: as, b :: bs => a == b && eqList as bs
  | _, _ => false

/-- The machine layer measured task `i`'s code and assets as hash `h`. If that is the
manifest's hash, the task may run; otherwise it is refused for good. Only an unverified
task is checked, so no task is ever checked twice. -/
def verify (s : KState) (i : Nat) (h : List Nat) : KState :=
  match nth? s.tasks i with
  | some t =>
    match t.status with
    | .unverified =>
      if openSlot i || eqList h (expectedHash i) then setTask s i { t with status := .ready, hash := h }
      else setTask s i { t with status := .dead, hash := h }
    | _ => s
  | none => s

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


/-! ## Time -/

/-- The timer ticks every 10 ms (the machine layer programs it so). -/
def tickMs : Nat := 10

/-- Status code: nothing came before the time ran out (`recvt`). -/
def eTimeout : Nat := 6

/-- Wake every task whose sleep ends at or before tick `now`, and every receiver whose
deadline has come (with `eTimeout`). -/
def wakeTask (now : Nat) (t : Task) : Task :=
  match t.status with
  | .sleeping u => if Nat.ble u now then { t with status := .ready, result := 0 :: .nil } else t
  | .receiving _ u =>
    if !(u == 0) && Nat.ble u now then { t with status := .ready, result := eTimeout :: .nil } else t
  | _ => t

def wakeSleepers (now : Nat) : List Task → List Task
  | .nil => .nil
  | t :: ts => wakeTask now t :: wakeSleepers now ts

/-- A timer tick: the clock advances, sleepers whose time has come wake, and the scheduler
picks the next task. -/
def tick (s : KState) : KState :=
  schedule { s with now := s.now + 1, tasks := wakeSleepers (s.now + 1) s.tasks }

/-- Stop the current task (it exited or faulted) and move on. -/
def killCurrent (s : KState) : KState :=
  match nth? s.tasks s.cur with
  | some t => schedule (setTask s s.cur { t with status := .dead, result := .nil })
  | none => schedule s

/-! ## Messages -/

def isReceiving (e : Nat) : Status → Bool
  | .receiving e' _ => e' == e
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

/-- A free reply slot. -/
def noTask : Nat := 1000000

/-- A task answers at most this many callers at once. -/
def maxCallers : Nat := 8

/-- Put caller `j` in the first free slot, or a new one at the end. Slots never move, so a
server can hold on to a slot number until it replies. Returns the slots and `j`'s slot. -/
def placeCaller (j : Nat) : List Nat → Nat → List Nat × Nat
  | .nil, i => (j :: .nil, i)
  | c :: cs, i =>
    if c == noTask then (j :: cs, i)
    else match placeCaller j cs (i + 1) with
      | (cs', k) => (c :: cs', k)

/-- Task `u` receives message `m` from task `sender`: it becomes ready with the message in
its registers (x0 = 0, x1 = badge, x2–x4 = words, x5 = 1 + index of a granted capability
or 0, x6 = 1 + the reply slot of a call or 0). A granted capability goes at the end of its
list. If its capabilities or reply slots are full, the delivery fails. -/
def deliver (u : Task) (m : Msg) (sender : Nat) : Option Task :=
  let placed := placeCaller sender u.callers 0
  let callers := if m.call then placed.1 else u.callers
  let slot := if m.call then placed.2 + 1 else 0
  if len callers ≤ maxCallers then
    match m.grant with
    | none => some { u with status := .ready, callers := callers,
                            result := 0 :: m.badge :: m.w0 :: m.w1 :: m.w2 :: 0 :: slot :: .nil }
    | some c =>
      if len u.caps < maxCaps then
        some { u with caps := snoc u.caps c, status := .ready, callers := callers,
                      result := 0 :: m.badge :: m.w0 :: m.w1 :: m.w2 :: (len u.caps + 1) :: slot :: .nil }
      else none
  else none

/-- Whether task `j` of `ts` is waiting for a reply from task `server`. -/
def awaitsFrom (ts : List Task) (j server : Nat) : Bool :=
  match nth? ts j with
  | some u => match u.status with
    | .awaiting k => k == server
    | _ => false
  | none => false

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
  /-- unmask interrupt line `unmask - 1` at the interrupt controller (0 = none) -/
  unmask : Nat
  /-- load the program for slot `load - 1` into its frames, measure it and verify it; every
  task's page tables must be rebuilt (0 = none) -/
  load : Nat
  /-- block I/O on the SD card: 1 = read block `ioBlock` into the calling task's 512 bytes at
  user address `outVa`, 2 = write those bytes to it (0 = none). Only returned after checking
  the block is in a block capability the task holds with that right, and the bytes lie in a
  page it has mapped writable (for a read) or readable (for a write). -/
  io : Nat
  ioBlock : Nat
  /-- with `load`: copy the `loadLen` bytes at the calling task's user address `outVa` into
  the slot's code frames, as its program (0 = load the program the kernel image has for
  the slot). Only returned after checking every page of that range is mapped readable in
  the calling task's address space as it is after the start. -/
  loadLen : Nat
  /-- switch the machine off (1) or restart it (2), at the request of a power capability's
  holder (0 = neither) -/
  power : Nat
  /-- ask the board's firmware or hardware (0 = nothing), at the request of a board
  capability's holder: one of `boardRequests`, see `sysBoard` -/
  board : Nat
  /-- the USB host controller, for the holder of the USB capability (0 = nothing):
  1 write `usbB` to register `usbA` · 2 start channel `usbA`: DMA address `usbB`, transfer
  size register `usbC`, then its characteristics `usbD` · 3 read register `usbA` -/
  usbOp : Nat
  usbA : Nat
  usbB : Nat
  usbC : Nat
  usbD : Nat

/-- The call returns to the caller with result registers `r`. -/
def ret (s : KState) (t : Task) (r : List Nat) : Reply :=
  ⟨setTask s s.cur { t with result := r }, 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Where the frame pool starts: frame `f < poolFrames` is at `frameBase + f * pageSize`. -/
def frameBase : Nat := 0x04000000

/-- The framebuffer address is usable: page-aligned, past the end of the frame pool (so it
overlaps neither the pool nor the kernel below it), and below the peripherals. -/
def fbSane (b : Nat) : Bool :=
  b % pageSize == 0 && frameBase + poolFrames * pageSize ≤ b && b + fbPages * pageSize ≤ 0xFE000000

/-- A run of frames that may be mapped: all in the pool, all in a sane framebuffer, or all
device pages. -/
def validRun (s : KState) (base count : Nat) : Bool :=
  base + count ≤ poolFrames || (fbSane s.fbBase && base + count ≤ devBase) ||
    (devBase ≤ base && base + count ≤ devBase + devPages)

/-- Status codes in x0. -/
def eNoCap : Nat := 1        -- no such capability
def eBadArg : Nat := 2       -- wrong kind of capability, missing right, or bad argument
def eNoCall : Nat := 3       -- no such system call
def eFull : Nat := 4         -- too many capabilities

/-- Map the run of frames named by capability `ci` at virtual pages `vpn` onward, with that
capability's rights. The only way a task gains mappings. -/
def sysMap (s : KState) (t : Task) (ci vpn : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .frames base count =>
      if vpn + count ≤ userPages && c.rights.r && validRun s base count then
        ⟨setTask s s.cur { t with maps := app (runMaps vpn base c.rights count)
                                               (dropRange vpn count t.maps),
                                  result := 0 :: .nil }, 0, 0, true, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
      else ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-- Unmap pages `vpn` to `vpn + count - 1`. -/
def sysUnmap (s : KState) (t : Task) (vpn count : Nat) : Reply :=
  ⟨setTask s s.cur { t with maps := dropRange vpn count t.maps, result := 0 :: .nil }, 0, 0, true, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The object a derived capability names: for a run of frames, the `count` frames from
`offset` on (`count = 0`: all of them from `offset` on), if they lie inside the run. -/
def subObj (o : Obj) (offset count : Nat) : Option Obj :=
  match o with
  | .frames base n =>
    if count = 0 then
      if offset < n then some (.frames (base + offset) (n - offset)) else none
    else if offset + count ≤ n then some (.frames (base + offset) count) else none
  | o => some o

/-- A new capability with at most the rights asked for, the same badge, and for a run of
frames a piece of it. Returns its index in x1. -/
def sysDerive (s : KState) (t : Task) (ci bits offset count : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match subObj c.obj offset count with
    | none => ret s t (eBadArg :: .nil)
    | some o =>
      if len t.caps < maxCaps then
        ret s { t with caps := snoc t.caps ⟨o, c.rights.meet (Rights.ofBits bits), c.badge⟩ }
          (0 :: len t.caps :: .nil)
      else ret s t (eFull :: .nil)

/-- x1 = rights bits, x2 = kind (0 frames, 1 endpoint, 2 interrupt, 3 launch, 4 disk blocks), x3 =
number of frames, the interrupt line, the slot, or the number of blocks. -/
def sysCapInfo (s : KState) (t : Task) (ci : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .frames _ n => ret s t (0 :: c.rights.toBits :: 0 :: n :: .nil)
    | .endpoint _ => ret s t (0 :: c.rights.toBits :: 1 :: 0 :: .nil)
    | .irq n => ret s t (0 :: c.rights.toBits :: 2 :: n :: .nil)
    | .launch k => ret s t (0 :: c.rights.toBits :: 3 :: k :: .nil)
    | .blocks _ n => ret s t (0 :: c.rights.toBits :: 4 :: n :: .nil)
    | .power => ret s t (0 :: c.rights.toBits :: 5 :: 0 :: .nil)
    | .board => ret s t (0 :: c.rights.toBits :: 6 :: 0 :: .nil)
    | .usbHost => ret s t (0 :: c.rights.toBits :: 7 :: 0 :: .nil)

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
    ⟨setTask s s.cur { t with result := 0 :: n :: .nil }, va, n, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  else ret s t (eBadArg :: .nil)

/-- The capability a send carries: none if `gi = 0`, else capability `gi - 1`, which must be
a run of frames, through an endpoint capability with the grant right. `none` means the grant is
not allowed. -/
def grantOf (t : Task) (ep : Cap) (gi : Nat) : Option (Option Cap) :=
  if gi = 0 then some none
  else if ep.rights.x then
    match nth? t.caps (gi - 1) with
    | some g =>
      match g.obj with
      | .frames _ _ => some (some g)
      | _ => none
    | none => none
  else none

/-- Send three words, and optionally a frame capability, through endpoint capability `ci`.
If a task is waiting to receive, it gets the message now; otherwise the sender waits. A
plain send then carries on; a call waits for the receiver's reply. -/
def sysSend (s : KState) (t : Task) (ci w0 w1 w2 gi : Nat) (call : Bool) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .endpoint e =>
      if c.rights.w then
        match grantOf t c gi with
        | none => ret s t (eBadArg :: .nil)
        | some g =>
          let m : Msg := ⟨c.badge, w0, w1, w2, g, call⟩
          match findReceiver e s.tasks 0 with
          | some j =>
            match nth? s.tasks j with
            | some u =>
              match deliver u m s.cur with
              | some u' =>
                if call then
                  ⟨schedule (setTask (setTask s j u') s.cur { t with status := .awaiting j, result := .nil }),
                    0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
                else ret (setTask s j u') t (0 :: .nil)
              | none => ret s t (eFull :: .nil)
            | none => ret s t (eBadArg :: .nil)
          | none =>
            ⟨schedule (setTask s s.cur { t with status := .sending e m, result := .nil }), 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
      else ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-- Receive through endpoint capability `ci`: take a waiting sender's message, or wait for
one. A waiting plain sender carries on with x0 = 0; a caller goes on waiting, for the reply. -/
def sysRecv (s : KState) (t : Task) (ci : Nat) (block : Bool) (deadline : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .endpoint e =>
      if c.rights.r then
        match findSender e s.tasks 0 with
        | some (j, m) =>
          match nth? s.tasks j with
          | some u =>
            match deliver t m j with
            | some t' =>
              let u' : Task := if m.call then { u with status := .awaiting s.cur, result := .nil }
                               else { u with status := .ready, result := 0 :: .nil }
              ⟨setTask (setTask s j u') s.cur t', 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
            | none => ret s t (eFull :: .nil)
          | none => ret s t (eBadArg :: .nil)
        | none =>
          if block then
            ⟨schedule (setTask s s.cur { t with status := .receiving e deadline, result := .nil }), 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
          else ret s t (eTimeout :: .nil)
      else ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-- Answer the caller in reply slot `slot` (see `Task.callers`) with three words. Only a
task still waiting for this task's reply is woken; a reply carries no capability. The slot
is freed either way. -/
def sysReply (s : KState) (t : Task) (slot w0 w1 w2 : Nat) : Reply :=
  match nth? t.callers slot with
  | none => ret s t (eBadArg :: .nil)
  | some j =>
    let t' : Task := { t with callers := setNth t.callers slot noTask }
    if awaitsFrom s.tasks j s.cur then
      match nth? s.tasks j with
      | some u => ret (setTask s j { u with status := .ready, result := 0 :: w0 :: w1 :: w2 :: .nil }) t'
                    (0 :: .nil)
      | none => ret s t' (eBadArg :: .nil)
    else ret s t' (eBadArg :: .nil)

/-- Remove every `n` from a list of interrupt lines. -/
def dropLine (n : Nat) : List Nat → List Nat
  | .nil => .nil
  | x :: xs => if x == n then dropLine n xs else x :: dropLine n xs

def hasLine (n : Nat) : List Nat → Bool
  | .nil => false
  | x :: xs => x == n || hasLine n xs

/-- Wait for the interrupt named by capability `ci`: return at once if it already fired,
otherwise sleep until it does. -/
def sysIrqWait (s : KState) (t : Task) (ci : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .irq n =>
      if hasLine n s.pending then ret { s with pending := dropLine n s.pending } t (0 :: .nil)
      else ⟨schedule (setTask s s.cur { t with status := .waitingIrq n, result := .nil }), 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    | _ => ret s t (eBadArg :: .nil)

/-- The holder of an interrupt has dealt with it: let it fire again. -/
def sysIrqAck (s : KState) (t : Task) (ci : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .irq n => { ret s t (0 :: .nil) with unmask := n + 1 }
    | _ => ret s t (eBadArg :: .nil)

/-! ## The SD card -/

/-- Virtual page `v` is mapped with write rights. -/
def writableAt : List Mapping → Nat → Bool
  | .nil, _ => false
  | m :: ms, v => (m.vpn == v && m.rights.w) || writableAt ms v

/-- The page right block I/O needs in memory: writable to read from the disk into it,
readable to write it to the disk. -/
def pageRightFor : Bool → List Mapping → Nat → Bool
  | true => readableAt
  | false => writableAt

/-- The capability right block I/O needs: read to read the disk, write to write it. -/
def capRightFor : Bool → Rights → Bool
  | true => Rights.w
  | false => Rights.r

def ioCode : Bool → Nat
  | true => 2
  | false => 1

/-- The 512 bytes at `va` may be filled from the disk (`write = false`: the page must be
writable) or sent to it (`write = true`: readable). -/
def ioPageOk (ms : List Mapping) (va : Nat) (write : Bool) : Bool :=
  va % 512 == 0 && Nat.ble userBase va && pageRightFor write ms ((va - userBase) / pageSize)

/-- Read block `idx` of block capability `ci` into the task's memory at `va`, or write it
from there (`write`). The machine layer moves the bytes, and reports a hardware failure
with `ioFailed`. -/
def sysBlock (s : KState) (t : Task) (ci idx va : Nat) (write : Bool) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .blocks b n =>
      if Nat.ble (idx + 1) n && capRightFor write c.rights && ioPageOk t.maps va write then
        ⟨setTask s s.cur { t with result := 0 :: .nil }, va, 0, false, 0, 0, ioCode write, b + idx, 0, 0, 0, 0, 0, 0, 0, 0⟩
      else ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-- The machine layer could not complete the block I/O the last call asked for: the calling
task gets an I/O error instead of success. -/
def eIO : Nat := 5
def ioFailed (s : KState) : KState :=
  match nth? s.tasks s.cur with
  | some t => setTask s s.cur { t with result := eIO :: .nil }
  | none => s

/-! ## Power -/

/-- Switch the machine off (`action` 0) or restart it (1), through power capability `ci`
with the write right. -/
def sysPower (s : KState) (t : Task) (ci action : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .power =>
      if c.rights.w && Nat.ble action 1 then
        ⟨setTask s s.cur { t with result := 0 :: .nil }, 0, 0, false, 0, 0, 0, 0, 0, action + 1, 0, 0, 0, 0, 0, 0⟩
      else ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-! ## The Raspberry Pi's settings -/

/-- The CPU clocks Settings may choose, in MHz. None is above 1500, what every Pi 4 is
rated for: the kernel never asks the firmware to overclock. -/
def cpuSpeeds : List Nat := 600 :: 1000 :: 1500 :: .nil

/-- What the machine layer may be asked to do with the board, by number:
  1 read the board (revision, serial, memory, firmware) · 2 read its sensors (temperature,
  CPU clock, throttling) · 3 switch the activity light off · 4 switch it on ·
  600, 1000, 1500 set the CPU clock to that many MHz.
Nothing else, ever: see `board_requests_listed`. -/
def boardRequests : List Nat := 1 :: 2 :: 3 :: 4 :: cpuSpeeds

/-- `board(cap, what, value)`: what 0 reads the board, 1 its sensors, 2 sets the CPU clock
to `cpuSpeeds[value]`, 3 switches the activity light off (value 0) or on (1). Returns the
request number, or 0 if the arguments ask for nothing on the list. -/
def boardRequest (what value : Nat) : Nat :=
  if what = 0 then 1
  else if what = 1 then 2
  else if what = 2 then (match nth? cpuSpeeds value with | some mhz => mhz | none => 0)
  else if what = 3 ∧ value < 2 then 3 + value
  else 0

/-- A request that changes something (as opposed to reading), which needs the write right. -/
def boardChanges (req : Nat) : Bool := Nat.ble 3 req

/-- Ask the board something through board capability `ci`. The machine layer carries the
request out and hands back what the firmware answered (`boardDone`), or an I/O error. -/
def sysBoard (s : KState) (t : Task) (ci what value : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .board =>
      let req := boardRequest what value
      if !(req == 0) && (if boardChanges req then c.rights.w else c.rights.r) then
        ⟨setTask s s.cur { t with result := 0 :: .nil }, 0, 0, false, 0, 0, 0, 0, 0, 0, req, 0, 0, 0, 0, 0⟩
      else ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-- The machine layer did a board request for the current task: its answer, five numbers
from the firmware, become the task's results. -/
def boardDone (s : KState) (a b c d e : Nat) : KState :=
  match nth? s.tasks s.cur with
  | some t => setTask s s.cur { t with result := 0 :: a :: b :: c :: d :: e :: .nil }
  | none => s

/-! ## The USB host controller

The Pi 4's DWC2 moves data by DMA: it reads and writes RAM at whatever address its channel
registers hold, and the Pi has no IOMMU to stop it. So the USB driver never writes those
registers itself. It reads and writes the controller's registers only through `usb`, and
the kernel keeps each channel's DMA address and transfer size aside until the driver starts
the channel; then it checks the whole transfer lies in frames the driver holds, with the
right the direction needs (write for data coming in, read for data going out), and only
then are the three registers written, together. The registers that could aim DMA anywhere
else (device mode's, descriptor lists, descriptor DMA itself, forcing device mode) are never
written at all. `usb_dma_confined` and `usb_dma_own_memory` are the theorems. -/

/-- Bit `k` of `v`. -/
def bit (v k : Nat) : Bool := (v / 2 ^ k) % 2 == 1

/-- A host channel register: offsets 0x500 to 0x5FF, eight channels of 0x20 bytes. -/
def inChan (reg : Nat) : Bool := Nat.ble 0x500 reg && Nat.ble (reg + 1) 0x600
def chanOf (reg : Nat) : Nat := (reg - 0x500) / 0x20
def chanReg (reg : Nat) : Nat := (reg - 0x500) % 0x20

/-- Writes the kernel never lets through: anything but an aligned register in the first
page (the data FIFOs above it are for slave mode), device mode's registers (whose DMA
addresses nobody checks), forcing device mode (GUSBCFG bit 30), descriptor DMA (HCFG bit 23),
and the channels' descriptor-list addresses (HCDMAB). -/
def usbForbidden (reg value : Nat) : Bool :=
  !(reg % 4 == 0) || !(Nat.ble (reg + 1) 0x1000) ||
  (Nat.ble 0x800 reg && Nat.ble (reg + 1) 0xC00) ||
  (reg == 0x00C && bit value 30) || (reg == 0x400 && bit value 23) ||
  (inChan reg && chanReg reg == 0x1C)

/-- The most a channel can write past its transfer size: one full-speed packet. -/
def usbSlack : Nat := 1024

/-- Some frame capability in `cs` covers bytes `a` to `a + n - 1` of task `j`'s own frames
in the pool (never memory another task lent it), with the write right (`w`) or the read
right. -/
def dmaOk (j : Nat) : List Cap → Nat → Nat → Bool → Bool
  | .nil, _, _, _ => false
  | c :: cs, a, n, w =>
    (match c.obj with
     | .frames b k => Nat.ble (framesPerTask * j) b && Nat.ble (b + k) (framesPerTask * (j + 1)) &&
         Nat.ble (b + k) poolFrames && Nat.ble (frameBase + b * pageSize) a &&
         Nat.ble (a + n) (frameBase + (b + k) * pageSize) && (if w then c.rights.w else c.rights.r)
     | _ => false) || dmaOk j cs a n w

def nthD (l : List Nat) (i : Nat) : Nat := match nth? l i with | some v => v | none => 0

/-- A reply that asks the machine layer for something on the USB controller. -/
def usbReply (s : KState) (t : Task) (op a b c d : Nat) : Reply :=
  ⟨setTask s s.cur { t with result := 0 :: .nil }, 0, 0, false, 0, 0, 0, 0, 0, 0, 0, op, a, b, c, d⟩

/-- `usb(cap, op, reg, value)`: op 0 reads register `reg`, op 1 writes `value` to it. -/
def sysUsb (s : KState) (t : Task) (ci op reg value : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .usbHost =>
      if op = 0 then
        if c.rights.r && reg % 4 == 0 && Nat.ble (reg + 1) 0x1000 then usbReply s t 3 reg 0 0 0
        else ret s t (eBadArg :: .nil)
      else if op = 1 && c.rights.w && !usbForbidden reg value then
        if inChan reg && chanReg reg == 0x14 then
          ret { s with usbDma := setNth s.usbDma (chanOf reg) value } t (0 :: .nil)
        else if inChan reg && chanReg reg == 0x10 then
          ret { s with usbSize := setNth s.usbSize (chanOf reg) value } t (0 :: .nil)
        else if inChan reg && chanReg reg == 0 && bit value 31 && !bit value 30 then
          let n := chanOf reg
          let dma := nthD s.usbDma n
          let size := nthD s.usbSize n
          if dmaOk s.cur t.caps dma (size % 2 ^ 19 + usbSlack) (bit value 15) then
            usbReply s t 2 n dma size value
          else ret s t (eBadArg :: .nil)
        else usbReply s t 1 reg value 0 0
      else ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-- The machine layer read a USB register for the current task: `v` is its result. -/
def usbDone (s : KState) (v : Nat) : KState :=
  match nth? s.tasks s.cur with
  | some t => setTask s s.cur { t with result := 0 :: v :: .nil }
  | none => s

/-! ## Time -/

/-- Milliseconds since boot, as hours, minutes and seconds: what the clock shows. -/
def clockOf (ms : Nat) : Nat × Nat × Nat :=
  let secs := ms / 1000
  (secs / 3600, secs / 60 % 60, secs % 60)

/-- `time`: the kernel's own count of timer ticks since boot, the milliseconds that makes,
and the hours, minutes and seconds of that. Changes nothing but the caller's results. -/
def sysTime (s : KState) (t : Task) : Reply :=
  let ms := s.now * tickMs
  ret s t (0 :: s.now :: ms :: (clockOf ms).1 :: (clockOf ms).2.1 :: (clockOf ms).2.2 :: .nil)

/-! ## Sleeping -/

/-- Sleep for at least `ms` milliseconds (rounded up to whole ticks), letting other tasks
run; 0 just lets the next ready task run. -/
def sysSleep (s : KState) (t : Task) (ms : Nat) : Reply :=
  let ticks := (ms + tickMs - 1) / tickMs
  if ticks = 0 then ⟨schedule (setTask s s.cur { t with result := 0 :: .nil }), 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  else ⟨schedule (setTask s s.cur { t with status := .sleeping (s.now + ticks), result := .nil }),
        0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-! ## Dropping a capability -/

def removeNth {α : Type} : List α → Nat → List α
  | .nil, _ => .nil
  | _ :: xs, 0 => xs
  | x :: xs, n + 1 => x :: removeNth xs n

/-- Capability `c` covers frame `f`. -/
def coversB (c : Cap) (f : Nat) : Bool :=
  match c.obj with
  | .frames b n => Nat.ble b f && Nat.ble (f + 1) (b + n)
  | _ => false

def sameRights (a b : Rights) : Bool := a.r == b.r && a.w == b.w && a.x == b.x

/-- Some capability in `cs` covers the mapping's frame with exactly its rights. -/
def backedBy : List Cap → Mapping → Bool
  | .nil, _ => false
  | c :: cs, m => (coversB c m.frame && sameRights c.rights m.rights) || backedBy cs m

def keepBacked (cs : List Cap) : List Mapping → List Mapping
  | .nil => .nil
  | m :: ms => if backedBy cs m then m :: keepBacked cs ms else keepBacked cs ms

/-- Let go of capability `ci`. Every page the task could see only through it goes too; the
task's other capabilities move down one place. -/
def sysDrop (s : KState) (t : Task) (ci : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some _ =>
    let cs := removeNth t.caps ci
    ⟨setTask s s.cur { t with caps := cs, maps := keepBacked cs t.maps, result := 0 :: .nil },
      0, 0, true, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-! ## Starting programs, and taking back what they shared -/

/-- A slot whose program may be (re)started: never started, or stopped. -/
def startable : Status → Bool
  | .unverified => true
  | .dead => true
  | _ => false

/-- Frame `f` is one of slot `k`'s own frames. -/
def inSlot (k f : Nat) : Bool := f < poolFrames && f / framesPerTask == k

/-- A capability to frames in slot `k`. Runs never cross from one slot's frames into
anything else (`RunOK` in the proofs), so looking at the first frame is enough. -/
def capInSlot (k : Nat) (c : Cap) : Bool :=
  match c.obj with
  | .frames b _ => inSlot k b
  | _ => false

def dropCaps (k : Nat) : List Cap → List Cap
  | .nil => .nil
  | c :: cs => if capInSlot k c then dropCaps k cs else c :: dropCaps k cs

def dropMaps (k : Nat) : List Mapping → List Mapping
  | .nil => .nil
  | m :: ms => if inSlot k m.frame then dropMaps k ms else m :: dropMaps k ms

/-- A waiting sender's message loses a granted capability into slot `k`. -/
def scrubStatus (k : Nat) : Status → Status
  | .sending e m =>
    .sending e { m with grant := match m.grant with
                   | some c => if capInSlot k c then none else some c
                   | none => none }
  | st => st

/-- Forget slot `k` as a caller waiting for a reply. The slot keeps its place, so the
server's other reply slots keep their numbers, but a reply to it now wakes nobody: not the
program that called, which is gone, and not a later run in the same slot. -/
def forgetCaller (k : Nat) : List Nat → List Nat
  | .nil => .nil
  | x :: xs => (if x == k then noTask else x) :: forgetCaller k xs

/-- Take back from a task everything that reaches into slot `k`'s frames, and any reply it
owes slot `k`'s previous run. -/
def revokeTask (k : Nat) (t : Task) : Task :=
  { t with caps := dropCaps k t.caps, maps := dropMaps k t.maps, status := scrubStatus k t.status,
           callers := forgetCaller k t.callers }

def revokeAll (k : Nat) : List Task → List Task
  | .nil => .nil
  | t :: ts => revokeTask k t :: revokeAll k ts

/-- The program a start names: none for a manifest slot (the kernel image has it), and for
an open slot `len` bytes at `src`, at most `maxImage`, every page readable in `ms` (the
caller's mappings, as they are once the slot's memory is taken back). -/
def imageOk (ms : List Mapping) (k src len : Nat) : Bool :=
  if openSlot k then
    Nat.ble 1 len && Nat.ble len maxImage && Nat.ble userBase src &&
      allReadable ms ((src - userBase) / pageSize)
        ((src + len - 1 - userBase) / pageSize + 1 - (src - userBase) / pageSize)
  else len == 0

/-- Start (or restart) the program in slot `k`, named by launch capability `ci`. First every
task loses whatever reaches into slot `k`'s frames, so nothing its previous run shared
survives; then the slot gets the manifest's fresh task, unverified. The machine layer
clears the frames, loads the program (the kernel image's, or for an open slot the `len`
bytes at `src` in the caller's memory), measures it, and it runs only if it verifies. -/
def sysStart (s : KState) (t : Task) (ci src len : Nat) : Reply :=
  match nth? t.caps ci with
  | none => ret s t (eNoCap :: .nil)
  | some c =>
    match c.obj with
    | .launch k =>
      match nth? s.tasks k with
      | some u =>
        if startable u.status && !(k == s.cur) && imageOk (dropMaps k t.maps) k src len then
          let s1 : KState := setTask { s with tasks := revokeAll k s.tasks } k (mkTask k)
          match nth? s1.tasks s.cur with
          | some t1 => ⟨setTask s1 s.cur { t1 with result := 0 :: .nil }, src, 0, true, 0, k + 1, 0, 0, len, 0, 0, 0, 0, 0, 0, 0⟩
          | none => ret s t (eBadArg :: .nil)
        else ret s t (eBadArg :: .nil)
      | none => ret s t (eBadArg :: .nil)
    | _ => ret s t (eBadArg :: .nil)

/-- The first task (from index `j` on) waiting for interrupt line `n`. -/
def findIrqWaiter (n : Nat) : List Task → Nat → Option Nat
  | .nil, _ => none
  | t :: ts, j =>
    match t.status with
    | .waitingIrq k => if k == n then some j else findIrqWaiter n ts (j + 1)
    | _ => findIrqWaiter n ts (j + 1)

/-- Interrupt line `n` fired (the machine layer has masked it). Wake the task waiting for
it, or remember it for the next wait. -/
def irqFired (s : KState) (n : Nat) : KState :=
  match findIrqWaiter n s.tasks 0 with
  | some j =>
    match nth? s.tasks j with
    | some u => setTask s j { u with status := .ready, result := 0 :: .nil }
    | none => s
  | none => if hasLine n s.pending then s else { s with pending := snoc s.pending n }

/-- The interrupt lines the manifest hands out; the machine layer enables these at boot. -/
def irqLines : List Nat := uartIrq :: usbIrq :: .nil

/-- Task number `i`'s boot check: x1 = 0 not measured yet, 1 matches the manifest, 2
refused, 3 an open slot's program (measured, not in the manifest); x2 and x3 = the first two words of its measured hash; x4 = 0 not started, 1
running, 2 stopped. -/
def sysBootInfo (s : KState) (t : Task) (i : Nat) : Reply :=
  match nth? s.tasks i with
  | none => ret s t (eBadArg :: .nil)
  | some u =>
    let w0 := match u.hash with
      | a :: _ => a
      | _ => 0
    let w1 := match u.hash with
      | _ :: b :: _ => b
      | _ => 0
    let st := match u.hash with
      | .nil => 0
      | _ => if openSlot i then 3 else if eqList u.hash (expectedHash i) then 1 else 2
    let run := match u.status with
      | .unverified => 0
      | .dead => 2
      | _ => 1
    ret s t (0 :: st :: w0 :: w1 :: run :: .nil)

/-- The system calls of a running task. -/
def runCall (s : KState) (t : Task) (num a0 a1 a2 a3 a4 : Nat) : Reply :=
  match num with
  | 0 => sysWrite s t a0 a1
  | 1 => ⟨schedule (setTask s s.cur { t with result := 0 :: .nil }), 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 2 => sysMap s t a0 a1
  | 3 => sysUnmap s t a0 a1
  | 4 => sysDerive s t a0 a1 a2 a3
  | 5 => ⟨killCurrent s, 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 6 => sysCapInfo s t a0
  | 7 => ret s t (0 :: s.cur :: .nil)
  | 8 => sysSend s t a0 a1 a2 a3 a4 false
  | 9 => sysRecv s t a0 true 0
  | 10 => sysSend s t a0 a1 a2 a3 a4 true
  | 11 => sysReply s t a0 a1 a2 a3
  | 12 => sysIrqWait s t a0
  | 13 => sysIrqAck s t a0
  | 14 => sysBootInfo s t a0
  | 15 => sysStart s t a0 0 0
  | 16 => sysDrop s t a0
  | 17 => sysBlock s t a0 a1 a2 false
  | 18 => sysBlock s t a0 a1 a2 true
  | 19 => sysStart s t a0 a1 a2
  | 20 => sysSleep s t a0
  | 21 => sysPower s t a0 a1
  | 22 => sysTime s t
  | 23 => sysBoard s t a0 a1 a2
  | 24 => sysUsb s t a0 a1 a2 a3
  | 25 => sysRecv s t a0 (!(a1 == 0)) (s.now + (a1 + tickMs - 1) / tickMs)
  | _ => ret s t (eNoCall :: .nil)

/-- System call `num` from the current task with arguments `a0` to `a4`:
  0 write(va, len) · 1 yield · 2 map(cap, vpn) · 3 unmap(vpn, count)
  4 derive(cap, rights, offset, count) · 5 exit · 6 capinfo(cap) · 7 whoami
  8 send(cap, w0, w1, w2, grant) · 9 recv(cap) · 10 call(cap, w0, w1, w2, grant)
  11 reply(slot, w0, w1, w2) · 12 irqwait(cap) · 13 irqack(cap) · 14 bootinfo(task)
  15 start(cap) · 16 drop(cap) · 17 blockread(cap, index, va) · 18 blockwrite(cap, index, va)
  19 exec(cap, va, len): start an open slot with the program at va · 20 sleep(ms)
  21 power(cap, action): 0 switch off, 1 restart · 22 time
  23 board(cap, what, value): read the board or its sensors, set the CPU clock or the light
  24 usb(cap, op, reg, value): read (op 0) or write (op 1) a USB host controller register
  25 recvt(cap, ms): like recv, but gives up after `ms` milliseconds (0: do not wait)
Only a running (ready) task makes system calls; anything else is ignored. -/
def syscall (s : KState) (num a0 a1 a2 a3 a4 : Nat) : Reply :=
  match nth? s.tasks s.cur with
  | none => ⟨s, 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | some t =>
    match t.status with
    | .ready => runCall s t num a0 a1 a2 a3 a4
    | _ => ⟨s, 0, 0, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩  -- only a running task makes system calls

/-- The machine layer has loaded task `j`'s result registers; forget them. -/
def clearResult (s : KState) (j : Nat) : KState :=
  match nth? s.tasks j with
  | some t => setTask s j { t with result := .nil }
  | none => s

/-! ## The interface the machine layer calls

Exported functions take every argument owned (Lean does not allow borrowed arguments on
`@[export]`), so the C caller increments the reference count of anything it wants to keep
before passing it in. -/

@[export leanos_init] def exInit (fbBase : Nat) : KState := init fbBase
@[export leanos_syscall] def exSyscall (s : KState) (num a0 a1 a2 a3 a4 : Nat) : Reply :=
  syscall s num a0 a1 a2 a3 a4
@[export leanos_tick] def exTick (s : KState) : KState := tick s
@[export leanos_fault] def exFault (s : KState) : KState := killCurrent s
@[export leanos_clear_result] def exClearResult (s : KState) (j : Nat) : KState := clearResult s j
@[export leanos_verify] def exVerify (s : KState) (i w0 w1 w2 w3 w4 w5 w6 w7 : Nat) : KState :=
  verify s i (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: .nil)
@[export leanos_irq] def exIrq (s : KState) (n : Nat) : KState := irqFired s n
@[export leanos_irq_line_count] def exIrqLineCount (u : Nat) : Nat := len irqLines + u * 0
@[export leanos_irq_line] def exIrqLine (k : Nat) : Nat :=
  match nth? irqLines k with
  | some n => n
  | none => 0
@[export leanos_reply_unmask] def exRUnmask (r : Reply) : Nat := r.unmask
@[export leanos_reply_load] def exRLoad (r : Reply) : Nat := r.load
@[export leanos_reply_io] def exRIo (r : Reply) : Nat := r.io
@[export leanos_reply_load_len] def exRLoadLen (r : Reply) : Nat := r.loadLen
@[export leanos_reply_power] def exRPower (r : Reply) : Nat := r.power
@[export leanos_reply_board] def exRBoard (r : Reply) : Nat := r.board
@[export leanos_reply_usb_op] def exRUsbOp (r : Reply) : Nat := r.usbOp
@[export leanos_reply_usb_a] def exRUsbA (r : Reply) : Nat := r.usbA
@[export leanos_reply_usb_b] def exRUsbB (r : Reply) : Nat := r.usbB
@[export leanos_reply_usb_c] def exRUsbC (r : Reply) : Nat := r.usbC
@[export leanos_reply_usb_d] def exRUsbD (r : Reply) : Nat := r.usbD
@[export leanos_usb_done] def exUsbDone (s : KState) (v : Nat) : KState := usbDone s v
@[export leanos_board_done] def exBoardDone (s : KState) (a b c d e : Nat) : KState := boardDone s a b c d e
@[export leanos_open_slot] def exOpenSlot (i : Nat) : Bool := openSlot i
@[export leanos_reply_io_block] def exRIoBlock (r : Reply) : Nat := r.ioBlock
@[export leanos_io_failed] def exIoFailed (s : KState) : KState := ioFailed s
@[export leanos_autostart] def exAutostart (i : Nat) : Bool := autostart i
/-- The screen the machine layer asks the firmware for. -/
@[export leanos_fb_width] def exFbWidth (u : Nat) : Nat := fbWidth + u * 0
@[export leanos_fb_height] def exFbHeight (u : Nat) : Nat := fbHeight + u * 0
@[export leanos_fb_pages] def exFbPages (u : Nat) : Nat := fbPages + u * 0

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

/-- The physical address of frame `f`: in the pool, the framebuffer, or a device page. -/
def physOf (s : KState) (f : Nat) : Nat :=
  if f < poolFrames then frameBase + f * pageSize
  else if f < devBase then s.fbBase + (f - poolFrames) * pageSize
  else devicePA (f - devBase)

/-- Descriptor fields. Every descriptor is a sum of these, each in its own bits. -/
def dValid : Nat := 1                   -- bit 0
def dTableOrPage : Nat := 2             -- bit 1: a table (levels 1–2) or a page (level 3)
def attrNormal : Nat := 1 * 4           -- AttrIndx = 1: normal write-back memory
def attrDevice : Nat := 0 * 4           -- AttrIndx = 0: device memory
def attrNoCache : Nat := 2 * 4          -- AttrIndx = 2: normal memory, not cached (framebuffer)
def apUserRW : Nat := 1 * 64            -- AP = 01: user read-write
def apUserRO : Nat := 3 * 64            -- AP = 11: user read-only
def shInner : Nat := 3 * 256            -- inner shareable
def accessFlag : Nat := 1024            -- AF
def notGlobal : Nat := 2048             -- nG: the entry belongs to one address space
def privNoExec : Nat := 9007199254740992   -- PXN, bit 53: the kernel never runs it
def userNoExec : Nat := 18014398509481984  -- UXN, bit 54: user mode never runs it

/-- The page descriptor for a mapping. A mapping without read rights is left unmapped:
the MMU cannot give user mode write or execute access without read. Framebuffer pages are
not cached, so what user mode draws reaches the display; device pages are device memory. -/
def pageDesc (s : KState) (m : Mapping) : Nat :=
  if m.rights.r then
    physOf s m.frame + dValid + dTableOrPage +
      (if m.frame < poolFrames then attrNormal else if m.frame < devBase then attrNoCache else attrDevice) +
      (if m.rights.w then apUserRW else apUserRO) + shInner + accessFlag + notGlobal +
      privNoExec + (if m.rights.x then 0 else userNoExec)
  else 0

/-- The first mapping of virtual page `v`. -/
def findVpn : List Mapping → Nat → Option Mapping
  | .nil, _ => none
  | m :: ms, v => if m.vpn == v then some m else findVpn ms v

/-- Entry `k` of task `i`'s level-3 tables: its user pages. The 16 tables are one array of
8192 words, table `k / 512` covering virtual pages `k` to `k + 511` of the window. -/
def l3Word (s : KState) (i k : Nat) : Nat :=
  match findVpn (mapsOf s i) k with
  | some m => pageDesc s m
  | none => 0

/-- The number of level-3 tables per task: the window is 16 × 2 MiB. -/
def l3Tables : Nat := 16

/-- Entry `k` of a task's level-2 table: entries 0–15 point at the task's level-3 tables,
which sit one after another from physical address `l3`. -/
def l2Word (l3 k : Nat) : Nat := if k < l3Tables then l3 + k * pageSize + dValid + dTableOrPage else 0

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
