import LeanOS.Kernel

/-!
# What is proved about the kernel

Every theorem here is about the definitions in `LeanOS/Kernel.lean`, the same definitions
compiled into the running kernel. The states considered are all the states the kernel can
reach: start from `init`, then apply any sequence of system calls (with any arguments),
timer ticks, faults, and result loads.

**Authority flow.** Tasks can hand each other frames, so memory is no longer always
private. What is proved instead is where memory can go. The boot manifest fixes, for good,
which task can send with grant to which (`Edge`: A may send with the grant right on an
endpoint B may receive from). `frame_flow`: a task can only ever hold a frame if a path of
such edges leads to it from the task that owned the frame at boot, and never with more
rights than that owner had.

For the demo manifest this gives: alice can share her memory with the server and nobody
else; the server can pass nothing on; mallory and carol can never hold, map or reach
anyone's memory but their own (`mallory_confined`, `carol_confined`).

For every reachable state, as well:

* `maps_backed`: every page a task can see comes from a capability it holds, with the same
  rights.
* `no_write_execute`: no page is ever both writable and executable.
* `maps_in_range`: every mapping is inside the user window and the frame pool.
* `endpoints_fixed`: endpoint capabilities never grow beyond the manifest's.

About single steps:

* `derive_never_amplifies`: a derived capability names the same object and allows nothing
  its parent does not.
* `write_reads_only_readable`: when `write` asks the machine layer to print user memory,
  every byte lies in a page the calling task has mapped readable.
* `schedule_picks_ready`: if any task is ready, the scheduler picks a ready task.

What the proofs do not cover is listed in TRUST.md.
-/

namespace LeanOS

/-! ## Facts about the list helpers -/

theorem nth?_mem {α : Type} : ∀ {l : List α} {i : Nat} {a : α}, nth? l i = some a → a ∈ l
  | [], _, _, h => by simp [nth?] at h
  | x :: l, 0, a, h => by simp [nth?] at h; simp [h]
  | x :: l, n + 1, a, h => by simp [nth?] at h; exact List.mem_cons_of_mem _ (nth?_mem h)

theorem nth?_lt {α : Type} : ∀ {l : List α} {i : Nat} {a : α}, nth? l i = some a → i < len l
  | [], _, _, h => by simp [nth?] at h
  | x :: l, 0, a, _ => by simp [len]
  | x :: l, n + 1, a, h => by simp [nth?] at h; simp [len]; exact nth?_lt h

theorem len_setNth {α : Type} : ∀ (l : List α) (i : Nat) (v : α), len (setNth l i v) = len l
  | [], _, _ => rfl
  | _ :: l, 0, _ => rfl
  | _ :: l, n + 1, v => by simp [setNth, len, len_setNth l n v]

/-- Reading back after a write: index `i` now holds `v` (if it existed), others unchanged. -/
theorem nth?_setNth {α : Type} : ∀ (l : List α) (i j : Nat) (v : α),
    nth? (setNth l i v) j = if i = j then (nth? l j).map (fun _ => v) else nth? l j
  | [], i, j, v => by simp [setNth, nth?]
  | _ :: l, 0, 0, v => by simp [setNth, nth?]
  | _ :: l, 0, j + 1, v => by simp [setNth, nth?]
  | _ :: l, i + 1, 0, v => by simp [setNth, nth?]
  | _ :: l, i + 1, j + 1, v => by simp [setNth, nth?, nth?_setNth l i j v]

theorem mem_snoc {α : Type} : ∀ {l : List α} {v a : α}, a ∈ snoc l v ↔ a ∈ l ∨ a = v
  | [], v, a => by simp [snoc]
  | x :: l, v, a => by simp [snoc, mem_snoc (l := l), or_assoc]

theorem mem_dropVpn : ∀ {v : Nat} {ms : List Mapping} {m : Mapping},
    m ∈ dropVpn v ms → m ∈ ms ∧ m.vpn ≠ v
  | v, [], m, h => by simp [dropVpn] at h
  | v, x :: ms, m, h => by
    unfold dropVpn at h
    by_cases hx : x.vpn = v
    · simp [hx] at h
      have := mem_dropVpn h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · simp [hx] at h
      rcases h with h | h
      · subst h; exact ⟨List.mem_cons_self .., hx⟩
      · have := mem_dropVpn h
        exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem mem_app {α : Type} : ∀ {l l' : List α} {a : α}, a ∈ app l l' ↔ a ∈ l ∨ a ∈ l'
  | [], l', a => by simp [app]
  | x :: l, l', a => by simp [app, mem_app (l := l), or_assoc]

theorem mem_dropRange : ∀ {vpn count : Nat} {ms : List Mapping} {m : Mapping},
    m ∈ dropRange vpn count ms ↔ m ∈ ms ∧ ¬(vpn ≤ m.vpn ∧ m.vpn < vpn + count)
  | _, _, [], _ => by simp [dropRange]
  | vpn, count, x :: ms, m => by
    by_cases hx : vpn ≤ x.vpn ∧ x.vpn < vpn + count
    · have : (decide (vpn ≤ x.vpn) && decide (x.vpn < vpn + count)) = true := by simp [hx.1, hx.2]
      simp only [dropRange, this, if_true, mem_dropRange (ms := ms)]
      constructor
      · rintro ⟨h, hn⟩; exact ⟨List.mem_cons_of_mem _ h, hn⟩
      · rintro ⟨h, hn⟩
        rcases List.mem_cons.1 h with rfl | h
        · exact absurd hx hn
        · exact ⟨h, hn⟩
    · have : (decide (vpn ≤ x.vpn) && decide (x.vpn < vpn + count)) = false := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using hx
      simp only [dropRange, this, Bool.false_eq_true, if_false, List.mem_cons, mem_dropRange (ms := ms)]
      constructor
      · rintro (rfl | ⟨h, hn⟩)
        · exact ⟨Or.inl rfl, hx⟩
        · exact ⟨Or.inr h, hn⟩
      · rintro ⟨rfl | h, hn⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h, hn⟩

theorem mem_runMaps : ∀ {vpn base : Nat} {r : Rights} {count : Nat} {m : Mapping},
    m ∈ runMaps vpn base r count → ∃ k < count, m.vpn = vpn + k ∧ m.frame = base + k ∧ m.rights = r
  | _, _, _, 0, _, h => by simp [runMaps] at h
  | vpn, base, r, k + 1, m, h => by
    simp only [runMaps, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact ⟨0, by omega, by simp, by simp, rfl⟩
    · obtain ⟨j, hj, h1, h2, h3⟩ := mem_runMaps h
      exact ⟨j + 1, by omega, by rw [h1]; omega, by rw [h2]; omega, h3⟩

/-! ## Rights -/

/-- `a` allows nothing that `b` does not. -/
def RLe (a b : Rights) : Prop :=
  (a.r = true → b.r = true) ∧ (a.w = true → b.w = true) ∧ (a.x = true → b.x = true)

theorem RLe.refl (a : Rights) : RLe a a := ⟨id, id, id⟩

theorem meet_le (a b : Rights) : RLe (a.meet b) a := by
  simp only [RLe, Rights.meet, Bool.and_eq_true]
  exact ⟨And.left, And.left, And.left⟩

/-- Writable and executable at once. -/
def WX (a : Rights) : Prop := a.w = true ∧ a.x = true

theorem not_wx_of_le {a b : Rights} (h : RLe a b) (hb : ¬ WX b) : ¬ WX a :=
  fun ⟨hw, hx⟩ => hb ⟨h.2.1 hw, h.2.2 hx⟩

theorem RLe.trans {a b c : Rights} (h1 : RLe a b) (h2 : RLe b c) : RLe a c :=
  ⟨fun h => h2.1 (h1.1 h), fun h => h2.2.1 (h1.2.1 h), fun h => h2.2.2 (h1.2.2 h)⟩

/-! ## Who can pass memory to whom -/

/-- `A` can hand frames directly to `B`: at boot `A` holds an endpoint capability with the
send and grant rights, and `B` one with the receive right, to the same endpoint. Endpoint
capabilities never move, so this relation is fixed for the life of the system. -/
def Edge (A B : Nat) : Prop :=
  A < numTasks ∧ B < numTasks ∧ ∃ e,
    (∃ c ∈ initCaps A, c.obj = .endpoint e ∧ c.rights.w = true ∧ c.rights.x = true) ∧
    (∃ c ∈ initCaps B, c.obj = .endpoint e ∧ c.rights.r = true)

/-- `B` is reachable from `A` by a chain of zero or more edges. -/
inductive Reach : Nat → Nat → Prop
  | refl (A : Nat) : Reach A A
  | step {A B C : Nat} : Reach A B → Edge B C → Reach A C

theorem Reach.trans {A B C : Nat} (h1 : Reach A B) (h2 : Reach B C) : Reach A C := by
  induction h2 with
  | refl => exact h1
  | step _ he ih => exact Reach.step ih he

/-! ## The invariant

Every property is about one task at a time, measured against the boot manifest. So a
system call that changes one or two tasks only has to show those tasks are still fine. -/

/-- Capability `c` covers frame `f`: it names a run of frames that includes `f`. -/
def Covers (c : Cap) (f : Nat) : Prop := ∃ b n, c.obj = .frames b n ∧ b ≤ f ∧ f < b + n

/-- Task `j` may hold frame `f` with rights `r`: the frame is in the pool, `r` is never
writable and executable, and the frame came to `j` along a chain of edges from its owner at
boot, with no more rights than the owner had. -/
def FrameOK (j f : Nat) (r : Rights) : Prop :=
  f < devBase + devPages ∧ ¬ WX r ∧
    ∃ A c0, A < numTasks ∧ Reach A j ∧ c0 ∈ initCaps A ∧ Covers c0 f ∧ RLe r c0.rights

/-- An endpoint capability held by task `j` is one `j` held at boot, or weaker. -/
def EndpointOK (j e : Nat) (r : Rights) (badge : Nat) : Prop :=
  ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ RLe r c0.rights ∧ c0.badge = badge

/-- A run of frames never spans two slots' memory: if it covers a pool frame, every frame it
covers is a pool frame of the same slot. So taking back a slot's memory never takes back
anything else. -/
def RunOK (c : Cap) : Prop :=
  ∀ f f', Covers c f → Covers c f' → f < poolFrames →
    f' < poolFrames ∧ f / framesPerTask = f' / framesPerTask

structure CapOK (j : Nat) (c : Cap) : Prop where
  frames : ∀ f, Covers c f → FrameOK j f c.rights
  endpoint : ∀ e, c.obj = .endpoint e → EndpointOK j e c.rights c.badge
  irq : ∀ n, c.obj = .irq n → ∃ c0 ∈ initCaps j, c0.obj = .irq n
  launch : ∀ k, c.obj = .launch k → ∃ c0 ∈ initCaps j, c0.obj = .launch k
  blocks : ∀ b n, c.obj = .blocks b n → ∃ c0 ∈ initCaps j, c0.obj = .blocks b n ∧ RLe c.rights c0.rights
  power : c.obj = .power → ∃ c0 ∈ initCaps j, c0.obj = .power
  board : c.obj = .board → ∃ c0 ∈ initCaps j, c0.obj = .board
  usb : c.obj = .usbHost → ∃ c0 ∈ initCaps j, c0.obj = .usbHost
  wall : c.obj = .wallClock → ∃ c0 ∈ initCaps j, c0.obj = .wallClock
  run : RunOK c

/-- A task waiting to send carries only a frame, one that is fine for it to hold, through an
endpoint it was given send and grant rights on at boot. A task waiting to receive was
given the receive right on that endpoint at boot. -/
def StatusOK (j : Nat) : Status → Prop
  | .sending e m =>
    (∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ c0.rights.w = true ∧ c0.badge = m.badge) ∧
    ∀ g, m.grant = some g → CapOK j g ∧ (∃ b n, g.obj = .frames b n) ∧
      ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ c0.rights.w = true ∧ c0.rights.x = true
  | .receiving e _ => ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ c0.rights.r = true
  | .waitingIrq n => ∃ c0 ∈ initCaps j, c0.obj = .irq n
  | _ => True

/-- A task that may run: it has been checked against the manifest and has not stopped. -/
def Alive : Status → Prop
  | .unverified => False
  | .dead => False
  | _ => True

/-- Task `j` is fine. `fb` says whether the framebuffer address is sane; framebuffer frames
are only ever mapped if it is. -/
structure TaskOK (fb : Bool) (j : Nat) (t : Task) : Prop where
  backed : ∀ m ∈ t.maps, ∃ c ∈ t.caps, Covers c m.frame ∧ c.rights = m.rights
  vpnOk : ∀ m ∈ t.maps, m.vpn < userPages
  caps : ∀ c ∈ t.caps, CapOK j c
  status : StatusOK j t.status
  fbMaps : ∀ m ∈ t.maps, m.frame < poolFrames ∨ (fb = true ∧ m.frame < devBase) ∨ devBase ≤ m.frame
  /-- A task that may run was loaded with exactly what the manifest names, unless it is in
  an open slot. -/
  measured : Alive t.status → openSlot j = false → t.hash = expectedHash j

structure Inv (s : KState) : Prop where
  len : len s.tasks = numTasks
  tasks : ∀ j t, nth? s.tasks j = some t → TaskOK (fbSane s.fbBase) j t

theorem Inv.lt {s : KState} (hs : Inv s) {j : Nat} {t : Task} (h : nth? s.tasks j = some t) :
    j < numTasks := hs.len ▸ nth?_lt h

/-- Replacing task `j` by a task that is fine keeps the invariant. -/
theorem inv_setTask {s : KState} (hs : Inv s) {j : Nat} {t : Task} (ht : TaskOK (fbSane s.fbBase) j t) :
    Inv (setTask s j t) := by
  constructor
  · simp [setTask, len_setNth, hs.len]
  · intro i u hu
    simp only [setTask, nth?_setNth] at hu
    by_cases hij : j = i
    · subst hij
      cases h : nth? s.tasks j <;> simp [h] at hu
      subst hu; exact ht
    · simp [hij] at hu; exact hs.tasks i u hu

/-- Which task an endpoint served last plays no part in the invariant. -/
theorem inv_serve {s : KState} (hs : Inv s) {e j : Nat} : Inv (serve s e j) := ⟨hs.len, hs.tasks⟩

/-! What the scheduler changes: which task runs here, the wake-up's choice, and where the
round robin is. Nothing else. -/

theorem rotate_eq (s : KState) : ∃ c t, rotate s = { s with cur := c, turn := t } := by
  unfold rotate; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨s.cur, s.turn, rfl⟩

theorem schedule_eq (s : KState) : ∃ c t, schedule s = { s with cur := c, next := noTask, turn := t } := by
  unfold schedule; split
  · exact ⟨_, s.turn, rfl⟩
  · obtain ⟨c, t, h⟩ := rotate_eq { s with next := noTask }
    exact ⟨c, t, h⟩

theorem preempt_eq (s : KState) (j : Nat) : ∃ c n, preempt s j = { s with cur := c, next := n } := by
  unfold preempt wake; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨s.cur, _, rfl⟩

section
variable (s : KState) (j : Nat) (b : Bool)
@[simp] theorem rotate_tasks : (rotate s).tasks = s.tasks := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_fbBase : (rotate s).fbBase = s.fbBase := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_pending : (rotate s).pending = s.pending := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_now : (rotate s).now = s.now := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_usbDma : (rotate s).usbDma = s.usbDma := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_usbSize : (rotate s).usbSize = s.usbSize := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_busy : (rotate s).busy = s.busy := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_wall : (rotate s).wall = s.wall := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_served : (rotate s).served = s.served := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem rotate_next : (rotate s).next = s.next := by obtain ⟨c, t, h⟩ := rotate_eq s; rw [h]
@[simp] theorem schedule_fbBase : (schedule s).fbBase = s.fbBase := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]
@[simp] theorem schedule_pending : (schedule s).pending = s.pending := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]
@[simp] theorem schedule_usbDma : (schedule s).usbDma = s.usbDma := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]
@[simp] theorem schedule_usbSize : (schedule s).usbSize = s.usbSize := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]
@[simp] theorem schedule_busy : (schedule s).busy = s.busy := by obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]
@[simp] theorem schedule_wall : (schedule s).wall = s.wall := by obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]
@[simp] theorem schedule_served' : (schedule s).served = s.served := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]
@[simp] theorem wake_tasks : (wake s j).tasks = s.tasks := rfl
@[simp] theorem wake_fbBase : (wake s j).fbBase = s.fbBase := rfl
@[simp] theorem wake_pending : (wake s j).pending = s.pending := rfl
@[simp] theorem wake_now : (wake s j).now = s.now := rfl
@[simp] theorem wake_usbDma : (wake s j).usbDma = s.usbDma := rfl
@[simp] theorem wake_usbSize : (wake s j).usbSize = s.usbSize := rfl
@[simp] theorem wake_busy : (wake s j).busy = s.busy := rfl
@[simp] theorem wake_wall : (wake s j).wall = s.wall := rfl
@[simp] theorem wake_served : (wake s j).served = s.served := rfl
@[simp] theorem wake_cur : (wake s j).cur = s.cur := rfl
@[simp] theorem wake_turn : (wake s j).turn = s.turn := rfl
@[simp] theorem wakeSender_tasks : (wakeSender b s j).tasks = s.tasks := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_fbBase : (wakeSender b s j).fbBase = s.fbBase := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_pending : (wakeSender b s j).pending = s.pending := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_now : (wakeSender b s j).now = s.now := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_usbDma : (wakeSender b s j).usbDma = s.usbDma := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_usbSize : (wakeSender b s j).usbSize = s.usbSize := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_busy : (wakeSender b s j).busy = s.busy := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_wall : (wakeSender b s j).wall = s.wall := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_served : (wakeSender b s j).served = s.served := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_cur : (wakeSender b s j).cur = s.cur := by unfold wakeSender; split <;> rfl
@[simp] theorem wakeSender_turn : (wakeSender b s j).turn = s.turn := by unfold wakeSender; split <;> rfl
@[simp] theorem preempt_tasks : (preempt s j).tasks = s.tasks := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_fbBase : (preempt s j).fbBase = s.fbBase := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_pending : (preempt s j).pending = s.pending := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_now : (preempt s j).now = s.now := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_usbDma : (preempt s j).usbDma = s.usbDma := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_usbSize : (preempt s j).usbSize = s.usbSize := by
  obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_busy : (preempt s j).busy = s.busy := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_wall : (preempt s j).wall = s.wall := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_served : (preempt s j).served = s.served := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
@[simp] theorem preempt_turn : (preempt s j).turn = s.turn := by obtain ⟨c, n, h⟩ := preempt_eq s j; rw [h]
end

/-- The invariant is about the tasks and the framebuffer's address only. -/
theorem Inv.of_eq {s s' : KState} (hs : Inv s) (ht : s'.tasks = s.tasks) (hf : s'.fbBase = s.fbBase) :
    Inv s' := ⟨ht ▸ hs.len, fun j t h => hf ▸ hs.tasks j t (ht ▸ h)⟩

theorem inv_rotate {s : KState} (hs : Inv s) : Inv (rotate s) := hs.of_eq (by simp) (by simp)
theorem inv_wake {s : KState} (hs : Inv s) (j : Nat) : Inv (wake s j) := hs.of_eq rfl rfl
theorem inv_wakeSender {s : KState} (hs : Inv s) (b : Bool) (j : Nat) : Inv (wakeSender b s j) :=
  hs.of_eq (by simp) (by simp)
theorem inv_preempt {s : KState} (hs : Inv s) (j : Nat) : Inv (preempt s j) := hs.of_eq (by simp) (by simp)

theorem inv_schedule {s : KState} (hs : Inv s) : Inv (schedule s) := by
  obtain ⟨c, t, h⟩ := schedule_eq s
  rw [h]; exact ⟨hs.len, hs.tasks⟩

/-- The registers a task will resume with play no part in the invariant. -/
theorem TaskOK.result {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (r : List Nat) :
    TaskOK fb j { t with result := r } := ⟨h.backed, h.vpnOk, h.caps, h.status, h.fbMaps, h.measured⟩

theorem TaskOK.setStatus {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (st : Status)
    (hst : StatusOK j st) (hm : Alive st → openSlot j = false → t.hash = expectedHash j) (r : List Nat) :
    TaskOK fb j { t with status := st, result := r } :=
  ⟨h.backed, h.vpnOk, h.caps, hst, h.fbMaps, hm⟩

theorem inv_killCurrent {s : KState} (hs : Inv s) : Inv (killCurrent s) := by
  unfold killCurrent
  split
  · rename_i t ht
    exact inv_schedule (inv_setTask hs ((hs.tasks _ t ht).setStatus .dead trivial (fun h => h.elim) _))
  · exact inv_schedule hs

theorem inv_clearResult {s : KState} (hs : Inv s) (j : Nat) : Inv (clearResult s j) := by
  unfold clearResult
  split
  · rename_i t ht; exact inv_setTask hs ((hs.tasks j t ht).result _)
  · exact hs

/-! ## Capabilities -/

theorem subObj_covers {o o' : Obj} {off cnt f : Nat} (h : subObj o off cnt = some o')
    (hf : ∃ b n, o' = .frames b n ∧ b ≤ f ∧ f < b + n) : ∃ b n, o = .frames b n ∧ b ≤ f ∧ f < b + n := by
  obtain ⟨b', n', rfl, h1, h2⟩ := hf
  unfold subObj at h
  split at h
  · rename_i base n
    split at h
    · split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨base, n, rfl, by omega, by omega⟩
      · simp at h
    · split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨base, n, rfl, by omega, by omega⟩
      · simp at h
  · simp at h; exact ⟨b', n', h, h1, h2⟩

theorem subObj_same {o o' : Obj} {off cnt : Nat} (h : subObj o off cnt = some o')
    (hn : ∀ b n, o' ≠ .frames b n) : o = o' := by
  unfold subObj at h
  split at h
  · rename_i base n
    split at h
    · split at h
      · simp at h; exact absurd h.symm (hn _ _)
      · simp at h
    · split at h
      · simp at h; exact absurd h.symm (hn _ _)
      · simp at h
  · simp at h; exact h

theorem subObj_endpoint {o o' : Obj} {off cnt e : Nat} (h : subObj o off cnt = some o')
    (he : o' = .endpoint e) : o = .endpoint e := by
  rw [subObj_same h (by intro b n hb; rw [he] at hb; cases hb), he]

theorem subObj_irq {o o' : Obj} {off cnt n : Nat} (h : subObj o off cnt = some o')
    (he : o' = .irq n) : o = .irq n := by
  rw [subObj_same h (by intro b k hb; rw [he] at hb; cases hb), he]

theorem subObj_launch {o o' : Obj} {off cnt k : Nat} (h : subObj o off cnt = some o')
    (he : o' = .launch k) : o = .launch k := by
  rw [subObj_same h (by intro b n hb; rw [he] at hb; cases hb), he]

theorem subObj_blocks {o o' : Obj} {off cnt b n : Nat} (h : subObj o off cnt = some o')
    (he : o' = .blocks b n) : o = .blocks b n := by
  rw [subObj_same h (by intro b' n' hb; rw [he] at hb; cases hb), he]

theorem subObj_usb {o o' : Obj} {off cnt : Nat} (h : subObj o off cnt = some o')
    (he : o' = .usbHost) : o = .usbHost := by
  cases o <;> simp [subObj] at h
  · split at h <;> split at h <;> simp at h <;> subst he <;> simp at h
  all_goals first | exact (h ▸ he) | (subst he; simp_all)

theorem subObj_wall {o o' : Obj} {off cnt : Nat} (h : subObj o off cnt = some o')
    (he : o' = .wallClock) : o = .wallClock := by
  cases o <;> simp [subObj] at h
  · split at h <;> split at h <;> simp at h <;> subst he <;> simp at h
  all_goals first | exact (h ▸ he) | (subst he; simp_all)

theorem subObj_board {o o' : Obj} {off cnt : Nat} (h : subObj o off cnt = some o')
    (he : o' = .board) : o = .board := by
  cases o <;> simp [subObj] at h
  · split at h <;> split at h <;> simp at h <;> subst he <;> simp at h
  all_goals first | exact (h ▸ he) | (subst he; simp_all)

theorem subObj_power {o o' : Obj} {off cnt : Nat} (h : subObj o off cnt = some o')
    (he : o' = .power) : o = .power := by
  rw [subObj_same h (by intro b n hb; rw [he] at hb; cases hb), he]

theorem capOK_derive {j : Nat} {c : Cap} {o : Obj} {off cnt : Nat} (h : CapOK j c)
    (ho : subObj c.obj off cnt = some o) (r : Rights) : CapOK j ⟨o, c.rights.meet r, c.badge⟩ where
  frames f hf := by
    obtain ⟨hlt, hwx, A, c0, hA, hr, hc0, hcov, hle⟩ := h.frames f (subObj_covers ho hf)
    exact ⟨hlt, not_wx_of_le (meet_le _ _) hwx, A, c0, hA, hr, hc0, hcov,
      RLe.trans (meet_le _ _) hle⟩
  endpoint e he := by
    obtain ⟨c0, hc0, hco, hle, hb⟩ := h.endpoint e (subObj_endpoint ho he)
    exact ⟨c0, hc0, hco, RLe.trans (meet_le _ _) hle, hb⟩
  irq n hn := h.irq n (subObj_irq ho hn)
  launch k hk := h.launch k (subObj_launch ho hk)
  blocks b n hb := by
    obtain ⟨c0, hc0, hco, hle⟩ := h.blocks b n (subObj_blocks ho hb)
    exact ⟨c0, hc0, hco, RLe.trans (meet_le _ _) hle⟩
  power hp := h.power (subObj_power ho hp)
  board hb := h.board (subObj_board ho hb)
  usb hu := h.usb (subObj_usb ho hu)
  wall hw := h.wall (subObj_wall ho hw)
  run f f' hf hf' hp := h.run f f' (subObj_covers ho hf) (subObj_covers ho hf') hp

/-- A frame capability that is fine for `A` to hold is fine for `B` to hold, if `A` can pass
frames to `B`. -/
theorem capOK_grant {A B : Nat} {g : Cap} (hg : CapOK A g) (hf : ∃ b n, g.obj = .frames b n)
    (he : Edge A B) : CapOK B g := by
  obtain ⟨b, n, hgf⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hg.run⟩
  · intro f' hf'
    obtain ⟨hlt, hwx, C, c0, hC, hr, hc0, ho, hle⟩ := hg.frames f' hf'
    exact ⟨hlt, hwx, C, c0, hC, Reach.step hr he, hc0, ho, hle⟩
  · intro e he'; rw [hgf] at he'; cases he'
  · intro n hn; rw [hgf] at hn; cases hn
  · intro k hk; rw [hgf] at hk; cases hk
  · intro b' n' hb; rw [hgf] at hb; cases hb
  · intro hp; rw [hgf] at hp; cases hp
  · intro hb; rw [hgf] at hb; cases hb
  · intro hu; rw [hgf] at hu; cases hu
  · intro hw; rw [hgf] at hw; cases hw

/-- The endpoint rights a task holds now are rights it held at boot. -/
theorem boot_rights {j : Nat} {c : Cap} {e : Nat} (h : CapOK j c) (he : c.obj = .endpoint e) :
    ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ RLe c.rights c0.rights ∧ c0.badge = c.badge :=
  h.endpoint e he

theorem grantOf_some {t : Task} {ep g : Cap} {gi : Nat} (h : grantOf t ep gi = some (some g)) :
    ep.rights.x = true ∧ g ∈ t.caps ∧ ∃ b n, g.obj = .frames b n := by
  unfold grantOf at h
  split at h
  · simp at h
  · split at h
    · rename_i hx
      split at h
      · rename_i g' hg'
        split at h
        · rename_i b n hf
          simp at h; subst h
          exact ⟨hx, nth?_mem hg', b, n, hf⟩
        · simp at h
      · simp at h
    · simp at h

theorem grantOf_none {t : Task} {ep : Cap} {gi : Nat} (g : Option Cap)
    (h : grantOf t ep gi = some g) : ∀ g', g = some g' → grantOf t ep gi = some (some g') := by
  intro g' hg; subst hg; exact h

/-! ## Finding the other side of a message -/

theorem findReceiver_spec {e : Nat} : ∀ {ts : List Task} {k j : Nat},
    findReceiver e ts k = some j → k ≤ j ∧ ∃ u d, nth? ts (j - k) = some u ∧ u.status = .receiving e d
  | [], _, _, h => by simp [findReceiver] at h
  | t :: ts, k, j, h => by
    simp only [findReceiver] at h
    split at h
    · rename_i hr
      simp at h; subst h
      unfold isReceiving at hr
      split at hr
      · rename_i e' d hst; simp at hr; subst hr; exact ⟨Nat.le_refl _, t, d, by simp [nth?], hst⟩
      · simp at hr
    · obtain ⟨hk, u, d, hu, hst⟩ := findReceiver_spec h
      refine ⟨by omega, u, d, ?_, hst⟩
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this]; simpa [nth?] using hu

theorem sendingAt_spec {e : Nat} {ts : List Task} {j : Nat} {m : Msg} (h : sendingAt e ts j = some m) :
    ∃ u, nth? ts j = some u ∧ u.status = .sending e m := by
  unfold sendingAt at h
  split at h
  · rename_i u hu
    refine ⟨u, hu, ?_⟩
    unfold sendingMsg at h
    split at h
    · rename_i e' m' hst
      split at h
      · rename_i hee; simp at hee h; subst hee; subst h; exact hst
      · simp at h
    · simp at h
  · simp at h

theorem findSender_spec {e : Nat} : ∀ {ts : List Task} {i fuel j : Nat} {m : Msg},
    findSender e ts i fuel = some (j, m) → ∃ u, nth? ts j = some u ∧ u.status = .sending e m
  | _, _, 0, _, _, h => by simp [findSender] at h
  | ts, i, fuel + 1, j, m, h => by
    simp only [findSender] at h
    split at h
    · rename_i m' hm
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact sendingAt_spec hm
    · exact findSender_spec h

/-- What a delivery can change: the receiver's capabilities grow by at most the granted one,
its mappings stay the same, and it becomes ready. -/
theorem deliver_spec {u u' : Task} {m : Msg} {sender : Nat} (hd : deliver u m sender = some u') :
    u'.maps = u.maps ∧ u'.status = .ready ∧ u'.hash = u.hash ∧
      (u'.caps = u.caps ∨ ∃ c, m.grant = some c ∧ u'.caps = snoc u.caps c) := by
  unfold deliver at hd
  dsimp only at hd
  repeat' split at hd
  all_goals first
    | (simp at hd; done)
    | (simp only [Option.some.injEq] at hd; subst hd
       first
         | exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
         | exact ⟨rfl, rfl, rfl, Or.inr ⟨_, by assumption, rfl⟩⟩)

/-- Receiving a message leaves a task fine, as long as a granted capability is fine for it. -/
theorem deliver_ok {fb : Bool} {j : Nat} {u u' : Task} {m : Msg} {sender : Nat}
    (hu : TaskOK fb j u) (hm : openSlot j = false → u.hash = expectedHash j) (hg : ∀ g, m.grant = some g → CapOK j g)
    (hd : deliver u m sender = some u') : TaskOK fb j u' := by
  obtain ⟨hmaps, hst, hhash, hcaps⟩ := deliver_spec hd
  have hcap : ∀ c ∈ u'.caps, c ∈ u.caps ∨ CapOK j c := by
    intro c hc
    rcases hcaps with h | ⟨g, hg', h⟩
    · rw [h] at hc; exact Or.inl hc
    · rw [h] at hc
      rcases mem_snoc.1 hc with h1 | h1
      · exact Or.inl h1
      · subst h1; exact Or.inr (hg _ hg')
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ ho => hhash.trans (hm ho)⟩
  · intro mp hmp
    rw [hmaps] at hmp
    obtain ⟨c, hc, h1, h2⟩ := hu.backed mp hmp
    refine ⟨c, ?_, h1, h2⟩
    rcases hcaps with h | ⟨g, -, h⟩
    · rw [h]; exact hc
    · rw [h]; exact mem_snoc.2 (Or.inl hc)
  · intro mp hmp; rw [hmaps] at hmp; exact hu.vpnOk mp hmp
  · intro c hc
    rcases hcap c hc with h | h
    · exact hu.caps c h
    · exact h
  · rw [hst]; trivial
  · intro mp hmp; rw [hmaps] at hmp; exact hu.fbMaps mp hmp

/-! ## System calls preserve the invariant -/

theorem inv_ret {s : KState} {t : Task} (hs : Inv s) (ht : TaskOK (fbSane s.fbBase) s.cur t) (r : List Nat) :
    Inv (ret s t r).state :=
  inv_setTask hs (ht.result r)

theorem inv_sysMap {s : KState} {t : Task} {ci vpn : Nat} (hs : Inv s) (ht : TaskOK (fbSane s.fbBase) s.cur t) :
    Inv (sysMap s t ci vpn).state := by
  unfold sysMap
  split
  · exact inv_ret hs ht _
  · rename_i c hc
    have hcm := nth?_mem hc
    split
    · rename_i base count hf
      split
      · rename_i hcond
        simp only [validRun, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcond
        refine inv_setTask hs ⟨?_, ?_, ht.caps, ht.status, ?_, ht.measured⟩
        · intro m hm
          rcases mem_app.1 hm with hm | hm
          · obtain ⟨k, hk, -, hf', hr⟩ := mem_runMaps hm
            exact ⟨c, hcm, ⟨base, count, hf, by omega, by omega⟩, hr.symm⟩
          · exact ht.backed m (mem_dropRange.1 hm).1
        · intro m hm
          rcases mem_app.1 hm with hm | hm
          · obtain ⟨k, hk, hv, -, -⟩ := mem_runMaps hm
            omega
          · exact ht.vpnOk m (mem_dropRange.1 hm).1
        · intro m hm
          rcases mem_app.1 hm with hm | hm
          · obtain ⟨k, hk, -, hf', -⟩ := mem_runMaps hm
            rcases hcond.2 with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · exact Or.inl (by omega)
            · exact Or.inr (Or.inl ⟨h1, by omega⟩)
            · exact Or.inr (Or.inr (by omega))
          · exact ht.fbMaps m (mem_dropRange.1 hm).1
      · exact inv_ret hs ht _
    · exact inv_ret hs ht _

theorem inv_sysUnmap {s : KState} {t : Task} {vpn count : Nat} (hs : Inv s) (ht : TaskOK (fbSane s.fbBase) s.cur t) :
    Inv (sysUnmap s t vpn count).state :=
  inv_setTask hs ⟨fun m hm => ht.backed m (mem_dropRange.1 hm).1,
    fun m hm => ht.vpnOk m (mem_dropRange.1 hm).1, ht.caps, ht.status,
    fun m hm => ht.fbMaps m (mem_dropRange.1 hm).1, ht.measured⟩

theorem inv_sysDerive {s : KState} {t : Task} {ci bits off cnt : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysDerive s t ci bits off cnt).state := by
  unfold sysDerive
  split
  · exact inv_ret hs ht _
  · rename_i c hc
    split
    · exact inv_ret hs ht _
    · rename_i o ho
      split
      · apply inv_ret hs
        refine ⟨?_, ht.vpnOk, ?_, ht.status, ht.fbMaps, ht.measured⟩
        · intro m hm
          obtain ⟨c0, hc0, h1, h2⟩ := ht.backed m hm
          exact ⟨c0, mem_snoc.2 (Or.inl hc0), h1, h2⟩
        · intro c' hc'
          rcases mem_snoc.1 hc' with h | h
          · exact ht.caps c' h
          · subst h; exact capOK_derive (ht.caps c (nth?_mem hc)) ho _
      · exact inv_ret hs ht _

theorem inv_sysCapInfo {s : KState} {t : Task} {ci : Nat} (hs : Inv s) (ht : TaskOK (fbSane s.fbBase) s.cur t) :
    Inv (sysCapInfo s t ci).state := by
  unfold sysCapInfo
  split
  · exact inv_ret hs ht _
  · split <;> exact inv_ret hs ht _

theorem inv_sysWrite {s : KState} {t : Task} {va n : Nat} (hs : Inv s) (ht : TaskOK (fbSane s.fbBase) s.cur t) :
    Inv (sysWrite s t va n).state := by
  unfold sysWrite
  split
  · exact inv_ret hs ht _
  · split
    · exact inv_setTask hs (ht.result _)
    · exact inv_ret hs ht _

theorem inv_sysSend {s : KState} {t : Task} {ci w0 w1 w2 gi : Nat} {call : Bool} (hs : Inv s)
    (hcur : nth? s.tasks s.cur = some t) (hmt : openSlot s.cur = false → t.hash = expectedHash s.cur) :
    Inv (sysSend s t ci w0 w1 w2 gi call).state := by
  have ht := hs.tasks _ _ hcur
  have hA := hs.lt hcur
  unfold sysSend
  split
  · exact inv_ret hs ht _
  · rename_i c hc
    have hcok := ht.caps c (nth?_mem hc)
    split
    rotate_left
    · exact inv_ret hs ht _
    · rename_i e he
      obtain ⟨c0, hc0, ho0, hle0, hb0⟩ := boot_rights hcok he
      split
      · rename_i hw
        split
        · exact inv_ret hs ht _
        · rename_i g hg
          -- a granted capability is a frame the sender may hold, through a grant-right endpoint
          have hgr : ∀ g', g = some g' → CapOK s.cur g' ∧ (∃ b n, g'.obj = .frames b n) ∧
              ∃ c1 ∈ initCaps s.cur, c1.obj = .endpoint e ∧ c1.rights.w = true ∧
                c1.rights.x = true := by
            intro g' hg'
            subst hg'
            obtain ⟨hx, hgm, hf⟩ := grantOf_some hg
            exact ⟨ht.caps g' hgm, hf, c0, hc0, ho0, hle0.2.1 hw, hle0.2.2 hx⟩
          dsimp only
          split
          · rename_i j hj
            obtain ⟨-, u0, d0, hu0, hst⟩ := findReceiver_spec hj
            rw [Nat.sub_zero] at hu0
            split
            · rename_i u hu
              rw [hu] at hu0; simp at hu0; subst hu0
              have huok := hs.tasks j u hu
              have hB := hs.lt hu
              split
              · rename_i u' hd
                have hrecv := huok.status
                rw [hst] at hrecv
                obtain ⟨c1, hc1, ho1, hr1⟩ := hrecv
                have hdel : Inv (setTask s j u') := by
                  apply inv_setTask hs (deliver_ok huok (huok.measured (by rw [hst]; trivial)) ?_ hd)
                  intro g' hg'
                  obtain ⟨hgok, hgf, c2, hc2, ho2, hw2, hx2⟩ := hgr g' hg'
                  exact capOK_grant hgok hgf ⟨hA, hB, e, ⟨c2, hc2, ho2, hw2, hx2⟩, ⟨c1, hc1, ho1, hr1⟩⟩
                split
                · exact inv_schedule (inv_wake (inv_setTask hdel (ht.setStatus (.awaiting j) trivial (fun _ => hmt) _)) j)
                · exact inv_ret (inv_wake hdel j) ht _
              · exact inv_ret hs ht _
            · exact inv_ret hs ht _
          · apply inv_schedule
            exact inv_setTask hs (ht.setStatus (.sending e ⟨c.badge, w0, w1, w2, g, call⟩)
              ⟨⟨c0, hc0, ho0, hle0.2.1 hw, hb0⟩, fun g' hg' => hgr g' hg'⟩ (fun _ => hmt) _)
      · exact inv_ret hs ht _

theorem inv_sysRecv {s : KState} {t : Task} {ci : Nat} {block : Bool} {deadline : Nat} (hs : Inv s)
    (hcur : nth? s.tasks s.cur = some t) (hmt : openSlot s.cur = false → t.hash = expectedHash s.cur) :
    Inv (sysRecv s t ci block deadline).state := by
  have ht := hs.tasks _ _ hcur
  have hB := hs.lt hcur
  unfold sysRecv
  split
  · exact inv_ret hs ht _
  · rename_i c hc
    have hcok := ht.caps c (nth?_mem hc)
    split
    rotate_left
    · exact inv_ret hs ht _
    · rename_i e he
      obtain ⟨c0, hc0, ho0, hle0, -⟩ := boot_rights hcok he
      split
      · rename_i hr
        split
        · rename_i j m hj
          obtain ⟨u0, hu0, hst⟩ := findSender_spec hj
          split
          · rename_i u hu
            rw [hu] at hu0; simp at hu0; subst hu0
            have huok := hs.tasks j u hu
            have hA := hs.lt hu
            have hsend := huok.status
            rw [hst] at hsend
            obtain ⟨-, hgrant⟩ := hsend
            split
            · rename_i t' hd
              dsimp only
              have h1 : Inv (setTask s j (if m.call then { u with status := .awaiting s.cur, result := .nil }
                  else { u with status := .ready, result := 0 :: .nil })) := by
                split
                · exact inv_setTask hs (huok.setStatus (.awaiting s.cur) trivial
                    (fun _ => huok.measured (by rw [hst]; trivial)) _)
                · exact inv_setTask hs (huok.setStatus .ready trivial
                    (fun _ => huok.measured (by rw [hst]; trivial)) _)
              -- `try`: a receive that forgot whom it served must break `recv_in_turn`, not this
              try apply inv_serve
              refine inv_wakeSender ?_ _ j
              apply inv_setTask h1
              apply deliver_ok ht hmt _ hd
              intro g hg
              obtain ⟨hgok, hgf, c2, hc2, ho2, hw2, hx2⟩ := hgrant g hg
              exact capOK_grant hgok hgf ⟨hA, hB, e, ⟨c2, hc2, ho2, hw2, hx2⟩,
                ⟨c0, hc0, ho0, hle0.1 hr⟩⟩
            · exact inv_ret hs ht _
          · exact inv_ret hs ht _
        · split
          · apply inv_schedule
            exact inv_setTask hs (ht.setStatus (.receiving e _) ⟨c0, hc0, ho0, hle0.1 hr⟩ (fun _ => hmt) _)
          · exact inv_ret hs ht _
      · exact inv_ret hs ht _

theorem TaskOK.setCallers {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (cs : List Nat) :
    TaskOK fb j { t with callers := cs } := ⟨h.backed, h.vpnOk, h.caps, h.status, h.fbMaps, h.measured⟩

theorem awaitsFrom_spec {ts : List Task} {j server : Nat} (h : awaitsFrom ts j server = true) :
    ∃ u, nth? ts j = some u ∧ u.status = .awaiting server := by
  unfold awaitsFrom at h
  split at h
  · rename_i u hu
    split at h
    · rename_i k hk; simp at h; subst h; exact ⟨u, hu, hk⟩
    · simp at h
  · simp at h

theorem inv_sysReply {s : KState} {t : Task} {slot w0 w1 w2 : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysReply s t slot w0 w1 w2).state := by
  unfold sysReply
  split
  · exact inv_ret hs ht _
  · rename_i j hj
    dsimp only
    split
    · rename_i haw
      split
      · rename_i u hu
        have halive : Alive u.status := by
          obtain ⟨w, hw, hst⟩ := awaitsFrom_spec haw
          rw [hu] at hw; cases hw; rw [hst]; trivial
        exact inv_ret (inv_wake (inv_setTask hs ((hs.tasks j u hu).setStatus .ready trivial
          (fun _ => (hs.tasks j u hu).measured halive) _)) j) (ht.setCallers _) _
      · exact inv_ret hs (ht.setCallers _) _
    · exact inv_ret hs (ht.setCallers _) _

theorem inv_sysIrqWait {s : KState} {t : Task} {ci : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) (hmt : openSlot s.cur = false → t.hash = expectedHash s.cur) :
    Inv (sysIrqWait s t ci).state := by
  unfold sysIrqWait
  split
  · exact inv_ret hs ht _
  · rename_i c hc
    split
    · rename_i n hn
      split
      · exact inv_ret (s := { s with pending := dropLine n s.pending }) ⟨hs.len, hs.tasks⟩ ht _
      · apply inv_schedule
        obtain ⟨c0, hc0, ho⟩ := (ht.caps c (nth?_mem hc)).irq n hn
        exact inv_setTask hs (ht.setStatus (.waitingIrq n) ⟨c0, hc0, ho⟩ (fun _ => hmt) _)
    · exact inv_ret hs ht _

theorem inv_sysIrqAck {s : KState} {t : Task} {ci : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysIrqAck s t ci).state := by
  unfold sysIrqAck
  split
  · exact inv_ret hs ht _
  · split
    · exact inv_ret hs ht _
    · exact inv_ret hs ht _

theorem findIrqWaiter_spec {n : Nat} : ∀ {ts : List Task} {k j : Nat},
    findIrqWaiter n ts k = some j → k ≤ j ∧ ∃ u, nth? ts (j - k) = some u ∧ u.status = .waitingIrq n
  | [], _, _, h => by simp [findIrqWaiter] at h
  | t :: ts, k, j, h => by
    simp only [findIrqWaiter] at h
    split at h
    · rename_i m hst
      split at h
      · rename_i hm
        simp at h hm; subst h; subst hm
        exact ⟨Nat.le_refl _, t, by simp [nth?], hst⟩
      · obtain ⟨hk, u, hu, hs⟩ := findIrqWaiter_spec h
        refine ⟨by omega, u, ?_, hs⟩
        have : j - k = (j - (k + 1)) + 1 := by omega
        rw [this]; simpa [nth?] using hu
    · obtain ⟨hk, u, hu, hs⟩ := findIrqWaiter_spec h
      refine ⟨by omega, u, ?_, hs⟩
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this]; simpa [nth?] using hu

theorem inv_irqFired {s : KState} (hs : Inv s) (n : Nat) : Inv (irqFired s n) := by
  unfold irqFired
  split
  · rename_i j hj
    split
    · rename_i u hu
      obtain ⟨-, u0, hu0, hst⟩ := findIrqWaiter_spec hj
      simp only [Nat.sub_zero] at hu0
      rw [hu] at hu0; cases hu0
      exact inv_preempt (inv_setTask hs ((hs.tasks j u hu).setStatus .ready trivial
        (fun _ => (hs.tasks j u hu).measured (by rw [hst]; trivial)) _)) j
    · exact hs
  · split
    · exact hs
    · exact ⟨hs.len, hs.tasks⟩

theorem inv_sysBootInfo {s : KState} {t : Task} {i : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysBootInfo s t i).state := by
  unfold sysBootInfo
  split <;> exact inv_ret hs ht _

/-! ## The boot manifest -/

theorem nth?_mkTasksFrom : ∀ (k n i : Nat),
    nth? (mkTasksFrom k n) i = if i < n then some (mkTask (k + i)) else none
  | k, 0, i => by simp [mkTasksFrom, nth?]
  | k, n + 1, 0 => by simp [mkTasksFrom, nth?]
  | k, n + 1, i + 1 => by
    simp only [mkTasksFrom, nth?, nth?_mkTasksFrom (k + 1) n i]
    congr 1 <;> simp [Nat.add_assoc, Nat.add_comm 1 i]

theorem len_mkTasksFrom : ∀ (k n : Nat), len (mkTasksFrom k n) = n
  | _, 0 => rfl
  | k, n + 1 => by simp [mkTasksFrom, len, len_mkTasksFrom (k + 1) n]

theorem cases17 {j : Nat} (h : j < numTasks) :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
      j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by
  simp [numTasks] at h; omega

-- Capabilities can be compared, so facts about single capabilities of the manifest can be
-- decided.
deriving instance DecidableEq for Rights, Obj, Cap

/-- Every capability the boot manifest gives any task passes the check `p`. Deciding this
is one evaluation of the manifest, far cheaper than a case for every task and capability. -/
def manifestAll (p : Nat → Cap → Bool) : Bool :=
  (List.range numTasks).all fun j => (initCaps j).all (p j)

/-- What `manifestAll` says about one capability of one task. -/
theorem manifestAll_spec {p : Nat → Cap → Bool} (h : manifestAll p = true) {j : Nat} {c : Cap}
    (hj : j < numTasks) (hc : c ∈ initCaps j) : p j c = true := by
  unfold manifestAll at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact h j hj c hc

/-- At boot, every frame a task holds is its own (`owner`), read-execute or read-write. -/
theorem initCaps_frame {j f : Nat} {c : Cap} (hj : j < numTasks) (hc : c ∈ initCaps j)
    (hf : Covers c f) : owner f = j ∧ f < devBase + devPages ∧ ¬ WX c.rights := by
  obtain ⟨b, n, ho, h1, h2⟩ := hf
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .frames b n => !(c.rights.w && c.rights.x) &&
        ((Nat.ble (b + n) poolFrames && b / framesPerTask == j && (b + n - 1) / framesPerTask == j) ||
          ((Nat.ble poolFrames b && Nat.ble (b + n) devBase && j == displayTask) ||
            (Nat.ble devBase b && Nat.ble (b + n) (devBase + devPages) && j == inputTask)))
    | _ => true) (by decide) hj hc
  simp only [ho, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq, beq_iff_eq] at this
  obtain ⟨hwx, hr⟩ := this
  refine ⟨?_, ?_, fun ⟨hw, hx⟩ => by simp [hw, hx] at hwx⟩
  · unfold owner
    split <;> (try split) <;>
      simp only [poolFrames, framesPerTask, maxTasks, devBase, fbPages, devPages, displayTask,
        inputTask] at * <;> omega
  · simp only [poolFrames, framesPerTask, maxTasks, devBase, fbPages, devPages] at hr ⊢
    omega

/-- A run inside one slot's frames, or wholly outside the pool, never spans two slots. -/
theorem runOK_of {c : Cap} {b n : Nat} (ho : c.obj = .frames b n)
    (h : (b + n ≤ poolFrames ∧ b / 256 = (b + n - 1) / 256) ∨ poolFrames ≤ b) : RunOK c := by
  intro f f' ⟨b1, n1, h1, hb1, hn1⟩ ⟨b2, n2, h2, hb2, hn2⟩ hp
  rw [ho] at h1 h2; cases h1; cases h2
  simp only [poolFrames, framesPerTask, maxTasks] at h hp ⊢
  omega

/-- At boot, no run spans two slots. -/
theorem initCaps_run {j : Nat} {c : Cap} (hj : j < numTasks) (hc : c ∈ initCaps j) : RunOK c := by
  intro f f' hf hf'
  have ⟨b, n, ho, _, _⟩ := hf
  apply runOK_of ho _ f f' hf hf'
  have := manifestAll_spec (p := fun _ c => match c.obj with
    | .frames b n => (Nat.ble (b + n) poolFrames && b / 256 == (b + n - 1) / 256) || Nat.ble poolFrames b
    | _ => true) (by decide) hj hc
  simpa [ho] using this

theorem initCap_ok {j : Nat} {c : Cap} (hj : j < numTasks) (hc : c ∈ initCaps j) : CapOK j c where
  frames f hf := by
    have ⟨_, hlt, hwx⟩ := initCaps_frame hj hc hf
    exact ⟨hlt, hwx, j, c, hj, Reach.refl j, hc, hf, RLe.refl _⟩
  endpoint e he := ⟨c, hc, he, RLe.refl _, rfl⟩
  irq n hn := ⟨c, hc, hn⟩
  launch k hk := ⟨c, hc, hk⟩
  blocks b n hb := ⟨c, hc, hb, RLe.refl _⟩
  power hp := ⟨c, hc, hp⟩
  board hb := ⟨c, hc, hb⟩
  usb hu := ⟨c, hc, hu⟩
  wall hw := ⟨c, hc, hw⟩
  run := initCaps_run hj hc

/-- Every task holds its own frames at boot. -/
theorem frameCaps_initCaps {j : Nat} {c : Cap} (h : c ∈ frameCaps j) : c ∈ initCaps j := by
  unfold initCaps; split <;> simp only [mem_snoc, h, true_or]

theorem mkTask_ok {fb : Bool} {j : Nat} (hj : j < numTasks) : TaskOK fb j (mkTask j) := by
  refine ⟨?_, ?_, fun c hc => initCap_ok hj hc, trivial, ?_, fun h => by simp [mkTask, Alive] at h⟩
  · intro m hm
    simp only [mkTask, initMaps] at hm
    have hcode : runCap (256 * j) 16 Rights.rx ∈ initCaps j := frameCaps_initCaps (by simp [frameCaps])
    have hdata : runCap (256 * j + 16) 8 Rights.rw ∈ initCaps j := frameCaps_initCaps (by simp [frameCaps])
    have hstack : runCap (256 * j + 24) 4 Rights.rw ∈ initCaps j := frameCaps_initCaps (by simp [frameCaps])
    rcases mem_app.1 hm with hm | hm
    · obtain ⟨k, hk, -, hf, hr⟩ := mem_runMaps hm
      exact ⟨_, hcode, ⟨_, _, rfl, by omega, by omega⟩, hr.symm⟩
    · rcases mem_app.1 hm with hm | hm
      · obtain ⟨k, hk, -, hf, hr⟩ := mem_runMaps hm
        exact ⟨_, hdata, ⟨_, _, rfl, by omega, by omega⟩, hr.symm⟩
      · obtain ⟨k, hk, -, hf, hr⟩ := mem_runMaps hm
        exact ⟨_, hstack, ⟨_, _, rfl, by omega, by omega⟩, hr.symm⟩
  · intro m hm
    simp only [mkTask, initMaps] at hm
    rcases mem_app.1 hm with hm | hm
    · obtain ⟨k, hk, hv, -⟩ := mem_runMaps hm; simp [userPages]; omega
    · rcases mem_app.1 hm with hm | hm
      · obtain ⟨k, hk, hv, -⟩ := mem_runMaps hm; simp [userPages]; omega
      · obtain ⟨k, hk, hv, -⟩ := mem_runMaps hm; simp [userPages] at hv ⊢; omega
  · intro m hm
    left
    simp only [mkTask, initMaps] at hm
    have : j < 18 := by simpa [numTasks] using hj
    rcases mem_app.1 hm with hm | hm
    · obtain ⟨k, hk, -, hf, -⟩ := mem_runMaps hm; simp [poolFrames, framesPerTask, maxTasks]; omega
    · rcases mem_app.1 hm with hm | hm
      · obtain ⟨k, hk, -, hf, -⟩ := mem_runMaps hm; simp [poolFrames, framesPerTask, maxTasks]; omega
      · obtain ⟨k, hk, -, hf, -⟩ := mem_runMaps hm; simp [poolFrames, framesPerTask, maxTasks]; omega

theorem inv_init (fb : Nat) : Inv (init fb) := by
  constructor
  · simp [init, len_mkTasksFrom]
  · intro j t h
    simp only [init, nth?_mkTasksFrom, Nat.zero_add] at h
    split at h
    · simp at h; subst h; rename_i hj; exact mkTask_ok hj
    · simp at h

/-! ### Starting a program: taking back what it shared -/

theorem mem_dropCaps {k : Nat} : ∀ {cs : List Cap} {c : Cap},
    c ∈ dropCaps k cs → c ∈ cs ∧ capInSlot k c = false
  | [], c, h => by simp [dropCaps] at h
  | x :: cs, c, h => by
    unfold dropCaps at h
    split at h
    · have := mem_dropCaps h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · rename_i hx
      rcases List.mem_cons.1 h with h | h
      · subst h; exact ⟨List.mem_cons_self .., by simpa using hx⟩
      · have := mem_dropCaps h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem dropCaps_keep {k : Nat} : ∀ {cs : List Cap} {c : Cap},
    c ∈ cs → capInSlot k c = false → c ∈ dropCaps k cs
  | [], c, h, _ => by simp at h
  | x :: cs, c, h, hc => by
    unfold dropCaps
    rcases List.mem_cons.1 h with h | h
    · subst h; simp [hc]
    · split
      · exact dropCaps_keep h hc
      · exact List.mem_cons_of_mem _ (dropCaps_keep h hc)

theorem mem_dropMaps {k : Nat} : ∀ {ms : List Mapping} {m : Mapping},
    m ∈ dropMaps k ms → m ∈ ms ∧ inSlot k m.frame = false
  | [], m, h => by simp [dropMaps] at h
  | x :: ms, m, h => by
    unfold dropMaps at h
    split at h
    · have := mem_dropMaps h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · rename_i hx
      rcases List.mem_cons.1 h with h | h
      · subst h; exact ⟨List.mem_cons_self .., by simpa using hx⟩
      · have := mem_dropMaps h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- A capability that revocation keeps covers none of the slot's frames. -/
theorem kept_covers {k : Nat} {c : Cap} (hr : RunOK c) (hk : capInSlot k c = false) {f : Nat}
    (hf : Covers c f) : inSlot k f = false := by
  obtain ⟨b, n, ho, h1, h2⟩ := hf
  simp only [capInSlot, ho] at hk
  cases hs : inSlot k f
  · rfl
  · simp only [inSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    have := hr f b ⟨b, n, ho, h1, h2⟩ ⟨b, n, ho, Nat.le_refl _, by omega⟩ hs.1
    simp [inSlot, this.1, ← this.2, hs.2] at hk

/-- A mapping that revocation keeps is still backed: the capability behind it is kept too. -/
theorem backer_kept {k : Nat} {c : Cap} (hr : RunOK c) {f : Nat} (hf : Covers c f)
    (hk : inSlot k f = false) : capInSlot k c = false := by
  obtain ⟨b, n, ho, h1, h2⟩ := hf
  simp only [capInSlot, ho]
  cases hs : inSlot k b
  · rfl
  · simp only [inSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    have := hr b f ⟨b, n, ho, Nat.le_refl _, by omega⟩ ⟨b, n, ho, h1, h2⟩ hs.1
    simp [inSlot, this.1, ← this.2, hs.2] at hk

theorem statusOK_scrub {j k : Nat} {st : Status} (h : StatusOK j st) :
    StatusOK j (scrubStatus k st) := by
  cases st
  case sending e m =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, fun g hg => h2 g ?_⟩
    revert hg
    simp only
    cases hm : m.grant with
    | none => simp
    | some c => by_cases hc : capInSlot k c = true <;> simp [hc]
  all_goals exact h

theorem alive_scrub {k : Nat} {st : Status} (h : Alive (scrubStatus k st)) : Alive st := by
  cases st <;> exact h

theorem TaskOK.revoke {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (k : Nat) :
    TaskOK fb j (revokeTask k t) where
  backed m hm := by
    obtain ⟨hm, hk⟩ := mem_dropMaps hm
    obtain ⟨c, hc, hcov, hr⟩ := h.backed m hm
    exact ⟨c, dropCaps_keep hc (backer_kept (h.caps c hc).run hcov hk), hcov, hr⟩
  vpnOk m hm := h.vpnOk m (mem_dropMaps hm).1
  caps c hc := h.caps c (mem_dropCaps hc).1
  status := statusOK_scrub h.status
  fbMaps m hm := h.fbMaps m (mem_dropMaps hm).1
  measured ha := h.measured (alive_scrub ha)

theorem nth?_revokeAll (k : Nat) : ∀ (ts : List Task) (j : Nat),
    nth? (revokeAll k ts) j = (nth? ts j).map (revokeTask k)
  | [], j => by simp [revokeAll, nth?]
  | t :: ts, 0 => by simp [revokeAll, nth?]
  | t :: ts, j + 1 => by simp [revokeAll, nth?, nth?_revokeAll k ts j]

theorem len_revokeAll (k : Nat) : ∀ (ts : List Task), len (revokeAll k ts) = len ts
  | [] => rfl
  | t :: ts => by simp [revokeAll, len, len_revokeAll k ts]

theorem inv_revoke {s : KState} (hs : Inv s) (k : Nat) :
    Inv { s with tasks := revokeAll k s.tasks } where
  len := by simp [len_revokeAll, hs.len]
  tasks j u hu := by
    dsimp only at hu
    rw [nth?_revokeAll] at hu
    cases h : nth? s.tasks j with
    | none => simp [h] at hu
    | some t => simp [h] at hu; subst hu; exact (hs.tasks j t h).revoke k

theorem inv_sysStart {s : KState} {t : Task} {ci src len : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysStart s t ci src len).state := by
  unfold sysStart
  split <;> (try exact inv_ret hs ht _)
  split <;> (try exact inv_ret hs ht _)
  rename_i k _
  split <;> (try exact inv_ret hs ht _)
  rename_i u hu
  split <;> (try exact inv_ret hs ht _)
  have h1 : Inv (setTask { s with tasks := revokeAll k s.tasks } k (mkTask k)) :=
    inv_setTask (inv_revoke hs k) (mkTask_ok (hs.lt hu))
  dsimp only
  split
  · rename_i t1 ht1
    exact inv_setTask h1 ((h1.tasks _ _ ht1).result _)
  · exact inv_ret hs ht _

/-! ### Dropping a capability -/

theorem mem_removeNth {α : Type} : ∀ {l : List α} {i : Nat} {a : α}, a ∈ removeNth l i → a ∈ l
  | [], _, _, h => by simp [removeNth] at h
  | x :: l, 0, a, h => List.mem_cons_of_mem _ h
  | x :: l, n + 1, a, h => by
    simp only [removeNth, List.mem_cons] at h
    rcases h with h | h
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_removeNth h)

theorem coversB_spec {c : Cap} {f : Nat} (h : coversB c f = true) : Covers c f := by
  unfold coversB at h
  split at h
  · rename_i b n ho
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    exact ⟨b, n, ho, h.1, by omega⟩
  · simp at h

theorem sameRights_spec {a b : Rights} (h : sameRights a b = true) : a = b := by
  cases a; cases b
  simp only [sameRights, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  subst h1; subst h2; subst h3; rfl

theorem backedBy_spec : ∀ {cs : List Cap} {m : Mapping}, backedBy cs m = true →
    ∃ c ∈ cs, Covers c m.frame ∧ c.rights = m.rights
  | [], m, h => by simp [backedBy] at h
  | c :: cs, m, h => by
    simp only [backedBy, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨c, List.mem_cons_self .., coversB_spec h1, sameRights_spec h2⟩
    · obtain ⟨c', hc', h'⟩ := backedBy_spec h
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩

theorem mem_keepBacked {cs : List Cap} : ∀ {ms : List Mapping} {m : Mapping},
    m ∈ keepBacked cs ms → m ∈ ms ∧ backedBy cs m = true
  | [], m, h => by simp [keepBacked] at h
  | x :: ms, m, h => by
    unfold keepBacked at h
    split at h
    · rename_i hx
      rcases List.mem_cons.1 h with h | h
      · subst h; exact ⟨List.mem_cons_self .., hx⟩
      · have := mem_keepBacked h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · have := mem_keepBacked h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem inv_sysDrop {s : KState} {t : Task} {ci : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysDrop s t ci).state := by
  unfold sysDrop
  split
  · exact inv_ret hs ht _
  · apply inv_setTask hs
    refine ⟨?_, ?_, ?_, ht.status, ?_, ht.measured⟩
    · intro m hm; exact backedBy_spec (mem_keepBacked hm).2
    · intro m hm; exact ht.vpnOk m (mem_keepBacked hm).1
    · intro c hc; exact ht.caps c (mem_removeNth hc)
    · intro m hm; exact ht.fbMaps m (mem_keepBacked hm).1

theorem inv_sysBlock {s : KState} {t : Task} {ci idx va k : Nat} {w : Bool} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysBlock s t ci idx va k w).state := by
  unfold sysBlock
  repeat' split
  all_goals first
    | exact inv_ret hs ht _
    | exact inv_setTask hs (ht.result _)

theorem inv_ioFailed {s : KState} (hs : Inv s) : Inv (ioFailed s) := by
  unfold ioFailed
  split
  · rename_i t ht; exact inv_setTask hs ((hs.tasks _ t ht).result _)
  · exact hs

/-! ### Power -/

theorem inv_sysPower {s : KState} {t : Task} {ci a : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysPower s t ci a).state := by
  unfold sysPower
  repeat' split
  all_goals first
    | exact inv_ret hs ht _
    | exact inv_setTask hs (ht.result _)

theorem inv_sysBoard {s : KState} {t : Task} {ci w v : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysBoard s t ci w v).state := by
  unfold sysBoard
  repeat' (first | split | dsimp only)
  all_goals first
    | exact inv_ret hs ht _
    | exact inv_setTask hs (ht.result _)

/-- The USB channel shadows are not part of the invariant. -/
theorem inv_usbFields {s : KState} (hs : Inv s) (d z : List Nat) :
    Inv { s with usbDma := d, usbSize := z } :=
  ⟨hs.len, hs.tasks⟩

/-- To show something of an `if`, show it of both branches. Much cheaper than `split` on a
tree of `if`s whose conditions are long. -/
theorem of_ite {α : Sort _} {P : α → Prop} {c : Prop} [Decidable c] {a b : α} (ha : P a) (hb : P b) :
    P (if c then a else b) := by
  split <;> assumption

theorem inv_sysUsb {s : KState} {t : Task} {ci op reg v : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysUsb s t ci op reg v).state := by
  unfold sysUsb usbReply
  split
  · exact inv_ret hs ht _
  split
  all_goals try exact inv_ret hs ht _
  repeat' (first | apply of_ite (P := fun r : Reply => Inv r.state) | dsimp only)
  all_goals first
    | exact inv_ret hs ht _
    | exact inv_setTask hs (ht.result _)
    | exact inv_ret (s := { s with usbDma := setNth s.usbDma (chanOf reg) v }) (inv_usbFields hs _ _) ht _
    | exact inv_ret (s := { s with usbSize := setNth s.usbSize (chanOf reg) v }) (inv_usbFields hs _ _) ht _

theorem inv_usbDone {s : KState} (hs : Inv s) (v : Nat) : Inv (usbDone s v) := by
  unfold usbDone
  split
  · rename_i t ht; exact inv_setTask hs ((hs.tasks _ t ht).result _)
  · exact hs

theorem inv_sysStop {s : KState} {t : Task} {ci : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysStop s t ci).state := by
  unfold sysStop
  split
  · exact inv_ret hs ht _
  · split
    · split
      · rename_i u hu
        split
        · exact inv_ret (inv_setTask hs ((hs.tasks _ u hu).setStatus .dead trivial (fun h => h.elim) _)) ht _
        · exact inv_ret hs ht _
      · exact inv_ret hs ht _
    · exact inv_ret hs ht _

theorem inv_sysSetWall {s : KState} {t : Task} {ci secs : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysSetWall s t ci secs).state := by
  unfold sysSetWall
  split
  · exact inv_ret hs ht _
  · split
    · split
      · exact inv_ret (s := { s with wall := secs - s.now * tickMs / 1000 }) ⟨hs.len, hs.tasks⟩ ht _
      · exact inv_ret hs ht _
    · exact inv_ret hs ht _

theorem inv_boardDone {s : KState} (hs : Inv s) (a b c d e : Nat) : Inv (boardDone s a b c d e) := by
  unfold boardDone
  split
  · rename_i t ht; exact inv_setTask hs ((hs.tasks _ t ht).result _)
  · exact hs

/-! ### Time -/

theorem TaskOK.wake {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (now : Nat) :
    TaskOK fb j (wakeTask now t) := by
  unfold wakeTask
  split
  · rename_i u hst
    split
    · exact h.setStatus .ready trivial (fun _ => h.measured (by rw [hst]; trivial)) _
    · exact h
  · rename_i e u hst
    split
    · exact h.setStatus .ready trivial (fun _ => h.measured (by rw [hst]; trivial)) _
    · exact h
  · exact h

theorem nth?_wakeSleepers (now : Nat) : ∀ (ts : List Task) (j : Nat),
    nth? (wakeSleepers now ts) j = (nth? ts j).map (wakeTask now)
  | [], j => by simp [wakeSleepers, nth?]
  | t :: ts, 0 => by simp [wakeSleepers, nth?]
  | t :: ts, j + 1 => by simp [wakeSleepers, nth?, nth?_wakeSleepers now ts j]

theorem len_wakeSleepers (now : Nat) : ∀ (ts : List Task), len (wakeSleepers now ts) = len ts
  | [] => rfl
  | t :: ts => by simp [wakeSleepers, len, len_wakeSleepers now ts]

theorem inv_tick {s : KState} (hs : Inv s) : Inv (tick s) := by
  unfold tick
  apply inv_rotate
  constructor
  · simp [len_wakeSleepers, hs.len]
  · intro j u hu
    dsimp only at hu
    rw [nth?_wakeSleepers] at hu
    cases h : nth? s.tasks j with
    | none => simp [h] at hu
    | some t => simp [h] at hu; subst hu; exact (hs.tasks j t h).wake _

theorem inv_sysSleep {s : KState} {t : Task} {ms : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) (hmt : openSlot s.cur = false → t.hash = expectedHash s.cur) :
    Inv (sysSleep s t ms).state := by
  unfold sysSleep
  dsimp only
  split
  · exact inv_schedule (inv_setTask hs (ht.result _))
  · exact inv_schedule (inv_setTask hs (ht.setStatus (.sleeping _) trivial (fun _ => hmt) _))

theorem inv_syscall {s : KState} (hs : Inv s) (num a0 a1 a2 a3 a4 : Nat) :
    Inv (syscall s num a0 a1 a2 a3 a4).state := by
  unfold syscall
  split
  · exact hs
  · rename_i t ht
    have hto := hs.tasks _ _ ht
    split
    · rename_i hrd
      have hmt : openSlot s.cur = false → t.hash = expectedHash s.cur := hto.measured (by rw [hrd]; trivial)
      unfold runCall
      split
      · exact inv_sysWrite hs hto
      · exact inv_schedule (inv_setTask hs (hto.result _))
      · exact inv_sysMap hs hto
      · exact inv_sysUnmap hs hto
      · exact inv_sysDerive hs hto
      · exact inv_killCurrent hs
      · exact inv_sysCapInfo hs hto
      · exact inv_ret hs hto _
      · exact inv_sysSend hs ht hmt
      · exact inv_sysRecv hs ht hmt
      · exact inv_sysSend hs ht hmt
      · exact inv_sysReply hs hto
      · exact inv_sysIrqWait hs hto hmt
      · exact inv_sysIrqAck hs hto
      · exact inv_sysBootInfo hs hto
      · exact inv_sysStart hs hto
      · exact inv_sysDrop hs hto
      · exact inv_sysBlock hs hto
      · exact inv_sysBlock hs hto
      · exact inv_sysStart hs hto
      · exact inv_sysSleep hs hto hmt
      · exact inv_sysPower hs hto
      · exact inv_ret hs hto _
      · exact inv_sysBoard hs hto
      · exact inv_sysUsb hs hto
      · exact inv_sysRecv hs ht hmt
      · exact inv_sysStop hs hto
      · exact inv_sysSetWall hs hto
      · exact inv_ret hs hto _
    · exact hs

/-! ## Verified boot -/

theorem eqList_spec : ∀ {a b : List Nat}, eqList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqList, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, eqList_spec h.2]
  | [], _ :: _, h => by simp [eqList] at h
  | _ :: _, [], h => by simp [eqList] at h

theorem inv_verify {s : KState} (hs : Inv s) (i : Nat) (h : List Nat) : Inv (verify s i h) := by
  unfold verify
  split
  · rename_i t ht
    split
    · split
      · rename_i heq
        have hok := hs.tasks i t ht
        exact inv_setTask hs ⟨hok.backed, hok.vpnOk, hok.caps, trivial, hok.fbMaps,
          fun _ ho => eqList_spec (by simpa [ho] using heq)⟩
      · have hok := hs.tasks i t ht
        exact inv_setTask hs ⟨hok.backed, hok.vpnOk, hok.caps, trivial, hok.fbMaps, fun h => h.elim⟩
    · exact hs
  · exact hs

/-! ## Reachable states -/

/-- The states the running kernel can be in: `init` (with whatever framebuffer address the
firmware returned), then any sequence of system calls,
timer ticks (`schedule`), faults (`killCurrent`), result loads (`clearResult`) and
interrupts (`irqFired`), and the boot-time checks of each task's code (`verify`), with any
measurement at all. -/
inductive Reachable : KState → Prop
  | init (fb : Nat) : Reachable (init fb)
  | syscall {s} (num a0 a1 a2 a3 a4 : Nat) : Reachable s →
      Reachable (syscall s num a0 a1 a2 a3 a4).state
  | tick {s} : Reachable s → Reachable (tick s)
  | fault {s} : Reachable s → Reachable (killCurrent s)
  | clear {s} (j : Nat) : Reachable s → Reachable (clearResult s j)
  | irq {s} (n : Nat) : Reachable s → Reachable (irqFired s n)
  | verify {s} (i : Nat) (h : List Nat) : Reachable s → Reachable (verify s i h)
  | ioFail {s} : Reachable s → Reachable (ioFailed s)
  | board {s} (a b c d e : Nat) : Reachable s → Reachable (boardDone s a b c d e)
  | usb {s} (v : Nat) : Reachable s → Reachable (usbDone s v)
  | enter {s} (c b0 b1 b2 : Nat) : Reachable s → Reachable (enter s c b0 b1 b2)
  | resched {s} : Reachable s → Reachable (schedule s)
  | rotate {s} : Reachable s → Reachable (rotate s)

theorem reachable_inv {s : KState} (h : Reachable s) : Inv s := by
  induction h with
  | init fb => exact inv_init fb
  | syscall num a0 a1 a2 a3 a4 _ ih => exact inv_syscall ih num a0 a1 a2 a3 a4
  | tick _ ih => exact inv_tick ih
  | fault _ ih => exact inv_killCurrent ih
  | clear j _ ih => exact inv_clearResult ih j
  | irq n _ ih => exact inv_irqFired ih n
  | verify i h _ ih => exact inv_verify ih i h
  | ioFail _ ih => exact inv_ioFailed ih
  | board a b c d e _ ih => exact inv_boardDone ih a b c d e
  | usb v _ ih => exact inv_usbDone ih v
  | enter c b0 b1 b2 _ ih => exact ⟨ih.len, ih.tasks⟩
  | resched _ ih => exact inv_schedule ih
  | rotate _ ih => exact inv_rotate ih

/-! ## The guarantees -/

/-- **Authority flow.** In every reachable state, a frame task `j` holds a capability to came
along a chain of grant edges from the task that owned it at boot (`owner f`: task `f / 64`
for the pool, the display server for the framebuffer), with no more rights than it had
at boot. -/
theorem frame_flow {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) :
    Reach (owner f) j ∧ ∃ c0 ∈ initCaps (owner f), Covers c0 f ∧ RLe c.rights c0.rights := by
  obtain ⟨-, -, A, c0, hA, hr, hc0, ho, hle⟩ :=
    ((reachable_inv h).tasks j t ht).caps c hc |>.frames f hf
  have := (initCaps_frame hA hc0 ho).1
  subst this
  exact ⟨hr, c0, hc0, ho, hle⟩

/-- Endpoint capabilities never grow: whatever a task holds for an endpoint, it held at
boot with at least those rights and the same badge. So no task can forge another's
badge or gain a right on an endpoint. -/
theorem endpoints_fixed {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {e : Nat}
    (he : c.obj = .endpoint e) :
    ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ RLe c.rights c0.rights ∧ c0.badge = c.badge :=
  ((reachable_inv h).tasks j t ht).caps c hc |>.endpoint e he

theorem maps_backed {s : KState} (h : Reachable s) {i : Nat} {t : Task}
    (ht : nth? s.tasks i = some t) :
    ∀ m ∈ t.maps, ∃ c ∈ t.caps, Covers c m.frame ∧ c.rights = m.rights :=
  ((reachable_inv h).tasks i t ht).backed

/-- **W^X.** No page of any task is ever both writable and executable. -/
theorem no_write_execute {s : KState} (h : Reachable s) {i : Nat} {t : Task}
    (ht : nth? s.tasks i = some t) : ∀ m ∈ t.maps, ¬ (m.rights.w = true ∧ m.rights.x = true) := by
  have hto := (reachable_inv h).tasks i t ht
  intro m hm
  obtain ⟨c, hc, hf, hr⟩ := hto.backed m hm
  rw [← hr]
  exact ((hto.caps c hc).frames _ hf).2.1

/-- Every mapping is in the user window and names a frame in the pool. -/
theorem maps_in_range {s : KState} (h : Reachable s) {i : Nat} {t : Task}
    (ht : nth? s.tasks i = some t) :
    ∀ m ∈ t.maps, m.vpn < userPages ∧ m.frame < devBase + devPages := by
  have hto := (reachable_inv h).tasks i t ht
  intro m hm
  obtain ⟨c, hc, hf, _⟩ := hto.backed m hm
  exact ⟨hto.vpnOk m hm, ((hto.caps c hc).frames _ hf).1⟩

/-- A page a task can see belongs, at boot, to a task that can reach it. -/
theorem mapping_flow {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {m : Mapping} (hm : m ∈ t.maps) : Reach (owner m.frame) j := by
  obtain ⟨c, hc, hf, _⟩ := maps_backed h ht m hm
  exact (frame_flow h ht hc hf).1

/-- **No amplification.** A derived capability covers only frames its parent covers, names
the same endpoint if its parent names one, keeps the badge, and allows nothing the parent
does not. -/
theorem derive_never_amplifies (c : Cap) (bits off cnt : Nat) (o : Obj)
    (ho : subObj c.obj off cnt = some o) :
    let d : Cap := ⟨o, c.rights.meet (Rights.ofBits bits), c.badge⟩
    (∀ f, Covers d f → Covers c f) ∧ (∀ e, d.obj = .endpoint e → c.obj = .endpoint e) ∧
      d.badge = c.badge ∧ RLe d.rights c.rights :=
  ⟨fun _ hf => subObj_covers ho hf, fun _ he => subObj_endpoint ho he, rfl, meet_le _ _⟩

/-! ## Replies -/

/-- Every task has the same capabilities and mappings in `s'` as in `s`. -/
def SameAuthority (s s' : KState) : Prop :=
  ∀ j u u', nth? s.tasks j = some u → nth? s'.tasks j = some u' → u'.caps = u.caps ∧ u'.maps = u.maps

theorem SameAuthority.trans {s1 s2 s3 : KState} (h1 : SameAuthority s1 s2) (h2 : SameAuthority s2 s3)
    (hl : ∀ j u, nth? s1.tasks j = some u → ∃ v, nth? s2.tasks j = some v) : SameAuthority s1 s3 := by
  intro j u u' hu hu'
  obtain ⟨v, hv⟩ := hl j u hu
  obtain ⟨c1, m1⟩ := h1 j u v hu hv
  obtain ⟨c2, m2⟩ := h2 j v u' hv hu'
  exact ⟨c2.trans c1, m2.trans m1⟩

/-- Replacing task `k` by a task with the same capabilities and mappings. -/
theorem sameAuthority_setTask {s : KState} {k : Nat} {v' : Task}
    (h : ∀ v, nth? s.tasks k = some v → v'.caps = v.caps ∧ v'.maps = v.maps) :
    SameAuthority s (setTask s k v') := by
  intro j u u' hu hu'
  simp only [setTask, nth?_setNth] at hu'
  by_cases hk : k = j
  · subst hk; simp [hu] at hu'; subst hu'; exact h u hu
  · simp [hk, hu] at hu'; subst hu'; exact ⟨rfl, rfl⟩

theorem nth?_setTask_some {s : KState} {k j : Nat} {v' u : Task} (hu : nth? s.tasks j = some u) :
    ∃ w, nth? (setTask s k v').tasks j = some w := by
  simp only [setTask, nth?_setNth]
  by_cases hk : k = j
  · subst hk; simp [hu]
  · simp [hk, hu]

/-- **A reply grants nothing.** No task's capabilities or mappings change when a task
replies. -/
theorem reply_grants_nothing {s : KState} {t : Task} (ht : nth? s.tasks s.cur = some t)
    (slot w0 w1 w2 : Nat) : SameAuthority s (sysReply s t slot w0 w1 w2).state := by
  have hcurT : ∀ (t' : Task), t'.caps = t.caps → t'.maps = t.maps →
      SameAuthority s (setTask s s.cur t') := by
    intro t' hc hm
    apply sameAuthority_setTask
    intro v hv; rw [ht] at hv; cases hv; exact ⟨hc, hm⟩
  unfold sysReply
  split
  · exact hcurT _ rfl rfl
  · rename_i j hj
    dsimp only
    split
    · split
      · rename_i u hu
        -- first the caller wakes, then the replier's slot is freed
        have h1 : SameAuthority s (setTask s j { u with status := .ready, result := 0 :: w0 :: w1 :: w2 :: .nil }) :=
          sameAuthority_setTask (fun v hv => by rw [hu] at hv; cases hv; exact ⟨rfl, rfl⟩)
        refine SameAuthority.trans h1 ?_ (fun k v hv => nth?_setTask_some hv)
        apply sameAuthority_setTask
        intro v hv
        simp only [setTask, nth?_setNth] at hv
        by_cases hjc : j = s.cur
        · subst hjc; rw [hu] at ht; cases ht; simp [hu] at hv; subst hv; exact ⟨rfl, rfl⟩
        · simp [hjc, ht] at hv; subst hv; exact ⟨rfl, rfl⟩
      · exact hcurT _ rfl rfl
    · exact hcurT _ rfl rfl

/-- **A reply wakes only its caller.** Replying changes the status of no task other than
the replier, except a task that was waiting for this replier's reply. -/
theorem reply_wakes_only_caller {s : KState} {t : Task} (ht : nth? s.tasks s.cur = some t)
    (slot w0 w1 w2 j : Nat) (hj : j ≠ s.cur) {u u' : Task} (hu : nth? s.tasks j = some u)
    (hu' : nth? (sysReply s t slot w0 w1 w2).state.tasks j = some u')
    (hch : u'.status ≠ u.status) : u.status = .awaiting s.cur := by
  unfold sysReply at hu'
  split at hu'
  · simp [ret, setTask, nth?_setNth, Ne.symm hj, hu] at hu'; subst hu'; exact absurd rfl hch
  · rename_i k hk
    dsimp only at hu'
    split at hu'
    · rename_i haw
      split at hu'
      · rename_i v hv
        simp only [ret, wake_tasks, wake_cur, setTask, nth?_setNth, Ne.symm hj, if_false] at hu'
        by_cases hkj : k = j
        · subst hkj
          obtain ⟨w, hw, hst⟩ := awaitsFrom_spec haw
          rw [hw] at hu; cases hu; exact hst
        · simp [hkj, hu] at hu'; subst hu'; exact absurd rfl hch
      · simp [ret, setTask, nth?_setNth, Ne.symm hj, hu] at hu'; subst hu'; exact absurd rfl hch
    · simp [ret, setTask, nth?_setNth, Ne.symm hj, hu] at hu'; subst hu'; exact absurd rfl hch

/-! ## The demo manifest: who can reach whom -/

/-- The apps that may open windows: alice's Notes (0), Terminal (5), Settings (6),
Security (7), Files (9), the programs in the open slots (10 to 15), and Apps (16). -/
def App (A : Nat) : Prop :=
  A = 0 ∨ A = 5 ∨ A = 6 ∨ A = 7 ∨ A = 9 ∨ A = 10 ∨ A = 11 ∨ A = 12 ∨ A = 13 ∨ A = 14 ∨ A = 15 ∨ A = 16

/-- The tasks that may use the network service (endpoint 2, received by the USB driver):
Terminal and Apps (which say which program may use it), and the open slots (10 to 15), which the USB driver answers only if Terminal
allowed the program running there. -/
def NetClient (A : Nat) : Prop := A = 5 ∨ A = 16 ∨ A = 10 ∨ A = 11 ∨ A = 12 ∨ A = 13 ∨ A = 14 ∨ A = 15

/-- The tasks that may use the file server: Notes (0), Terminal (5), Files (9), Apps (16), and
the open slots (10 to 15), which the file server lets reach only what they were given. -/
def FsClient (A : Nat) : Prop := A = 0 ∨ A = 5 ∨ A = 9 ∨ A = 16 ∨ A = 10 ∨ A = 11 ∨ A = 12 ∨ A = 13 ∨ A = 14 ∨ A = 15

/-- `App`, `NetClient` and `FsClient` can be decided, so checks over the manifest can use
them. -/
instance (A : Nat) : Decidable (App A) := by unfold App; infer_instance
instance (A : Nat) : Decidable (NetClient A) := by unfold NetClient; infer_instance
instance (A : Nat) : Decidable (FsClient A) := by unfold FsClient; infer_instance

/-- Who may receive on an endpoint at boot: the display server on endpoint 0, the file
server on endpoint 1, nobody else. (One pass over the manifest, not one per sender.) -/
theorem recv_owner {B e : Nat} {d : Cap} (hB : B < numTasks) (hd : d ∈ initCaps B)
    (hdo : d.obj = .endpoint e) (hr : d.rights.r = true) :
    (e = 0 ∧ B = 1) ∨ (e = 1 ∧ B = 8) ∨ (e = 2 ∧ B = 17) := by
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .endpoint e => !c.rights.r || ((e == 0 && j == 1) || ((e == 1 && j == 8) || (e == 2 && j == 17)))
    | _ => true) (by decide) hB hd
  simpa [hdo, hr] using this

/-- Who may send and grant through an endpoint at boot: the apps through endpoint 0, the
file server's clients through endpoint 1. -/
theorem grant_sender {A e : Nat} {c : Cap} (hA : A < numTasks) (hc : c ∈ initCaps A)
    (hco : c.obj = .endpoint e) (hw : c.rights.w = true) (hx : c.rights.x = true) :
    (e = 0 ∧ App A) ∨ (e = 1 ∧ FsClient A) ∨ (e = 2 ∧ NetClient A) := by
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .endpoint e => !(c.rights.w && c.rights.x) ||
        ((e == 0 && decide (App j)) || ((e == 1 && decide (FsClient j)) || (e == 2 && decide (NetClient j))))
    | _ => true) (by decide) hA hc
  simpa [hco, hw, hx] using this

/-- The only grant edges in the manifest: from each app to the display server (1), and
from the file server's clients to the file server (8). -/
theorem edge_iff {A B : Nat} :
    Edge A B ↔ (App A ∧ B = 1) ∨ (FsClient A ∧ B = 8) ∨ (NetClient A ∧ B = 17) := by
  constructor
  · rintro ⟨hA, hB, e, ⟨c, hc, hco, hw, hx⟩, ⟨d, hd, hdo, hr⟩⟩
    rcases recv_owner hB hd hdo hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases grant_sender hA hc hco hw hx with ⟨he, h⟩ | ⟨he, h⟩ | ⟨he, h⟩ <;> simp_all
  · have hd0 : epCap 0 true false false 0 ∈ initCaps 1 := by decide
    have hd1 : epCap 1 true false false 0 ∈ initCaps 8 := by decide
    have hd2 : epCap 2 true false false 0 ∈ initCaps 17 := by decide
    rintro (⟨hA, rfl⟩ | ⟨hA, rfl⟩ | ⟨hA, rfl⟩)
    · rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 1,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 5,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 6,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 7,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 9,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 10,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 11,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 12,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 13,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 14,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 15,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 0, ⟨epCap 0 false true true 16,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd0, rfl, rfl⟩⟩
    · rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 1,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 5,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 9,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 16,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 10,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 11,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 12,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 13,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 14,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 1, ⟨epCap 1 false true true 15,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd1, rfl, rfl⟩⟩
    · rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 5,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 16,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 10,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 11,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 12,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 13,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 14,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩
      · exact ⟨by decide, by decide, 2, ⟨epCap 2 false true true 15,
          by decide, rfl, rfl, rfl⟩, ⟨_, hd2, rfl, rfl⟩⟩

/-- Memory moves at most one step: from an app to the display server, or from a client to
the file server. Neither server can pass anything on. -/
theorem reach_iff {A B : Nat} (h : Reach A B) :
    A = B ∨ (App A ∧ B = 1) ∨ (FsClient A ∧ B = 8) ∨ (NetClient A ∧ B = 17) := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ he ih =>
    rcases edge_iff.1 he with ⟨hB, rfl⟩ | ⟨hB, rfl⟩ | ⟨hB, rfl⟩
    · rcases ih with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (Or.inl ⟨hB, rfl⟩)
      all_goals simp [App] at hB
    · rcases ih with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hB, rfl⟩))
      all_goals simp [FsClient] at hB
    · rcases ih with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (Or.inr (Or.inr ⟨hB, rfl⟩))
      all_goals simp [NetClient] at hB

/-- **Every task but the three servers is confined.** Whatever happens, a task other than
the display server, the file server and the USB driver (which serves the network) holds
capabilities only to its own frames, so it can never map, read or write anyone else's
memory. -/
theorem confined {s : KState} (h : Reachable s) {j : Nat} (hj : j ≠ displayTask)
    (hj8 : j ≠ fileServer) (hj17 : j ≠ usbTask) {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) :
    owner f = j := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · exact absurd h hj
  · exact absurd h hj8
  · exact absurd h hj17

/-- The file server holds only its own frames and frames its clients granted it. -/
theorem file_server_frames {s : KState} (h : Reachable s) {t : Task}
    (ht : nth? s.tasks fileServer = some t) {c : Cap} (hc : c ∈ t.caps) {f : Nat}
    (hf : Covers c f) : owner f = fileServer ∨ FsClient (owner f) := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl h
  · simp [fileServer] at h
  · exact Or.inr h
  · simp [fileServer] at h

/-- The USB driver, which serves the network, holds only its own frames and frames Terminal
lent it for a request. -/
theorem net_server_frames {s : KState} (h : Reachable s) {t : Task}
    (ht : nth? s.tasks usbTask = some t) {c : Cap} (hc : c ∈ t.caps) {f : Nat}
    (hf : Covers c f) : owner f = usbTask ∨ NetClient (owner f) := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
  · exact Or.inl h
  · simp [usbTask] at h
  · simp [usbTask] at h
  · exact Or.inr h

/-- **mallory is confined.** Whatever happens, task 2 holds capabilities only to its own
frames (512 to 767), so it can never map, read or write anyone else's memory. -/
theorem mallory_confined {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 2 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 2 := by
  exact confined h (by decide) (by decide) (by decide) ht hc hf

/-- carol (task 3) holds capabilities only to her own frames (768 to 1023). -/
theorem carol_confined {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 3 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 3 := by
  exact confined h (by decide) (by decide) (by decide) ht hc hf

/-- alice (task 0) is never given anyone's memory: she only ever holds her own frames. -/
theorem alice_confined {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 0 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 0 := by
  exact confined h (by decide) (by decide) (by decide) ht hc hf

/-- The display server (task 1) holds only its own frames, the framebuffer, and frames the
apps granted it. -/
theorem server_frames {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 1 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 1 ∨ App (owner f) := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · simp at h
  · simp at h

/-! ## Only verified code runs -/

theorem isReady_task {ts : List Task} {j : Nat} (h : isReady ts j = true) :
    ∃ t, nth? ts j = some t ∧ t.status = .ready := by
  unfold isReady at h
  split at h
  · rename_i t ht
    split at h
    · rename_i hst; exact ⟨t, ht, hst⟩
    · simp at h
  · simp at h

/-- **Only verified code runs.** In every reachable state, a task that can run was loaded
with exactly the code and assets the boot manifest names: the machine layer measured them,
and the measurement matched. Whatever the machine layer measures, a task whose measurement
differs never becomes ready, and nothing ever makes it ready later. -/
theorem only_verified_runs {s : KState} (h : Reachable s) {j : Nat} (hr : isReady s.tasks j = true)
    (ho : openSlot j = false) :
    ∃ t, nth? s.tasks j = some t ∧ t.hash = expectedHash j := by
  obtain ⟨t, ht, hst⟩ := isReady_task hr
  exact ⟨t, ht, ((reachable_inv h).tasks j t ht).measured (by rw [hst]; trivial) ho⟩

/-- A measurement that differs from the manifest refuses the task for good. -/
theorem verify_refuses_mismatch (s : KState) (i : Nat) (hm : List Nat) (hne : hm ≠ expectedHash i)
    (ho : openSlot i = false) {t : Task} (ht : nth? s.tasks i = some t) (hu : t.status = .unverified) :
    ∃ t', nth? (verify s i hm).tasks i = some t' ∧ t'.status = .dead := by
  have hneq : eqList hm (expectedHash i) = false := by
    cases h : eqList hm (expectedHash i)
    · rfl
    · exact absurd (eqList_spec h) hne
  refine ⟨{ t with status := .dead, hash := hm }, ?_, rfl⟩
  simp [verify, ht, hu, hneq, ho, setTask, nth?_setNth]

/-! ## Dropping a capability -/

/-- **Dropping only takes away.** After `drop`, every task holds a subset of the
capabilities and mappings it held before; the caller loses the capability and every page
it could see only through it. -/
theorem drop_only_shrinks {s : KState} {t : Task} (ht : nth? s.tasks s.cur = some t) (ci j : Nat)
    {u u' : Task} (hu : nth? s.tasks j = some u) (hu' : nth? (sysDrop s t ci).state.tasks j = some u') :
    (∀ c ∈ u'.caps, c ∈ u.caps) ∧ (∀ m ∈ u'.maps, m ∈ u.maps) := by
  unfold sysDrop at hu'
  split at hu'
  · simp only [ret, setTask, nth?_setNth] at hu'
    by_cases hj : s.cur = j
    · subst hj; rw [ht] at hu; cases hu; simp [ht] at hu'; subst hu'; exact ⟨fun _ h => h, fun _ h => h⟩
    · simp [hj, hu] at hu'; subst hu'; exact ⟨fun _ h => h, fun _ h => h⟩
  · simp only [setTask, nth?_setNth] at hu'
    by_cases hj : s.cur = j
    · subst hj; rw [ht] at hu; cases hu; simp [ht] at hu'; subst hu'
      exact ⟨fun _ h => mem_removeNth h, fun _ h => (mem_keepBacked h).1⟩
    · simp [hj, hu] at hu'; subst hu'; exact ⟨fun _ h => h, fun _ h => h⟩

/-! ## Starting programs -/

@[simp] theorem ret_load (s : KState) (t : Task) (r : List Nat) : (ret s t r).load = 0 := rfl

theorem forgetCaller_ne {k : Nat} (hk : k ≠ noTask) : ∀ {cs : List Nat} {x : Nat},
    x ∈ forgetCaller k cs → x ≠ k
  | [], x, h => by simp [forgetCaller] at h
  | c :: cs, x, h => by
    simp only [forgetCaller, List.mem_cons] at h
    rcases h with h | h
    · subst h; split
      · exact Ne.symm hk
      · rename_i hc; simpa using hc
    · exact forgetCaller_ne hk h

theorem scrub_grant {k : Nat} {st : Status} {e : Nat} {m : Msg} (h : scrubStatus k st = .sending e m)
    {g : Cap} (hg : m.grant = some g) :
    ∃ m0, st = .sending e m0 ∧ m0.grant = some g ∧ capInSlot k g = false := by
  cases st <;> simp only [scrubStatus, reduceCtorEq] at h
  rename_i e0 m0
  simp only [Status.sending.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨m0, rfl, ?_⟩
  revert hg
  cases hm : m0.grant with
  | none => simp
  | some c =>
    by_cases hc : capInSlot k c = true
    · simp [hc]
    · have hcf : capInSlot k c = false := by simpa using hc
      intro h
      simp [hcf] at h
      subst h; exact ⟨rfl, hcf⟩

/-- After a revocation, a task's capabilities and mappings reach none of the slot's frames,
a message it is waiting to send grants none of them, and it owes the slot no reply. -/
theorem revoked_clean {fb : Bool} {j k : Nat} {v : Task} (hv : TaskOK fb j v) (hk : k ≠ noTask) :
    (∀ c ∈ (revokeTask k v).caps, ∀ f, Covers c f → inSlot k f = false) ∧
      (∀ m ∈ (revokeTask k v).maps, inSlot k m.frame = false) ∧
      (∀ e msg g, (revokeTask k v).status = .sending e msg → msg.grant = some g →
        ∀ f, Covers g f → inSlot k f = false) ∧
      ∀ x ∈ (revokeTask k v).callers, x ≠ k := by
  refine ⟨fun c hc f hf => ?_, fun m hm => (mem_dropMaps hm).2, fun e msg g hs hg f hf => ?_,
    fun x hx => forgetCaller_ne hk hx⟩
  · obtain ⟨hc, hk⟩ := mem_dropCaps hc
    exact kept_covers (hv.caps c hc).run hk hf
  · obtain ⟨m0, hst, hg0, hkg⟩ := scrub_grant hs hg
    have hok := hv.status
    rw [hst] at hok
    exact kept_covers ((hok.2 g hg0).1.run) hkg hf

/-- **Starting a program takes back its memory.** When `start` asks the machine layer to
load slot `k`, the slot holds exactly the manifest's fresh task, not yet verified, and no
other task holds a capability to, or a mapping of, any of slot `k`'s frames, or is waiting
to send a message that would grant one. Whatever the slot's previous run shared, nobody
keeps it; and no task holds a reply slot for it, so no reply meant for the old run can
reach the new one. -/
theorem start_revokes {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks s.cur = some t)
    {ci src len k : Nat} (hl : (sysStart s t ci src len).load = k + 1) :
    nth? (sysStart s t ci src len).state.tasks k = some (mkTask k) ∧
    ∀ j u, j ≠ k → nth? (sysStart s t ci src len).state.tasks j = some u →
      (∀ c ∈ u.caps, ∀ f, Covers c f → inSlot k f = false) ∧
        (∀ m ∈ u.maps, inSlot k m.frame = false) ∧
        (∀ e msg g, u.status = .sending e msg → msg.grant = some g →
          ∀ f, Covers g f → inSlot k f = false) ∧
        ∀ x ∈ u.callers, x ≠ k := by
  have hs := reachable_inv h
  unfold sysStart at hl ⊢
  split at hl <;> (try simp at hl)
  rename_i c hc
  split at hl <;> (try simp at hl)
  rename_i k' _
  split at hl <;> (try simp at hl)
  rename_i u0 hu0
  split at hl <;> (try simp at hl)
  rename_i hok
  have hck : s.cur ≠ k' := by
    intro e; subst e; simp at hok
  have hkn : k' ≠ noTask := by
    have := hs.lt hu0; simp [numTasks, noTask] at this ⊢; omega
  dsimp only at hl ⊢
  split at hl <;> (try simp at hl)
  rename_i t1 ht1
  subst hl
  split
  rotate_left
  · exfalso; simp_all
  simp only [setTask, nth?_setNth, nth?_revokeAll] at ht1 ⊢
  refine ⟨by simp [hck, hu0], ?_⟩
  intro j u hjk hu
  by_cases hcj : s.cur = j
  · subst hcj
    simp [Ne.symm hjk] at hu
    obtain ⟨-, rfl⟩ := hu
    simp [Ne.symm hck, ht] at ht1
    subst ht1
    exact revoked_clean (hs.tasks _ _ ht) hkn
  · simp [hcj, Ne.symm hjk] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact revoked_clean (hs.tasks _ _ hv) hkn

/-- Launch capabilities never move: a task holds one only if it held it at boot. -/
theorem launch_fixed {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {k : Nat} (hk : c.obj = .launch k) :
    ∃ c0 ∈ initCaps j, c0.obj = .launch k :=
  ((reachable_inv h).tasks j t ht).caps c hc |>.launch k hk

/-- **Who starts programs.** Only the display server starts the manifest's apps (Notes,
Terminal, Settings, Security, Files, Apps), and only Terminal and Apps start the open
slots. No task can
start (or restart) the display server, the input driver, the file server, mallory or
carol. -/
theorem only_display_launches {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {k : Nat} (hk : c.obj = .launch k) :
    (j = displayTask ∧ App k ∧ openSlot k = false) ∨ ((j = 5 ∨ j = 16) ∧ openSlot k = true) := by
  obtain ⟨c0, hc0, ho⟩ := launch_fixed h ht hc hk
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .launch k => (j == displayTask && (decide (App k) && !openSlot k)) || ((j == 5 || j == 16) && openSlot k)
    | _ => true) (by decide) ((reachable_inv h).lt ht) hc0
  simpa [ho] using this

/-! ## Interrupts and devices -/

/-- Interrupt capabilities never move: a task holds one only if it held it at boot. -/
theorem irqs_fixed {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {n : Nat} (hn : c.obj = .irq n) :
    ∃ c0 ∈ initCaps j, c0.obj = .irq n :=
  ((reachable_inv h).tasks j t ht).caps c hc |>.irq n hn

/-- **An interrupt wakes only its holder.** If interrupt line `n` firing changes a task's
status, that task was given the capability to line `n` at boot. -/
theorem irq_wakes_holder {s : KState} (h : Reachable s) (n j : Nat) {u u' : Task}
    (hu : nth? s.tasks j = some u) (hu' : nth? (irqFired s n).tasks j = some u')
    (hch : u'.status ≠ u.status) : ∃ c0 ∈ initCaps j, c0.obj = .irq n := by
  unfold irqFired at hu'
  split at hu'
  · rename_i k hk
    split at hu'
    · rename_i v hv
      simp only [preempt_tasks, setTask, nth?_setNth] at hu'
      by_cases hkj : k = j
      · subst hkj
        obtain ⟨-, w, hw, hst⟩ := findIrqWaiter_spec hk
        simp only [Nat.sub_zero] at hw
        rw [hw] at hu; cases hu
        have := ((reachable_inv h).tasks k _ hw).status
        rw [hst] at this
        exact this
      · simp [hkj, hu] at hu'; subst hu'; exact absurd rfl hch
    · rw [hu] at hu'; cases hu'; exact absurd rfl hch
  · split at hu'
    · rw [hu] at hu'; cases hu'; exact absurd rfl hch
    · simp [hu] at hu'; subst hu'; exact absurd rfl hch

/-- **The keyboard's interrupt belongs to the input driver.** No other task can ever hold a
capability to the UART's interrupt line, so no other task can wait for it or acknowledge
it. -/
theorem uart_irq_only_input {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) (hn : c.obj = .irq uartIrq) :
    j = inputTask := by
  obtain ⟨c0, hc0, ho⟩ := irqs_fixed h ht hc hn
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .irq n => n != uartIrq || j == inputTask
    | _ => true) (by decide) ((reachable_inv h).lt ht) hc0
  simpa [ho] using this

/-- **The UART belongs to the input driver.** No other task can ever hold a capability to
the UART's registers. -/
theorem uart_confined {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) (hf : Covers c devBase) :
    j = inputTask := by
  have hr := (frame_flow h ht hc hf).1
  have : owner devBase = inputTask := by decide
  rw [this] at hr
  rcases reach_iff hr with h1 | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
  · exact h1.symm
  · simp [App, inputTask] at h0
  · simp [FsClient, inputTask] at h0
  · simp [NetClient, inputTask] at h0

/-! ## `write` reads only what the task may read -/

theorem readableAt_spec : ∀ {ms : List Mapping} {p : Nat},
    readableAt ms p = true → ∃ m ∈ ms, m.vpn = p ∧ m.rights.r = true
  | [], p, h => by simp [readableAt] at h
  | m :: ms, p, h => by
    simp only [readableAt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨m, List.mem_cons_self .., h.1, h.2⟩
    · obtain ⟨m', hm', h'⟩ := readableAt_spec h
      exact ⟨m', List.mem_cons_of_mem _ hm', h'⟩

theorem allReadable_spec : ∀ {ms : List Mapping} {first count p : Nat},
    allReadable ms first count = true → first ≤ p → p < first + count → readableAt ms p = true
  | ms, first, 0, p, _, h1, h2 => by omega
  | ms, first, k + 1, p, h, h1, h2 => by
    simp only [allReadable, Bool.and_eq_true] at h
    by_cases hp : p = first
    · subst hp; exact h.1
    · exact allReadable_spec h.2 (by omega) (by omega)

/-! ## What each system call asks of the machine layer

Most system calls ask the machine layer for nothing beyond loading result registers, and
none but `setwall` touches either clock. These facts, proved once per call, are what the
theorems below about single fields of a reply (`outLen_pos`, `io_pos`, `power_pos`,
`loadLen_pos`, `board_pos`, `usb_pos`, `syscall_now`, `syscall_wall`) rest on. -/

/-- The reply asks the machine layer for nothing (no printing, block I/O, program load,
power change, board request or USB access) and leaves both clocks as they were in `s`. -/
abbrev Calm (s : KState) (r : Reply) : Prop :=
  r.outLen = 0 ∧ r.io = 0 ∧ r.loadLen = 0 ∧ r.power = 0 ∧ r.board = 0 ∧ r.usbOp = 0 ∧
    r.state.now = s.now ∧ r.state.wall = s.wall

/-- The scheduler moves neither clock. -/
theorem schedule_keeps_clocks (s : KState) : (schedule s).now = s.now ∧ (schedule s).wall = s.wall := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]; exact ⟨rfl, rfl⟩

/-- Stopping the current task moves neither clock. -/
theorem killCurrent_keeps_clocks (s : KState) :
    (killCurrent s).now = s.now ∧ (killCurrent s).wall = s.wall := by
  unfold killCurrent; split <;> exact schedule_keeps_clocks _

/-- Closes `Calm` for a reply whose state is the old one, changed only in its tasks, its
pending interrupts or its USB registers, possibly then rescheduled. -/
local macro "calm_leaf" : tactic => `(tactic| first
  | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, (schedule_keeps_clocks _).1, (schedule_keeps_clocks _).2⟩
  | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [serve, setTask], by simp [serve, setTask]⟩)

@[simp] theorem ret_calm (s : KState) (t : Task) (r : List Nat) : Calm s (ret s t r) := by calm_leaf

@[simp] theorem sysMap_calm (s : KState) (t : Task) (ci vpn : Nat) : Calm s (sysMap s t ci vpn) := by
  unfold sysMap; repeat' split
  all_goals calm_leaf

@[simp] theorem sysUnmap_calm (s : KState) (t : Task) (vpn count : Nat) :
    Calm s (sysUnmap s t vpn count) := by
  unfold sysUnmap; calm_leaf

@[simp] theorem sysDerive_calm (s : KState) (t : Task) (ci bits offset count : Nat) :
    Calm s (sysDerive s t ci bits offset count) := by
  unfold sysDerive; repeat' split
  all_goals calm_leaf

@[simp] theorem sysCapInfo_calm (s : KState) (t : Task) (ci : Nat) : Calm s (sysCapInfo s t ci) := by
  unfold sysCapInfo; repeat' split
  all_goals calm_leaf

@[simp] theorem sysSend_calm (s : KState) (t : Task) (ci w0 w1 w2 gi : Nat) (call : Bool) :
    Calm s (sysSend s t ci w0 w1 w2 gi call) := by
  unfold sysSend; repeat' (first | split | dsimp only)
  all_goals calm_leaf

@[simp] theorem sysRecv_calm (s : KState) (t : Task) (ci : Nat) (block : Bool) (deadline : Nat) :
    Calm s (sysRecv s t ci block deadline) := by
  unfold sysRecv; repeat' (first | split | dsimp only)
  all_goals calm_leaf

@[simp] theorem sysReply_calm (s : KState) (t : Task) (slot w0 w1 w2 : Nat) :
    Calm s (sysReply s t slot w0 w1 w2) := by
  unfold sysReply; repeat' (first | split | dsimp only)
  all_goals calm_leaf

@[simp] theorem sysIrqWait_calm (s : KState) (t : Task) (ci : Nat) : Calm s (sysIrqWait s t ci) := by
  unfold sysIrqWait; repeat' split
  all_goals calm_leaf

@[simp] theorem sysIrqAck_calm (s : KState) (t : Task) (ci : Nat) : Calm s (sysIrqAck s t ci) := by
  unfold sysIrqAck; repeat' split
  all_goals calm_leaf

@[simp] theorem sysBootInfo_calm (s : KState) (t : Task) (i : Nat) : Calm s (sysBootInfo s t i) := by
  unfold sysBootInfo; split
  all_goals calm_leaf

@[simp] theorem sysDrop_calm (s : KState) (t : Task) (ci : Nat) : Calm s (sysDrop s t ci) := by
  unfold sysDrop; split
  all_goals calm_leaf

@[simp] theorem sysSleep_calm (s : KState) (t : Task) (ms : Nat) : Calm s (sysSleep s t ms) := by
  unfold sysSleep; dsimp only; split
  all_goals calm_leaf

@[simp] theorem sysTime_calm (s : KState) (t : Task) : Calm s (sysTime s t) := by
  unfold sysTime; calm_leaf

@[simp] theorem sysStop_calm (s : KState) (t : Task) (ci : Nat) : Calm s (sysStop s t ci) := by
  unfold sysStop; repeat' split
  all_goals calm_leaf

/-- `write` asks only to print. -/
@[simp] theorem sysWrite_asks (s : KState) (t : Task) (va n : Nat) :
    (sysWrite s t va n).io = 0 ∧ (sysWrite s t va n).loadLen = 0 ∧ (sysWrite s t va n).power = 0 ∧
      (sysWrite s t va n).board = 0 ∧ (sysWrite s t va n).usbOp = 0 ∧
      (sysWrite s t va n).state.now = s.now ∧ (sysWrite s t va n).state.wall = s.wall := by
  generalize hr : sysWrite s t va n = r
  unfold sysWrite at hr; repeat' split at hr
  all_goals (subst hr; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `blockread` and `blockwrite` ask only for block I/O. -/
@[simp] theorem sysBlock_asks (s : KState) (t : Task) (ci idx va k : Nat) (w : Bool) :
    (sysBlock s t ci idx va k w).outLen = 0 ∧ (sysBlock s t ci idx va k w).loadLen = 0 ∧
      (sysBlock s t ci idx va k w).power = 0 ∧ (sysBlock s t ci idx va k w).board = 0 ∧
      (sysBlock s t ci idx va k w).usbOp = 0 ∧ (sysBlock s t ci idx va k w).state.now = s.now ∧
      (sysBlock s t ci idx va k w).state.wall = s.wall := by
  generalize hr : sysBlock s t ci idx va k w = r
  unfold sysBlock at hr; repeat' split at hr
  all_goals (subst hr; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `start` and `exec` ask only to load a program. -/
@[simp] theorem sysStart_asks (s : KState) (t : Task) (ci src len : Nat) :
    (sysStart s t ci src len).outLen = 0 ∧ (sysStart s t ci src len).io = 0 ∧
      (sysStart s t ci src len).power = 0 ∧ (sysStart s t ci src len).board = 0 ∧
      (sysStart s t ci src len).usbOp = 0 ∧ (sysStart s t ci src len).state.now = s.now ∧
      (sysStart s t ci src len).state.wall = s.wall := by
  generalize hr : sysStart s t ci src len = r
  unfold sysStart at hr; repeat' (first | split at hr | dsimp only at hr)
  all_goals (subst hr; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `power` asks only to switch off or restart. -/
@[simp] theorem sysPower_asks (s : KState) (t : Task) (ci a : Nat) :
    (sysPower s t ci a).outLen = 0 ∧ (sysPower s t ci a).io = 0 ∧ (sysPower s t ci a).loadLen = 0 ∧
      (sysPower s t ci a).board = 0 ∧ (sysPower s t ci a).usbOp = 0 ∧
      (sysPower s t ci a).state.now = s.now ∧ (sysPower s t ci a).state.wall = s.wall := by
  generalize hr : sysPower s t ci a = r
  unfold sysPower at hr; repeat' split at hr
  all_goals (subst hr; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `board` asks only for a board request. -/
@[simp] theorem sysBoard_asks (s : KState) (t : Task) (ci w v : Nat) :
    (sysBoard s t ci w v).outLen = 0 ∧ (sysBoard s t ci w v).io = 0 ∧
      (sysBoard s t ci w v).loadLen = 0 ∧ (sysBoard s t ci w v).power = 0 ∧
      (sysBoard s t ci w v).usbOp = 0 ∧ (sysBoard s t ci w v).state.now = s.now ∧
      (sysBoard s t ci w v).state.wall = s.wall := by
  generalize hr : sysBoard s t ci w v = r
  unfold sysBoard at hr; repeat' (first | split at hr | dsimp only at hr)
  all_goals (subst hr; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `usb` asks only for the USB controller. -/
@[simp] theorem sysUsb_asks (s : KState) (t : Task) (ci op reg v : Nat) :
    (sysUsb s t ci op reg v).outLen = 0 ∧ (sysUsb s t ci op reg v).io = 0 ∧
      (sysUsb s t ci op reg v).loadLen = 0 ∧ (sysUsb s t ci op reg v).power = 0 ∧
      (sysUsb s t ci op reg v).board = 0 ∧ (sysUsb s t ci op reg v).state.now = s.now ∧
      (sysUsb s t ci op reg v).state.wall = s.wall := by
  generalize hr : sysUsb s t ci op reg v = r
  unfold sysUsb usbReply at hr
  split at hr
  · subst hr; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split at hr <;> subst hr
    -- the checks on the USB capability's arguments are a tree of `if`s, far cheaper to push
    -- each field through than to split
    all_goals first
      | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | simp only [apply_ite Reply.outLen, apply_ite Reply.io, apply_ite Reply.loadLen,
          apply_ite Reply.power, apply_ite Reply.board, apply_ite Reply.state, apply_ite KState.now,
          apply_ite KState.wall, ret_calm, setTask, ite_self, and_self]

/-- `setwall` asks the machine layer for nothing, and changes only the time of day. -/
@[simp] theorem sysSetWall_asks (s : KState) (t : Task) (ci secs : Nat) :
    (sysSetWall s t ci secs).outLen = 0 ∧ (sysSetWall s t ci secs).io = 0 ∧
      (sysSetWall s t ci secs).loadLen = 0 ∧ (sysSetWall s t ci secs).power = 0 ∧
      (sysSetWall s t ci secs).board = 0 ∧ (sysSetWall s t ci secs).usbOp = 0 ∧
      (sysSetWall s t ci secs).state.now = s.now := by
  generalize hr : sysSetWall s t ci secs = r
  unfold sysSetWall at hr; repeat' split at hr
  all_goals (subst hr; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- A running task's system call asks the machine layer for nothing and keeps both clocks,
or it is one of the calls that ask for something: `write`, `blockread` or `blockwrite`,
`start` or `exec`, `power`, `board`, `usb`, or `setwall` (call 27). -/
theorem runCall_cases (s : KState) (t : Task) (num a0 a1 a2 a3 a4 : Nat) :
    Calm s (runCall s t num a0 a1 a2 a3 a4) ∨
      runCall s t num a0 a1 a2 a3 a4 = sysWrite s t a0 a1 ∨
      (∃ w, runCall s t num a0 a1 a2 a3 a4 = sysBlock s t a0 a1 a2 a3 w) ∨
      (∃ ci src len, runCall s t num a0 a1 a2 a3 a4 = sysStart s t ci src len) ∨
      (∃ ci a, runCall s t num a0 a1 a2 a3 a4 = sysPower s t ci a) ∨
      (∃ ci w v, runCall s t num a0 a1 a2 a3 a4 = sysBoard s t ci w v) ∨
      (∃ ci op reg v, runCall s t num a0 a1 a2 a3 a4 = sysUsb s t ci op reg v) ∨
      (num = 27 ∧ ∃ ci secs, runCall s t num a0 a1 a2 a3 a4 = sysSetWall s t ci secs) := by
  generalize hr : runCall s t num a0 a1 a2 a3 a4 = r
  unfold runCall at hr
  split at hr <;> subst hr
  all_goals first
    | (left; simp [Calm, setTask, schedule_keeps_clocks, killCurrent_keeps_clocks]; done)
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, rfl⟩))))))

@[simp] theorem ret_outLen (s : KState) (t : Task) (r : List Nat) : (ret s t r).outLen = 0 := rfl

/-- The only system call that asks the machine layer to print is `write`. -/
theorem outLen_pos {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : 0 < (syscall s num a0 a1 a2 a3 a4).outLen) :
    ∃ t, nth? s.tasks s.cur = some t ∧ syscall s num a0 a1 a2 a3 a4 = sysWrite s t a0 a1 := by
  unfold syscall at *
  split at *
  · simp at h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    split at *
    rotate_left
    · simp at h
    rcases runCall_cases s t num a0 a1 a2 a3 a4 with
      hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨-, _, _, hr⟩ <;>
      first | exact hr | simp [hr] at h

/-- When a system call asks the machine layer to print user memory, every byte of it is in
the user window, in a page the calling task has mapped with read rights. -/
theorem write_reads_only_readable (s : KState) (num a0 a1 a2 a3 a4 : Nat)
    (hout : 0 < (syscall s num a0 a1 a2 a3 a4).outLen) :
    ∃ t, nth? s.tasks s.cur = some t ∧
      ∀ a, (syscall s num a0 a1 a2 a3 a4).outVa ≤ a →
        a < (syscall s num a0 a1 a2 a3 a4).outVa + (syscall s num a0 a1 a2 a3 a4).outLen →
        userBase ≤ a ∧ ∃ m ∈ t.maps, m.vpn = (a - userBase) / pageSize ∧ m.rights.r = true := by
  obtain ⟨t, ht, heq⟩ := outLen_pos hout
  refine ⟨t, ht, ?_⟩
  rw [heq]
  unfold sysWrite
  split
  · intro a h1 h2; simp at h2; omega
  · split
    · rename_i hc
      obtain ⟨_, hva, hall⟩ := hc
      intro a ha1 ha2
      dsimp only at ha1 ha2
      refine ⟨by omega, readableAt_spec (allReadable_spec hall ?_ ?_)⟩
      · exact Nat.div_le_div_right (by omega)
      · have : (a - userBase) / pageSize ≤ (a0 + a1 - 1 - userBase) / pageSize :=
          Nat.div_le_div_right (by omega)
        omega
    · intro a h1 h2; simp at h2; omega

/-! ## The SD card -/

/-- Block capabilities never move: a task holds one only if it held it at boot, with at
least those rights. -/
theorem blocks_fixed {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {b n : Nat} (hb : c.obj = .blocks b n) :
    ∃ c0 ∈ initCaps j, c0.obj = .blocks b n ∧ RLe c.rights c0.rights :=
  ((reachable_inv h).tasks j t ht).caps c hc |>.blocks b n hb

/-- **The disk belongs to the file server.** No other task can ever hold a capability to
any block of the SD card, and the file server holds only the manifest's blocks. -/
theorem disk_only_file_server {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {b n : Nat} (hb : c.obj = .blocks b n) :
    j = fileServer ∧ b = 0 ∧ n = diskBlocks := by
  obtain ⟨c0, hc0, ho, -⟩ := blocks_fixed h ht hc hb
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .blocks b n => j == fileServer && (b == 0 && n == diskBlocks)
    | _ => true) (by decide) ((reachable_inv h).lt ht) hc0
  simpa [ho] using this

theorem writableAt_spec : ∀ {ms : List Mapping} {p : Nat},
    writableAt ms p = true → ∃ m ∈ ms, m.vpn = p ∧ m.rights.w = true
  | [], p, h => by simp [writableAt] at h
  | m :: ms, p, h => by
    simp only [writableAt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨m, List.mem_cons_self .., h.1, h.2⟩
    · obtain ⟨m', hm', h'⟩ := writableAt_spec h
      exact ⟨m', List.mem_cons_of_mem _ hm', h'⟩

@[simp] theorem ret_io (s : KState) (t : Task) (r : List Nat) : (ret s t r).io = 0 := rfl

/-- The only system calls that ask the machine layer for block I/O are `blockread` and
`blockwrite`. -/
theorem io_pos {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).io ≠ 0) :
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ w, syscall s num a0 a1 a2 a3 a4 = sysBlock s t a0 a1 a2 a3 w := by
  unfold syscall at *
  split at *
  · simp at h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    split at *
    rotate_left
    · simp at h
    rcases runCall_cases s t num a0 a1 a2 a3 a4 with
      hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨-, _, _, hr⟩ <;>
      first | exact ⟨_, hr⟩ | simp [hr] at h

/-- What a `blockread` or `blockwrite` that asks for I/O checked. -/
theorem sysBlock_io {s : KState} {t : Task} {ci idx va k : Nat} {w : Bool}
    (h : (sysBlock s t ci idx va k w).io ≠ 0) :
    ∃ c b n, nth? t.caps ci = some c ∧ c.obj = .blocks b n ∧ runFits (runLen k) idx n = true ∧
      capRightFor w c.rights = true ∧ runPageOk t.maps va (runLen k) w = true ∧
      (sysBlock s t ci idx va k w).io = ioRun w (runLen k) ∧
      (sysBlock s t ci idx va k w).ioBlock = b + idx ∧ (sysBlock s t ci idx va k w).outVa = va := by
  unfold sysBlock at *
  split at h
  · simp at h
  · rename_i c hc
    split at h
    · rename_i b n hb
      split at h
      · rename_i hcond
        have hc' := hcond
        simp only [Bool.and_eq_true] at hc'
        refine ⟨c, b, n, hc, hb, hc'.1.1, hc'.1.2, hc'.2, ?_⟩
        simp only [if_pos hcond, and_self]
      · simp at h
    · simp at h

theorem runLen_pos (k : Nat) : 1 ≤ runLen k := by
  unfold runLen; split <;> omega

theorem ioCount_ioRun (w : Bool) {k : Nat} (hk : 1 ≤ k) : ioCount (ioRun w k) = k := by
  cases w <;> simp only [ioCount, ioRun, ioCode] <;> omega

theorem ioWrites_ioRun (w : Bool) (k : Nat) : ioWrites (ioRun w k) = w := by
  cases w <;> simp only [ioWrites, ioRun, ioCode, beq_iff_eq, beq_eq_false_iff_ne] <;> omega

theorem allRightFor_spec {w : Bool} : ∀ {ms : List Mapping} {first count p : Nat},
    allRightFor w ms first count = true → first ≤ p → p < first + count → pageRightFor w ms p = true
  | ms, first, 0, p, _, h1, h2 => by omega
  | ms, first, k + 1, p, h, h1, h2 => by
    simp only [allRightFor, Bool.and_eq_true] at h
    by_cases hp : p = first
    · subst hp; exact h.1
    · exact allRightFor_spec h.2 (by omega) (by omega)

/-- **A run of block I/O touches only what the caller may touch.** When a system call asks
the machine layer for block I/O, it asks for a run of 1 to `maxRun` blocks (`ioCount`),
read or written (`ioWrites`). Every block of the run is inside one block capability the
caller holds, with the read right (to read the disk) or the write right (to write it); and
every byte of memory the run moves, 512 a block from `outVa` on, is in the user window, in a
page the caller has mapped writable (the disk writes into it) or readable (the disk reads
from it). -/
theorem block_run_confined (s : KState) (num a0 a1 a2 a3 a4 : Nat)
    (hio : (syscall s num a0 a1 a2 a3 a4).io ≠ 0) :
    1 ≤ ioCount (syscall s num a0 a1 a2 a3 a4).io ∧ ioCount (syscall s num a0 a1 a2 a3 a4).io ≤ maxRun ∧
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ c ∈ t.caps, ∃ b n, c.obj = .blocks b n ∧
      b ≤ (syscall s num a0 a1 a2 a3 a4).ioBlock ∧
      (syscall s num a0 a1 a2 a3 a4).ioBlock + ioCount (syscall s num a0 a1 a2 a3 a4).io ≤ b + n ∧
      (ioWrites (syscall s num a0 a1 a2 a3 a4).io = false → c.rights.r = true) ∧
      (ioWrites (syscall s num a0 a1 a2 a3 a4).io = true → c.rights.w = true) ∧
      ∀ a, (syscall s num a0 a1 a2 a3 a4).outVa ≤ a →
        a < (syscall s num a0 a1 a2 a3 a4).outVa + 512 * ioCount (syscall s num a0 a1 a2 a3 a4).io →
        userBase ≤ a ∧ ∃ m ∈ t.maps, m.vpn = (a - userBase) / pageSize ∧
          (ioWrites (syscall s num a0 a1 a2 a3 a4).io = false → m.rights.w = true) ∧
          (ioWrites (syscall s num a0 a1 a2 a3 a4).io = true → m.rights.r = true) := by
  obtain ⟨t, ht, w, heq⟩ := io_pos hio
  rw [heq] at hio ⊢
  obtain ⟨c, b, n, hc, hb, hfit, hr, hpage, hop, hblk, hva⟩ := sysBlock_io hio
  have hk := runLen_pos a3
  rw [hop, hblk, hva, ioCount_ioRun w hk, ioWrites_ioRun]
  simp only [runFits, Bool.and_eq_true, Nat.ble_eq] at hfit
  simp only [runPageOk, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hpage
  obtain ⟨⟨hal, hub⟩, hpg⟩ := hpage
  refine ⟨hk, hfit.1, t, ht, c, nth?_mem hc, b, n, hb, by omega, by omega, ?_, ?_, ?_⟩
  · intro h; subst h; simpa [capRightFor] using hr
  · intro h; subst h; simpa [capRightFor] using hr
  · intro a h1 h2
    have hlo : (a2 - userBase) / pageSize ≤ (a - userBase) / pageSize := Nat.div_le_div_right (by omega)
    have hhi : (a - userBase) / pageSize ≤ (a2 + 512 * runLen a3 - 1 - userBase) / pageSize :=
      Nat.div_le_div_right (by omega)
    have hp := allRightFor_spec hpg hlo (by omega)
    refine ⟨by omega, ?_⟩
    cases w
    · obtain ⟨m, hm, hv, hw⟩ := writableAt_spec (by simpa [pageRightFor] using hp)
      exact ⟨m, hm, hv, fun _ => hw, fun h => by simp at h⟩
    · obtain ⟨m, hm, hv, hr'⟩ := readableAt_spec (by simpa [pageRightFor] using hp)
      exact ⟨m, hm, hv, fun h => by simp at h, fun _ => hr'⟩

/-- **Block I/O touches only what the caller may touch.** When a system call asks the
machine layer to read or write a block, the block is inside a block capability the caller
holds, with the read right (for `blockread`) or the write right (for `blockwrite`); and all
512 bytes of memory are in the user window, in one page the caller has mapped writable
(the disk writes into it) or readable (the disk reads from it). The first block of a run,
from `block_run_confined`. -/
theorem block_io_confined (s : KState) (num a0 a1 a2 a3 a4 : Nat)
    (hio : (syscall s num a0 a1 a2 a3 a4).io ≠ 0) :
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ c ∈ t.caps, ∃ b n, c.obj = .blocks b n ∧
      b ≤ (syscall s num a0 a1 a2 a3 a4).ioBlock ∧ (syscall s num a0 a1 a2 a3 a4).ioBlock < b + n ∧
      ((syscall s num a0 a1 a2 a3 a4).io = 1 → c.rights.r = true) ∧
      ((syscall s num a0 a1 a2 a3 a4).io = 2 → c.rights.w = true) ∧
      ∀ a, (syscall s num a0 a1 a2 a3 a4).outVa ≤ a → a < (syscall s num a0 a1 a2 a3 a4).outVa + 512 →
        userBase ≤ a ∧ ∃ m ∈ t.maps, m.vpn = (a - userBase) / pageSize ∧
          ((syscall s num a0 a1 a2 a3 a4).io = 1 → m.rights.w = true) ∧
          ((syscall s num a0 a1 a2 a3 a4).io = 2 → m.rights.r = true) := by
  obtain ⟨h1, -, t, ht, c, hc, b, n, hb, hlo, hhi, hr, hw, hmem⟩ := block_run_confined s num a0 a1 a2 a3 a4 hio
  refine ⟨t, ht, c, hc, b, n, hb, hlo, by omega, fun h => hr (by simp [h, ioWrites]),
    fun h => hw (by simp [h, ioWrites]), ?_⟩
  intro a ha1 ha2
  obtain ⟨hu, m, hm, hv, hmw, hmr⟩ := hmem a ha1 (by omega)
  exact ⟨hu, m, hm, hv, fun h => hmw (by simp [h, ioWrites]), fun h => hmr (by simp [h, ioWrites])⟩

/-! ## Time -/

theorem schedule_tasks (s : KState) : (schedule s).tasks = s.tasks := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]

/-- **A tick wakes only tasks whose time has come.** If a timer tick changes a task's
status, the task was asleep until at most the new tick, or waiting for a message with a
deadline of at most the new tick (then it wakes with `eTimeout`, having received nothing);
either way it is now ready. -/
theorem tick_wakes_only_sleepers (s : KState) (j : Nat) {u u' : Task}
    (hu : nth? s.tasks j = some u) (hu' : nth? (tick s).tasks j = some u')
    (hch : u'.status ≠ u.status) :
    (∃ w, u.status = .sleeping w ∧ w ≤ s.now + 1 ∧ u'.status = .ready) ∨
    (∃ e w, u.status = .receiving e w ∧ w ≠ 0 ∧ w ≤ s.now + 1 ∧ u'.status = .ready ∧
      u'.result = eTimeout :: .nil) := by
  unfold tick at hu'
  rw [rotate_tasks] at hu'
  dsimp only at hu'
  rw [nth?_wakeSleepers, hu] at hu'
  simp only [Option.map_some, Option.some.injEq] at hu'
  subst hu'
  unfold wakeTask at hch ⊢
  split at hch
  · rename_i w hst
    split at hch
    · rename_i hle
      left
      exact ⟨w, hst, by simpa using hle, by simp [hle]⟩
    · exact absurd rfl hch
  · rename_i e w hst
    split at hch
    · rename_i hle
      right
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, Nat.ble_eq] at hle
      refine ⟨e, w, hst, hle.1, hle.2, ?_, ?_⟩ <;> simp [hle.1, hle.2]
    · exact absurd rfl hch
  · exact absurd rfl hch

/-! ## Power -/

@[simp] theorem ret_power (s : KState) (t : Task) (r : List Nat) : (ret s t r).power = 0 := rfl

/-- The only system call that asks the machine layer to switch off or restart is `power`. -/
theorem power_pos {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).power ≠ 0) :
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ ci a, syscall s num a0 a1 a2 a3 a4 = sysPower s t ci a := by
  unfold syscall at *
  split at *
  · simp at h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    split at *
    rotate_left
    · simp at h
    rcases runCall_cases s t num a0 a1 a2 a3 a4 with
      hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨-, _, _, hr⟩ <;>
      first | exact ⟨_, _, hr⟩ | simp [hr] at h

/-- **Only the display server can switch the machine off or restart it.** When a system
call asks the machine layer to do either, the caller is the display server: the power
capability is the manifest's, it never moves, and only the display server holds it. -/
theorem only_display_powers {s : KState} (hr : Reachable s) {num a0 a1 a2 a3 a4 : Nat}
    (hp : (syscall s num a0 a1 a2 a3 a4).power ≠ 0) : s.cur = displayTask := by
  obtain ⟨t, ht, ci, a, heq⟩ := power_pos hp
  rw [heq] at hp
  unfold sysPower at hp
  split at hp
  · simp at hp
  · rename_i c hc
    split at hp
    · rename_i hpow
      obtain ⟨c0, hc0, ho⟩ := ((reachable_inv hr).tasks _ t ht).caps c (nth?_mem hc) |>.power hpow
      have hj := (reachable_inv hr).lt ht
      have := manifestAll_spec (p := fun j c => match c.obj with
        | .power => j == displayTask
        | _ => true) (by decide) hj hc0
      simpa [ho] using this
    · simp at hp

/-! ## Programs from the SD card -/

@[simp] theorem ret_loadLen (s : KState) (t : Task) (r : List Nat) : (ret s t r).loadLen = 0 := rfl

/-- What a start that loads a program image checked: the slot is an open slot, and the
image is in pages the caller can read once the slot's memory is taken back. -/
theorem sysStart_image {s : KState} {t : Task} (ht : nth? s.tasks s.cur = some t) {ci src len : Nat}
    (hl : (sysStart s t ci src len).loadLen ≠ 0) :
    ∃ k t', (sysStart s t ci src len).load = k + 1 ∧ openSlot k = true ∧
      (sysStart s t ci src len).outVa = src ∧ (sysStart s t ci src len).loadLen = len ∧
      nth? (sysStart s t ci src len).state.tasks s.cur = some t' ∧
      imageOk t'.maps k src len = true := by
  unfold sysStart at *
  split at hl <;> (try simp at hl)
  rename_i c hc
  split at hl <;> (try simp at hl)
  rename_i k _
  split at hl <;> (try simp at hl)
  rename_i u hu
  split at hl <;> (try simp at hl)
  rename_i hok
  have hck : s.cur ≠ k := by
    intro e; subst e; simp at hok
  have himg : imageOk (dropMaps k t.maps) k src len = true := by
    first
      | exact hok.2
      | exact hok.2.2
      | (simp only [Bool.and_eq_true] at hok; exact hok.2)
  dsimp only at hl ⊢
  split at hl <;> (try simp at hl)
  rename_i t1 ht1
  split
  rotate_left
  · exfalso; simp_all
  have hopen : openSlot k = true := by
    cases ho : openSlot k
    · simp [imageOk, ho] at himg; exact absurd himg hl
    · rfl
  have ht1' : t1 = revokeTask k t := by
    simp only [setTask, nth?_setNth, nth?_revokeAll] at ht1
    simp [Ne.symm hck, ht] at ht1
    exact ht1.symm
  subst ht1'
  refine ⟨k, { revokeTask k t with result := 0 :: .nil }, rfl, hopen, rfl, rfl, ?_, himg⟩
  simp [setTask, nth?_setNth, nth?_revokeAll, Ne.symm hck, ht]

theorem loadLen_pos {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).loadLen ≠ 0) :
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ ci src len, syscall s num a0 a1 a2 a3 a4 = sysStart s t ci src len := by
  unfold syscall at *
  split at *
  · simp at h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    split at *
    rotate_left
    · simp at h
    rcases runCall_cases s t num a0 a1 a2 a3 a4 with
      hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨-, _, _, hr⟩ <;>
      first | exact ⟨_, _, _, hr⟩ | simp [hr] at h

/-- **A program from the SD card is read only from memory its loader may read.** When a
call asks the machine layer to load a program image into a slot, the slot is an open slot,
the image is at most `maxImage` bytes, and every byte of it is in the user window, in a page
the calling task (Terminal) has mapped readable, in its address space as it is after the
start. Whatever the program then does, it holds only what the manifest gives an open
slot: `confined` and the other guarantees hold for it as for any task. -/
theorem exec_reads_only_readable (s : KState) (num a0 a1 a2 a3 a4 : Nat)
    (hl : (syscall s num a0 a1 a2 a3 a4).loadLen ≠ 0) :
    ∃ k t', (syscall s num a0 a1 a2 a3 a4).load = k + 1 ∧ openSlot k = true ∧
      nth? (syscall s num a0 a1 a2 a3 a4).state.tasks s.cur = some t' ∧
      (syscall s num a0 a1 a2 a3 a4).loadLen ≤ maxImage ∧
      ∀ a, (syscall s num a0 a1 a2 a3 a4).outVa ≤ a →
        a < (syscall s num a0 a1 a2 a3 a4).outVa + (syscall s num a0 a1 a2 a3 a4).loadLen →
        userBase ≤ a ∧ ∃ m ∈ t'.maps, m.vpn = (a - userBase) / pageSize ∧ m.rights.r = true := by
  obtain ⟨t, ht, ci, src, len, heq⟩ := loadLen_pos hl
  rw [heq] at hl ⊢
  obtain ⟨k, t', hload, hopen, hva, hlen, ht', himg⟩ := sysStart_image ht hl
  refine ⟨k, t', hload, hopen, ht', ?_, ?_⟩
  · rw [hlen]
    simp only [imageOk, hopen, if_true, Bool.and_eq_true, Nat.ble_eq] at himg
    exact himg.1.1.2
  · rw [hva, hlen]
    simp only [imageOk, hopen, if_true, Bool.and_eq_true, Nat.ble_eq] at himg
    obtain ⟨⟨⟨h1, _⟩, hub⟩, hall⟩ := himg
    intro a ha1 ha2
    refine ⟨by omega, readableAt_spec (allReadable_spec hall ?_ ?_)⟩
    · exact Nat.div_le_div_right (by omega)
    · have : (a - userBase) / pageSize ≤ (src + len - 1 - userBase) / pageSize :=
        Nat.div_le_div_right (by omega)
      omega

/-! ## Scheduling -/

theorem findReady_ready : ∀ {busy : List Nat} {ts : List Task} {i fuel j : Nat},
    findReady busy ts i fuel = some j → runnable busy ts j = true
  | _, ts, i, 0, j, h => by simp [findReady] at h
  | _, ts, i, fuel + 1, j, h => by
    simp only [findReady] at h
    split at h
    · simp at h; subst h; assumption
    · exact findReady_ready h

/-- If the search finds nothing, none of the `fuel` tasks it looked at may run here. -/
theorem findReady_none : ∀ {busy : List Nat} {ts : List Task} {i fuel : Nat},
    findReady busy ts i fuel = none → ∀ k < fuel, runnable busy ts ((i + k) % len ts) = false
  | _, ts, i, 0, _, k, hk => by omega
  | _, ts, i, fuel + 1, h, k, hk => by
    simp only [findReady] at h
    split at h
    · simp at h
    · rename_i hnot
      cases k with
      | zero => simpa using hnot
      | succ k =>
        have := findReady_none h k (by omega)
        rwa [Nat.add_assoc, Nat.mod_add_mod, Nat.add_comm 1 k] at this

theorem isReady_lt {ts : List Task} {j : Nat} (h : isReady ts j = true) : j < len ts := by
  unfold isReady at h
  split at h
  · exact nth?_lt (by assumption)
  · simp at h

/-- Every index below `n` is `(i + k) % n` for some `k < n`. -/
theorem hits_every (i j n : Nat) (hj : j < n) : ∃ k < n, (i + k) % n = j := by
  have hn : 0 < n := by omega
  have hr : i % n < n := Nat.mod_lt _ hn
  by_cases h : i % n ≤ j
  · refine ⟨j - i % n, by omega, ?_⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt (a := j - i % n) (by omega),
      show i % n + (j - i % n) = j by omega, Nat.mod_eq_of_lt hj]
  · refine ⟨j + n - i % n, by omega, ?_⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt (a := j + n - i % n) (by omega),
      show i % n + (j + n - i % n) = j + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

/-- The round robin never runs a waiting or stopped task while one may run here. -/
theorem rotate_picks_ready (s : KState) (h : ∃ i, runnable s.busy s.tasks i = true) :
    runnable (rotate s).busy (rotate s).tasks (rotate s).cur = true := by
  obtain ⟨i, hi⟩ := h
  have hlt : i < len s.tasks := by
    unfold runnable at hi
    simp only [Bool.and_eq_true] at hi
    exact isReady_lt hi.1
  unfold rotate
  split
  · rename_i j hj
    exact findReady_ready hj
  · rename_i hnone
    obtain ⟨k, hk, hkj⟩ := hits_every (s.turn + 1) i (len s.tasks) hlt
    have := findReady_none hnone k hk
    rw [hkj, hi] at this
    exact absurd this (by simp)

/-- **The scheduler never runs a waiting or stopped task while a ready one exists, and never
one another core is running.** If some task is ready and no other core runs it, the task the
scheduler picks is ready and no other core runs it. -/
theorem schedule_picks_ready (s : KState) (h : ∃ i, runnable s.busy s.tasks i = true) :
    runnable (schedule s).busy (schedule s).tasks (schedule s).cur = true := by
  unfold schedule
  split
  · assumption
  · exact rotate_picks_ready _ h

/-! ## Wake-ups run next

A task woken by a message or an interrupt runs on the core that woke it, ahead of the tasks
waiting for their turn: a key goes from the input driver to the display to the app without
waiting behind programs that only compute. The preference is for one pick only, and the
timer never follows it (`tick`, `rotate`), so it cannot keep a ready task waiting for good
(`run_bounded_wait` in `Fair.lean`). -/

/-- **A task a wake-up chose runs next.** When the task running here stops, the task a
message or an interrupt woke last runs here, before any task waiting for its turn, if it
may run here: it is ready and no other core runs it. -/
theorem schedule_prefers_woken (s : KState) (h : runnable s.busy s.tasks s.next = true) :
    (schedule s).cur = s.next := by
  unfold schedule; simp [h]

/-- **A wake-up's choice lasts one pick.** Whatever the scheduler picks, no task is chosen
by a wake-up any more, until the next one. -/
theorem schedule_spends_woken (s : KState) : (schedule s).next = noTask := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]

/-- With no wake-up's choice that may run here, the scheduler is the round robin. -/
theorem schedule_rotates (s : KState) (h : runnable s.busy s.tasks s.next = false) :
    schedule s = rotate { s with next := noTask } := by
  unfold schedule; simp [h]

/-- **An interrupt runs its holder at once.** If interrupt line `n` firing changes task
`j`'s status (it woke the task waiting for the line), and no other core runs `j`, then `j`
runs now on the core that took the interrupt, and the task it took the core from runs
after it. -/
theorem irq_runs_holder (s : KState) (n j : Nat) {u u' : Task}
    (hu : nth? s.tasks j = some u) (hu' : nth? (irqFired s n).tasks j = some u')
    (hch : u'.status ≠ u.status) (hb : memNat j s.busy = false) :
    (irqFired s n).cur = j ∧ (irqFired s n).next = s.cur := by
  unfold irqFired at hu' ⊢
  cases hk : findIrqWaiter n s.tasks 0 with
  | none =>
    simp only [hk] at hu'
    split at hu'
    · rw [hu] at hu'; cases hu'; exact absurd rfl hch
    · simp [hu] at hu'; subst hu'; exact absurd rfl hch
  | some k =>
    cases hv : nth? s.tasks k with
    | none => simp only [hk, hv] at hu'; rw [hu] at hu'; cases hu'; exact absurd rfl hch
    | some v =>
      simp only [hk, hv, preempt_tasks] at hu' ⊢
      by_cases hkj : k = j
      · subst hkj
        have hr : runnable (setTask s k { v with status := .ready, result := 0 :: .nil }).busy
            (setTask s k { v with status := .ready, result := 0 :: .nil }).tasks k = true := by
          simp [runnable, isReady, setTask, nth?_setNth, hv, hb]
        unfold preempt; rw [if_pos hr]; exact ⟨rfl, rfl⟩
      · simp [setTask, nth?_setNth, hkj, hu] at hu'; subst hu'; exact absurd rfl hch

/-- **An interrupt never runs a task another core runs.** Taking an interrupt either leaves
this core's task as it was or gives it a task that no other core is running. -/
theorem irq_not_on_other_core (s : KState) (n : Nat) :
    (irqFired s n).cur = s.cur ∨ memNat (irqFired s n).cur (irqFired s n).busy = false := by
  unfold irqFired
  split
  · split
    · unfold preempt
      split
      · rename_i hr
        right
        simp only [runnable, Bool.and_eq_true, Bool.not_eq_true'] at hr
        exact hr.2
      · exact Or.inl rfl
    · exact Or.inl rfl
  · split <;> exact Or.inl rfl

/-- A send or a call that wakes a task (the receiver) makes it run next here; a call, which
waits for the reply, runs it now. -/
theorem send_wakes_next (s : KState) (t : Task) (ci w0 w1 w2 gi : Nat) (call : Bool) {j : Nat}
    {u u' : Task} (hj : j ≠ s.cur) (hu : nth? s.tasks j = some u) (hnr : u.status ≠ .ready)
    (hu' : nth? (sysSend s t ci w0 w1 w2 gi call).state.tasks j = some u') (hr' : u'.status = .ready)
    (hb : memNat j s.busy = false) :
    (sysSend s t ci w0 w1 w2 gi call).state.next = j ∨ (sysSend s t ci w0 w1 w2 gi call).state.cur = j := by
  generalize hr : sysSend s t ci w0 w1 w2 gi call = r at hu' ⊢
  unfold sysSend at hr
  repeat' (first | split at hr | dsimp only at hr)
  all_goals subst hr
  all_goals simp only [ret, wake_tasks, wake_cur, schedule_tasks, setTask, nth?_setNth, Ne.symm hj, if_false,
    Option.map_some, hu] at hu'
  all_goals first
    | (cases hu'; exact absurd hr' hnr)
    | (split at hu'
       · subst_vars
         first
           | (left; rfl)
           | (right; apply schedule_prefers_woken
              have := Ne.symm hj
              simp_all [runnable, isReady, wake, setTask, nth?_setNth])
       · cases hu'; exact absurd hr' hnr)

/-- A receive that wakes a task (a plain sender whose message it took) makes it run next
here. -/
theorem recv_wakes_next (s : KState) (t : Task) (ci : Nat) (block : Bool) (deadline : Nat) {j : Nat}
    {u u' : Task} (hj : j ≠ s.cur) (hu : nth? s.tasks j = some u) (hnr : u.status ≠ .ready)
    (hu' : nth? (sysRecv s t ci block deadline).state.tasks j = some u') (hr' : u'.status = .ready) :
    (sysRecv s t ci block deadline).state.next = j := by
  generalize hr : sysRecv s t ci block deadline = r at hu' ⊢
  unfold sysRecv at hr
  repeat' (first | split at hr | dsimp only at hr)
  all_goals subst hr
  all_goals simp only [ret, serve, wakeSender_tasks, wakeSender_cur, schedule_tasks, setTask, nth?_setNth,
    Ne.symm hj, if_false, Option.map_some, hu] at hu'
  all_goals first
    | (cases hu'; exact absurd hr' hnr)
    | (split at hu'
       · subst_vars
         simp only [serve, wakeSender]
         split
         · cases hu'; simp_all
         · first | rfl | simp_all
       · cases hu'; exact absurd hr' hnr)

/-- A reply that wakes a task (its caller) makes it run next here. -/
theorem reply_wakes_next (s : KState) (t : Task) (slot w0 w1 w2 : Nat) {j : Nat}
    {u u' : Task} (hj : j ≠ s.cur) (hu : nth? s.tasks j = some u) (hnr : u.status ≠ .ready)
    (hu' : nth? (sysReply s t slot w0 w1 w2).state.tasks j = some u') (hr' : u'.status = .ready) :
    (sysReply s t slot w0 w1 w2).state.next = j := by
  generalize hr : sysReply s t slot w0 w1 w2 = r at hu' ⊢
  unfold sysReply at hr
  repeat' (first | split at hr | dsimp only at hr)
  all_goals subst hr
  all_goals simp only [ret, wake_tasks, wake_cur, setTask, nth?_setNth, Ne.symm hj, if_false, Option.map_some,
    hu] at hu'
  all_goals first
    | (cases hu'; exact absurd hr' hnr)
    | (split at hu'
       · subst_vars; rfl
       · cases hu'; exact absurd hr' hnr)

/-- **A message wakes a task to run next.** When a send, a call, a receive or a reply wakes a
task (one that was not ready is now), that task runs next on this core, when the caller
stops (`schedule_prefers_woken`); a call, which waits for the reply, runs it now. (A task
not ready is never running on another core, which the machine layer says in `enter`.) -/
theorem wake_runs_next {s : KState} {t : Task} {num a0 a1 a2 a3 a4 : Nat}
    (hr : (∃ ci gi call, runCall s t num a0 a1 a2 a3 a4 = sysSend s t ci a0 a1 a2 gi call) ∨
      (∃ ci block deadline, runCall s t num a0 a1 a2 a3 a4 = sysRecv s t ci block deadline) ∨
      (∃ slot, runCall s t num a0 a1 a2 a3 a4 = sysReply s t slot a0 a1 a2))
    {j : Nat} {u u' : Task} (hj : j ≠ s.cur) (hu : nth? s.tasks j = some u) (hnr : u.status ≠ .ready)
    (hu' : nth? (runCall s t num a0 a1 a2 a3 a4).state.tasks j = some u') (hr' : u'.status = .ready)
    (hb : memNat j s.busy = false) :
    (runCall s t num a0 a1 a2 a3 a4).state.next = j ∨ (runCall s t num a0 a1 a2 a3 a4).state.cur = j := by
  rcases hr with ⟨ci, gi, call, h⟩ | ⟨ci, block, deadline, h⟩ | ⟨slot, h⟩ <;> rw [h] at hu' ⊢
  · exact send_wakes_next s t ci a0 a1 a2 gi call hj hu hnr hu' hr' hb
  · exact Or.inl (recv_wakes_next s t ci block deadline hj hu hnr hu' hr')
  · exact Or.inl (reply_wakes_next s t slot a0 a1 a2 hj hu hnr hu' hr')

/-! ## The certified clock

The kernel keeps time as `now`, the number of timer ticks since boot. The clock program
shows what `time` returns. These theorems say what that number is: it moves only on a
timer tick, by exactly one, never back; `time` reads it without changing anything else;
the hours, minutes and seconds it hands out are exactly the uptime; and `sleep` never ends
before the time asked for. That each tick is 10 ms apart is the machine layer's timer
programming (trusted, see TRUST.md). -/

@[simp] theorem now_setTask (s : KState) (j : Nat) (t : Task) : (setTask s j t).now = s.now := rfl

@[simp] theorem now_schedule (s : KState) : (schedule s).now = s.now := by
  obtain ⟨c, t, h⟩ := schedule_eq s; rw [h]

@[simp] theorem now_killCurrent (s : KState) : (killCurrent s).now = s.now := by
  unfold killCurrent; split <;> simp


/-- With four cores: the task the scheduler picks for a core is never one another core is
running (the machine layer tells the kernel which those are, `enter`), so no task ever runs
on two cores at once. -/
theorem schedule_not_on_other_core (s : KState) (h : ∃ i, runnable s.busy s.tasks i = true) :
    memNat (schedule s).cur (schedule s).busy = false := by
  have hr := schedule_picks_ready s h
  unfold runnable at hr
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr
  exact hr.2

/-- `enter` changes only which task is current and which the other cores run. -/
theorem enter_only_cores (s : KState) (c b0 b1 b2 : Nat) :
    (enter s c b0 b1 b2).tasks = s.tasks ∧ (enter s c b0 b1 b2).now = s.now ∧
    (enter s c b0 b1 b2).cur = c ∧ (enter s c b0 b1 b2).busy = b0 :: b1 :: b2 :: .nil := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A timer tick moves the clock by exactly one.** -/
theorem tick_now (s : KState) : (tick s).now = s.now + 1 := by
  unfold tick; simp

theorem clearResult_now (s : KState) (j : Nat) : (clearResult s j).now = s.now := by
  unfold clearResult; split <;> simp

theorem irqFired_now (s : KState) (n : Nat) : (irqFired s n).now = s.now := by
  unfold irqFired; repeat' split
  all_goals simp

theorem verify_now (s : KState) (i : Nat) (h : List Nat) : (verify s i h).now = s.now := by
  unfold verify; repeat' split
  all_goals simp

theorem ioFailed_now (s : KState) : (ioFailed s).now = s.now := by
  unfold ioFailed; split <;> simp

theorem boardDone_now (s : KState) (a b c d e : Nat) : (boardDone s a b c d e).now = s.now := by
  unfold boardDone; split <;> simp

theorem ret_now (s : KState) (t : Task) (r : List Nat) : (ret s t r).state.now = s.now := rfl

/-- **No system call changes the clock.** Only the timer does. -/
theorem syscall_now (s : KState) (num a0 a1 a2 a3 a4 : Nat) :
    (syscall s num a0 a1 a2 a3 a4).state.now = s.now := by
  unfold syscall
  split
  · rfl
  · rename_i t _
    split
    · rcases runCall_cases s t num a0 a1 a2 a3 a4 with
        hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨-, _, _, hr⟩ <;>
        simp [hr]
    · rfl

@[simp] theorem ret_wall (s : KState) (t : Task) (r : List Nat) : (ret s t r).state.wall = s.wall := rfl
@[simp] theorem setTask_wall (s : KState) (j : Nat) (t : Task) : (setTask s j t).wall = s.wall := rfl
@[simp] theorem killCurrent_wall (s : KState) : (killCurrent s).wall = s.wall := by
  unfold killCurrent; split <;> simp

/-- **Only `setwall` changes the time of day.** -/
theorem syscall_wall (s : KState) (num a0 a1 a2 a3 a4 : Nat) (hn : num ≠ 27) :
    (syscall s num a0 a1 a2 a3 a4).state.wall = s.wall := by
  unfold syscall
  split
  · rfl
  · rename_i t _
    split
    · rcases runCall_cases s t num a0 a1 a2 a3 a4 with
        hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨hr, -⟩ <;>
        first | exact absurd hr hn | simp [hr]
    · rfl

/-- **Only the USB driver says what time it is.** A system call that changes the time of
day was made by the USB driver: only `setwall` changes it, and only through the time
capability, which only the USB driver was given and which never moves. -/
theorem only_usb_driver_sets_time {s : KState} (hr : Reachable s) {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).state.wall ≠ s.wall) : s.cur = usbTask := by
  by_cases hn : num = 27
  · subst hn
    unfold syscall at h
    split at h
    · simp at h
    · rename_i t ht
      split at h
      · change (sysSetWall s t a0 a1).state.wall ≠ s.wall at h
        unfold sysSetWall at h
        split at h
        · simp at h
        · rename_i c hc
          split at h
          · rename_i hw
            obtain ⟨c0, hc0, ho⟩ := ((reachable_inv hr).tasks _ t ht).caps c (nth?_mem hc) |>.wall hw
            have hj := (reachable_inv hr).lt ht
            have := manifestAll_spec (p := fun j c => match c.obj with
              | .wallClock => j == usbTask
              | _ => true) (by decide) hj hc0
            simpa [ho] using this
          · simp at h
      · simp at h
  · exact absurd (syscall_wall s num a0 a1 a2 a3 a4 hn) h

/-- **The clock never goes back.** Every step the machine can take leaves `now` where it was
or, on a timer tick, one further on. -/
theorem clock_monotone (s : KState) :
    (∀ num a0 a1 a2 a3 a4, (syscall s num a0 a1 a2 a3 a4).state.now = s.now) ∧
    (tick s).now = s.now + 1 ∧ (killCurrent s).now = s.now ∧
    (∀ j, (clearResult s j).now = s.now) ∧ (∀ n, (irqFired s n).now = s.now) ∧
    (∀ i h, (verify s i h).now = s.now) ∧ (ioFailed s).now = s.now ∧
    (∀ a b c d e, (boardDone s a b c d e).now = s.now) ∧ (∀ v, (usbDone s v).now = s.now) ∧
    (∀ c b0 b1 b2, (enter s c b0 b1 b2).now = s.now) ∧ (schedule s).now = s.now :=
  ⟨syscall_now s, tick_now s, now_killCurrent s, clearResult_now s, irqFired_now s, verify_now s,
    ioFailed_now s, boardDone_now s, fun v => by unfold usbDone; split <;> simp,
    fun _ _ _ _ => rfl, now_schedule s⟩

/-- Hours, minutes and seconds add back up to the whole seconds, and read like a clock. -/
theorem clockOf_spec (ms : Nat) :
    (clockOf ms).1 * 3600 + (clockOf ms).2.1 * 60 + (clockOf ms).2.2 = ms / 1000 ∧
    (clockOf ms).2.1 < 60 ∧ (clockOf ms).2.2 < 60 := by
  unfold clockOf
  dsimp only
  refine ⟨?_, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
  omega

/-- **What `time` returns is the kernel's clock, and nothing else changes.** The caller
gets `now`, the milliseconds since boot, and hours, minutes and seconds that add up to
exactly those whole seconds, and the time of day (`wallNow`); the state is the old one with
only the caller's results set. -/
theorem time_reads_clock (s : KState) (t : Task) :
    ∃ h m sec, (sysTime s t).state = setTask s s.cur
        { t with result := 0 :: s.now :: s.now * tickMs :: h :: m :: sec :: wallNow s :: .nil } ∧
      h * 3600 + m * 60 + sec = s.now * tickMs / 1000 ∧ m < 60 ∧ sec < 60 ∧
      (sysTime s t).outLen = 0 ∧ (sysTime s t).io = 0 ∧ (sysTime s t).power = 0 ∧
      (sysTime s t).board = 0 ∧ (sysTime s t).load = 0 := by
  obtain ⟨h1, h2, h3⟩ := clockOf_spec (s.now * tickMs)
  exact ⟨_, _, _, rfl, h1, h2, h3, rfl, rfl, rfl, rfl, rfl⟩

/-- **`sleep` never ends early, and is at most one tick late.** A task that asks to sleep
`ms > 0` milliseconds is asleep until tick `w`, and the ticks from now to `w` last at least
`ms` and less than `ms` plus one tick. With `tick_wakes_only_sleepers` (a tick wakes a
sleeper only once `now` has reached its `w`), it cannot wake before its time. -/
theorem sleep_on_time (s : KState) (t : Task) (ms : Nat) (hms : 0 < ms)
    (ht : nth? s.tasks s.cur = some t) :
    ∃ w u, nth? (sysSleep s t ms).state.tasks s.cur = some u ∧ u.status = .sleeping w ∧
      s.now ≤ w ∧ ms ≤ (w - s.now) * tickMs ∧ (w - s.now) * tickMs < ms + tickMs := by
  have hlt : s.cur < len s.tasks := by
    exact nth?_lt ht
  unfold sysSleep
  dsimp only
  have hpos : (ms + tickMs - 1) / tickMs ≠ 0 := by simp [tickMs]; omega
  simp only [hpos, if_false, schedule_tasks, setTask, nth?_setNth, if_pos, ht, Option.map_some]
  refine ⟨s.now + (ms + tickMs - 1) / tickMs, _, rfl, rfl, Nat.le_add_right _ _, ?_, ?_⟩ <;>
    simp only [Nat.add_sub_cancel_left, tickMs] <;> omega

/-! ## The Raspberry Pi's settings

The board capability lets its holder read the board and its sensors and change two
things: the CPU clock and the activity light. These theorems say which requests can reach
the machine layer at all, from whom, and with which right. -/

@[simp] theorem ret_board (s : KState) (t : Task) (r : List Nat) : (ret s t r).board = 0 := rfl

theorem board_pos {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).board ≠ 0) :
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ ci w v, syscall s num a0 a1 a2 a3 a4 = sysBoard s t ci w v := by
  unfold syscall at *
  split at *
  · simp at h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    split at *
    rotate_left
    · simp at h
    rcases runCall_cases s t num a0 a1 a2 a3 a4 with
      hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨-, _, _, hr⟩ <;>
      first | exact ⟨_, _, _, hr⟩ | simp [hr] at h


/-- `boardRequest` asks for nothing, or for something on the list. -/
theorem boardRequest_listed (w v : Nat) : boardRequest w v = 0 ∨ boardRequest w v ∈ boardRequests := by
  unfold boardRequest
  by_cases h0 : w = 0
  · simp [h0, boardRequests]
  by_cases h1 : w = 1
  · simp [h1, boardRequests]
  by_cases h2 : w = 2
  · simp only [h2, if_true]
    rcases v with _ | _ | _ | v <;> simp [nth?, cpuSpeeds, boardRequests]
  by_cases h3 : w = 3 ∧ v < 2
  · simp only [h3, if_true, and_self]
    right
    rcases h3 with ⟨_, hv⟩
    rcases v with _ | _ | v
    · simp [boardRequests]
    · simp [boardRequests]
    · omega
  · simp [h0, h1, h2, h3]

/-- **Only listed requests ever reach the hardware.** Whatever a task passes, a system call
asks the machine layer for nothing, or for one of `boardRequests`: read the board, read the
sensors, the light off or on, or the CPU at 600, 1000 or 1500 MHz. -/
theorem board_requests_listed (s : KState) (num a0 a1 a2 a3 a4 : Nat) :
    (syscall s num a0 a1 a2 a3 a4).board = 0 ∨ (syscall s num a0 a1 a2 a3 a4).board ∈ boardRequests := by
  by_cases h : (syscall s num a0 a1 a2 a3 a4).board = 0
  · exact Or.inl h
  obtain ⟨t, _, ci, w, v, heq⟩ := board_pos h
  rw [heq] at h ⊢
  unfold sysBoard at h ⊢
  repeat' (first | split at h | split | dsimp only at h ⊢)
  all_goals first
    | (left; rfl)
    | (simp at h; done)
    | exact boardRequest_listed _ _

/-- **The CPU is never overclocked.** Any CPU clock a system call asks the machine layer
for is between 600 and 1500 MHz: a Pi 4's rated range. (Requests 1 to 4 are the reads and
the light; every other request is a clock.) -/
theorem cpu_never_overclocked (s : KState) (num a0 a1 a2 a3 a4 : Nat)
    (h : 4 < (syscall s num a0 a1 a2 a3 a4).board) :
    600 ≤ (syscall s num a0 a1 a2 a3 a4).board ∧ (syscall s num a0 a1 a2 a3 a4).board ≤ 1500 := by
  rcases board_requests_listed s num a0 a1 a2 a3 a4 with h0 | hl
  · omega
  · generalize (syscall s num a0 a1 a2 a3 a4).board = b at h hl ⊢
    simp [boardRequests, cpuSpeeds] at hl
    omega

/-- **Changes need the write right; reads, the read right.** A board request reaches the
machine layer only through a board capability the caller holds, with the right that kind of
request needs, and the call asks for nothing else: no printing, no disk, no power, no load. -/
theorem board_needs_right (s : KState) (t : Task) (ci w v : Nat)
    (h : (sysBoard s t ci w v).board ≠ 0) :
    ∃ c, nth? t.caps ci = some c ∧ c.obj = .board ∧
      (boardChanges (sysBoard s t ci w v).board = true → c.rights.w = true) ∧
      (boardChanges (sysBoard s t ci w v).board = false → c.rights.r = true) ∧
      (sysBoard s t ci w v).outLen = 0 ∧ (sysBoard s t ci w v).io = 0 ∧
      (sysBoard s t ci w v).power = 0 ∧ (sysBoard s t ci w v).load = 0 ∧
      (sysBoard s t ci w v).state = setTask s s.cur { t with result := 0 :: .nil } := by
  cases hc : nth? t.caps ci with
  | none => unfold sysBoard at h; simp [hc] at h
  | some c =>
    cases hobj : c.obj
    all_goals try (unfold sysBoard at h; simp [hc, hobj] at h; done)
    unfold sysBoard at h ⊢
    simp only [hc, hobj] at h ⊢
    refine ⟨c, rfl, hobj, ?_⟩
    cases hch : boardChanges (boardRequest w v) <;> cases hw : c.rights.w <;> cases hr : c.rights.r <;>
      by_cases h0 : boardRequest w v = 0 <;> simp_all [ret]

/-- **Only Settings touches the board.** When a system call asks the machine layer to read
or change the board, the caller is Settings: the board capability is the manifest's, only
frames can be granted, so it never moves, and only Settings holds it. -/
theorem only_settings_touches_board {s : KState} (hr : Reachable s) {num a0 a1 a2 a3 a4 : Nat}
    (hp : (syscall s num a0 a1 a2 a3 a4).board ≠ 0) : s.cur = settingsTask := by
  obtain ⟨t, ht, ci, w, v, heq⟩ := board_pos hp
  rw [heq] at hp
  unfold sysBoard at hp
  split at hp
  · simp at hp
  · rename_i c hc
    split at hp
    · rename_i hb
      obtain ⟨c0, hc0, ho⟩ := ((reachable_inv hr).tasks _ t ht).caps c (nth?_mem hc) |>.board hb
      have hj := (reachable_inv hr).lt ht
      have := manifestAll_spec (p := fun j c => match c.obj with
        | .board => j == settingsTask
        | _ => true) (by decide) hj hc0
      simpa [ho] using this
    · simp at hp

/-! ## The USB host controller

The theorems behind `sysUsb`: only the USB driver reaches the controller; a DMA transfer
starts only inside frames the driver holds, with the right its direction needs; those
frames are the driver's own (nobody can pass memory to it, and it cannot pass memory on);
and the writes that could aim DMA anywhere else never reach the controller. -/

@[simp] theorem ret_usbOp (s : KState) (t : Task) (r : List Nat) : (ret s t r).usbOp = 0 := rfl

theorem usb_pos {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).usbOp ≠ 0) :
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ ci op reg v, syscall s num a0 a1 a2 a3 a4 = sysUsb s t ci op reg v := by
  unfold syscall at *
  split at *
  · simp at h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    split at *
    rotate_left
    · simp at h
    rcases runCall_cases s t num a0 a1 a2 a3 a4 with
      hr | hr | ⟨_, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨-, _, _, hr⟩ <;>
      first | exact ⟨_, _, _, _, hr⟩ | simp [hr] at h



/-- What a USB reply asks of the machine layer, and what the kernel checked first. -/
theorem sysUsb_spec {s : KState} {t : Task} {ci op reg v : Nat} (h : (sysUsb s t ci op reg v).usbOp ≠ 0) :
    ∃ c, nth? t.caps ci = some c ∧ c.obj = .usbHost ∧
    let r := sysUsb s t ci op reg v
    ((r.usbOp = 3 ∧ c.rights.r = true ∧ r.usbA % 4 = 0 ∧ r.usbA < 0x1000) ∨
     (r.usbOp = 1 ∧ c.rights.w = true ∧ usbForbidden r.usbA r.usbB = false ∧
        ¬(inChan r.usbA = true ∧ (chanReg r.usbA = 0x14 ∨ chanReg r.usbA = 0x10)) ∧
        ¬(inChan r.usbA = true ∧ chanReg r.usbA = 0 ∧ bit r.usbB 31 = true ∧ bit r.usbB 30 = false)) ∨
     (r.usbOp = 2 ∧ c.rights.w = true ∧ r.usbA < 8 ∧
        r.usbB = nthD s.usbDma r.usbA ∧ r.usbC = nthD s.usbSize r.usbA ∧
        dmaOk s.cur t.caps r.usbB (r.usbC % 2 ^ 19 + usbSlack) (bit r.usbD 15) = true)) := by
  unfold sysUsb usbReply at *
  cases hc : nth? t.caps ci with
  | none => simp [hc] at h
  | some c =>
    simp only [hc] at h ⊢
    cases ho : c.obj
    all_goals try (simp [ho] at h; done)
    simp only [ho] at h ⊢
    refine ⟨c, rfl, ho, ?_⟩
    by_cases hop0 : op = 0
    · subst hop0
      simp only [if_true] at h ⊢
      split at h
      · rename_i hr
        simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hr
        simp only [if_pos (by simp [hr.1.1, hr.1.2, hr.2] : (c.rights.r && reg % 4 == 0 && Nat.ble (reg + 1) 0x1000) = true)]
        left; exact ⟨by simp, hr.1.1, hr.1.2, by omega⟩
      · simp at h
    · simp only [hop0, if_false] at h ⊢
      split at h
      · rename_i hw
        rw [if_pos hw]
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
        obtain ⟨⟨_, hwr⟩, hf⟩ := hw
        split at h
        · simp at h
        · rename_i hd
          rw [if_neg hd]
          split at h
          · simp at h
          · rename_i hz
            rw [if_neg hz]
            split at h
            · rename_i hen
              rw [if_pos hen]
              try dsimp only at h ⊢
              split at h
              · rename_i hok
                rw [if_pos hok]
                right; right
                simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, inChan] at hen
                refine ⟨by simp, hwr, ?_, by simp, by simp, hok⟩
                show chanOf reg < 8
                unfold chanOf; omega
              · simp at h
            · rename_i hen
              rw [if_neg hen]
              right; left
              refine ⟨by simp, hwr, hf, ?_, ?_⟩
              · rintro ⟨hi, hr | hr⟩
                · exact hd (by simp [hi, hr])
                · exact hz (by simp [hi, hr])
              · rintro ⟨hi, hr, h31, h30⟩
                exact hen (by simp [hi, hr, h31, h30])
      · simp at h

/-- **Only the USB driver reaches the USB controller.** When a system call asks the machine
layer to read or write the controller, the caller is the USB driver: the USB capability is
the manifest's, only frames can be granted, so it never moves, and only the driver holds it. -/
theorem only_usb_driver_drives_usb {s : KState} (hr : Reachable s) {num a0 a1 a2 a3 a4 : Nat}
    (hp : (syscall s num a0 a1 a2 a3 a4).usbOp ≠ 0) : s.cur = usbTask := by
  obtain ⟨t, ht, ci, op, reg, v, heq⟩ := usb_pos hp
  rw [heq] at hp
  obtain ⟨c, hc, hu, -⟩ := sysUsb_spec hp
  obtain ⟨c0, hc0, ho⟩ := ((reachable_inv hr).tasks _ t ht).caps c (nth?_mem hc) |>.usb hu
  have hj := (reachable_inv hr).lt ht
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .usbHost => j == usbTask
    | _ => true) (by decide) hj hc0
  simpa [ho] using this

theorem dmaOk_spec {j : Nat} : ∀ {cs : List Cap} {a n : Nat} {w : Bool}, dmaOk j cs a n w = true →
    ∃ c ∈ cs, ∃ b k, c.obj = .frames b k ∧ framesPerTask * j ≤ b ∧ b + k ≤ framesPerTask * (j + 1) ∧
      b + k ≤ poolFrames ∧ frameBase + b * pageSize ≤ a ∧
      a + n ≤ frameBase + (b + k) * pageSize ∧ (if w then c.rights.w else c.rights.r) = true
  | [], _, _, _, h => by simp [dmaOk] at h
  | c :: cs, a, n, w, h => by
    unfold dmaOk at h
    rcases Bool.or_eq_true_iff.1 h with h1 | h1
    · split at h1
      · rename_i b k hbk
        simp only [Bool.and_eq_true, Nat.ble_eq] at h1
        exact ⟨c, List.mem_cons_self, b, k, hbk, h1.1.1.1.1.1, h1.1.1.1.1.2, h1.1.1.1.2, h1.1.1.2, h1.1.2, h1.2⟩
      · simp at h1
    · obtain ⟨c', hc', rest⟩ := dmaOk_spec h1
      exact ⟨c', List.mem_cons_of_mem _ hc', rest⟩

/-- **A USB transfer starts only inside the driver's memory.** When a system call asks the
machine layer to start a USB channel, the whole transfer (its size, plus one packet of
slack) lies in one run of the caller's own frames in the pool, which it holds, with the
write right if data comes in and the read right if it goes out: never in memory another
task lent it. -/
theorem usb_dma_confined {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).usbOp = 2) :
    ∃ t, nth? s.tasks s.cur = some t ∧ ∃ c ∈ t.caps, ∃ b k, c.obj = .frames b k ∧
      framesPerTask * s.cur ≤ b ∧ b + k ≤ framesPerTask * (s.cur + 1) ∧
      b + k ≤ poolFrames ∧
      frameBase + b * pageSize ≤ (syscall s num a0 a1 a2 a3 a4).usbB ∧
      (syscall s num a0 a1 a2 a3 a4).usbB + ((syscall s num a0 a1 a2 a3 a4).usbC % 2 ^ 19 + usbSlack) ≤
        frameBase + (b + k) * pageSize ∧
      (if bit (syscall s num a0 a1 a2 a3 a4).usbD 15 then c.rights.w else c.rights.r) = true := by
  have hne : (syscall s num a0 a1 a2 a3 a4).usbOp ≠ 0 := by omega
  obtain ⟨t, ht, ci, op, reg, v, heq⟩ := usb_pos hne
  refine ⟨t, ht, ?_⟩
  rw [heq] at h ⊢
  obtain ⟨c, _, _, hs⟩ := sysUsb_spec (by omega : (sysUsb s t ci op reg v).usbOp ≠ 0)
  rcases hs with ⟨h3, -⟩ | ⟨h1, -⟩ | ⟨-, -, -, -, -, hok⟩
  · omega
  · omega
  · exact dmaOk_spec hok

/-- **The USB controller only ever touches the USB driver's own memory.** In every reachable
state, every byte a started transfer can reach is in a frame the manifest gave the USB
driver: it holds no other memory, since nobody may pass it memory and it cannot receive. -/
theorem usb_dma_own_memory {s : KState} (hr : Reachable s) {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).usbOp = 2) (x : Nat)
    (hx1 : (syscall s num a0 a1 a2 a3 a4).usbB ≤ x)
    (hx2 : x < (syscall s num a0 a1 a2 a3 a4).usbB + ((syscall s num a0 a1 a2 a3 a4).usbC % 2 ^ 19 + usbSlack)) :
    frameBase ≤ x ∧ owner ((x - frameBase) / pageSize) = usbTask := by
  have hcur := only_usb_driver_drives_usb hr (by omega : (syscall s num a0 a1 a2 a3 a4).usbOp ≠ 0)
  obtain ⟨t, ht, c, hc, b, k, ho, hown1, hown2, hpool, hlo, hhi, -⟩ := usb_dma_confined h
  rw [hcur] at hown1 hown2
  refine ⟨by simp only [pageSize, frameBase] at *; omega, ?_⟩
  -- the frame is one of the driver's own, whatever else it was lent
  have hf1 : framesPerTask * usbTask ≤ (x - frameBase) / pageSize := by
    simp only [pageSize, frameBase, framesPerTask, usbTask] at *; omega
  have hf2 : (x - frameBase) / pageSize < framesPerTask * (usbTask + 1) := by
    simp only [pageSize, frameBase, framesPerTask, usbTask] at *; omega
  unfold owner
  have hp : (x - frameBase) / pageSize < poolFrames := by
    simp only [pageSize, frameBase, framesPerTask, usbTask, poolFrames, maxTasks] at *; omega
  rw [if_pos hp]
  simp only [framesPerTask, usbTask] at hf1 hf2 ⊢
  omega

/-- **The dangerous USB writes never happen.** A plain register write the kernel passes on
is an aligned register in the first page (never the data FIFOs); never one of device mode's
registers (0x800-0xBFF, whose DMA addresses nobody checks); never forces device mode
(GUSBCFG bit 30) or turns on descriptor DMA (HCFG bit 23); never a channel's descriptor
list (HCDMAB), DMA address (HCDMA) or transfer size (HCTSIZ), which reach the controller
only when a checked transfer starts; and never starts a channel, which must go through
that check. -/
theorem usb_writes_safe {s : KState} {num a0 a1 a2 a3 a4 : Nat}
    (h : (syscall s num a0 a1 a2 a3 a4).usbOp = 1) :
    let reg := (syscall s num a0 a1 a2 a3 a4).usbA
    let v := (syscall s num a0 a1 a2 a3 a4).usbB
    reg % 4 = 0 ∧ reg < 0x1000 ∧ ¬(0x800 ≤ reg ∧ reg < 0xC00) ∧
    ¬(reg = 0x00C ∧ bit v 30 = true) ∧ ¬(reg = 0x400 ∧ bit v 23 = true) ∧
    ¬(inChan reg = true ∧ (chanReg reg = 0x1C ∨ chanReg reg = 0x14 ∨ chanReg reg = 0x10)) ∧
    ¬(inChan reg = true ∧ chanReg reg = 0 ∧ bit v 31 = true ∧ bit v 30 = false) := by
  have hne : (syscall s num a0 a1 a2 a3 a4).usbOp ≠ 0 := by omega
  obtain ⟨t, ht, ci, op, reg, v, heq⟩ := usb_pos hne
  rw [heq] at h ⊢
  obtain ⟨c, _, _, hs⟩ := sysUsb_spec (by omega : (sysUsb s t ci op reg v).usbOp ≠ 0)
  rcases hs with ⟨h3, -⟩ | ⟨-, -, hf, hd, hen⟩ | ⟨h2, -⟩
  · omega
  · generalize (sysUsb s t ci op reg v).usbA = R at hf hd hen ⊢
    generalize (sysUsb s t ci op reg v).usbB = V at hf hd hen ⊢
    simp only [usbForbidden, Bool.or_eq_false_iff, Bool.not_eq_false', beq_iff_eq, Nat.ble_eq,
      Bool.and_eq_false_imp] at hf
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hen⟩
    · exact hf.1.1.1.1.1
    · have := hf.1.1.1.1.2; omega
    · rintro ⟨a, b⟩
      have := hf.1.1.1.2 a
      have hb : Nat.ble (R + 1) 3072 = true := by rw [Nat.ble_eq]; omega
      rw [hb] at this; exact absurd this (by decide)
    · rintro ⟨a, b⟩; have := hf.1.1.2 a; simp_all
    · rintro ⟨a, b⟩; have := hf.1.2 a; simp_all
    · rintro ⟨hi, hr | hr | hr⟩
      · have := hf.2 hi; simp_all
      · exact hd ⟨hi, Or.inl hr⟩
      · exact hd ⟨hi, Or.inr hr⟩
  · omega

/-! ## The file server knows who is asking -/

/-- The badge task `j` sends to the file server with: Notes sends as 1, everyone else as its
own number. -/
def fsBadge (j : Nat) : Nat := if j = 0 then 1 else j

/-- **The file server knows who is asking.** In every reachable state, any capability to the
file server's endpoint (endpoint 1) that task `j` holds with the send right carries `j`'s own
badge, and the kernel delivers that badge with every message. So the file server can decide
what each program may reach by its badge: a program from the card, in open slot `k`,
arrives as `k` and nothing else, and cannot pass for Terminal, Files, Apps or Notes. -/
theorem file_server_knows_the_sender {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) (he : c.obj = .endpoint 1)
    (hw : c.rights.w = true) : c.badge = fsBadge j := by
  obtain ⟨c0, hc0, ho, hle, hb⟩ := endpoints_fixed h ht hc he
  have hw0 : c0.rights.w = true := by
    have := hle.2.1; simp_all
  rw [← hb]
  have := manifestAll_spec (p := fun j c => match c.obj with
    | .endpoint e => e != 1 || !c.rights.w || c.badge == fsBadge j
    | _ => true) (by decide) ((reachable_inv h).lt ht) hc0
  simpa [ho, hw0] using this

/-! ## Stopping a program -/

/-- A stop changes only the program it names: every other task but the caller is as it was,
and the named one only if the caller holds the launch capability for it. -/
theorem sysStop_only {s : KState} {t : Task} {ci j : Nat} (hj : j ≠ s.cur)
    (hch : nth? (sysStop s t ci).state.tasks j ≠ nth? s.tasks j) :
    ∃ c ∈ t.caps, c.obj = .launch j := by
  unfold sysStop at hch
  split at hch
  · simp [ret, setTask, nth?_setNth, Ne.symm hj] at hch
  · rename_i c hc
    split at hch
    · rename_i k hk
      split at hch
      · split at hch
        · by_cases hjk : j = k
          · subst hjk; exact ⟨c, nth?_mem hc, hk⟩
          · exfalso; apply hch
            simp [ret, setTask, nth?_setNth, Ne.symm hj, Ne.symm hjk]
        · simp [ret, setTask, nth?_setNth, Ne.symm hj] at hch
      · simp [ret, setTask, nth?_setNth, Ne.symm hj] at hch
    · simp [ret, setTask, nth?_setNth, Ne.symm hj] at hch

/-- **Only the right task can stop a program.** When `stop` changes any task but the caller,
the caller is the display server stopping one of the apps it starts, or Terminal or Apps
stopping a program from the card: nothing can stop the display server, the input driver,
the file server, the USB driver or the tests. -/
theorem only_launchers_stop {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks s.cur = some t)
    (hrd : t.status = .ready) {a0 a1 a2 a3 a4 j : Nat} (hj : j ≠ s.cur)
    (hch : nth? (syscall s 26 a0 a1 a2 a3 a4).state.tasks j ≠ nth? s.tasks j) :
    (s.cur = displayTask ∧ App j ∧ openSlot j = false) ∨ ((s.cur = 5 ∨ s.cur = 16) ∧ openSlot j = true) := by
  have hs : syscall s 26 a0 a1 a2 a3 a4 = sysStop s t a0 := by
    unfold syscall; rw [ht]; simp only [hrd]; rfl
  rw [hs] at hch
  obtain ⟨c, hc, hk⟩ := sysStop_only hj hch
  exact only_display_launches h ht hc hk

end LeanOS
