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
    m ∈ dropRange vpn count ms → m ∈ ms
  | _, 0, _, _, h => h
  | _, k + 1, _, _, h => (mem_dropVpn (mem_dropRange (count := k) h)).1

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

def CapOK (j : Nat) (c : Cap) : Prop :=
  (∀ f, Covers c f → FrameOK j f c.rights) ∧
  (∀ e, c.obj = .endpoint e → EndpointOK j e c.rights c.badge) ∧
  (∀ n, c.obj = .irq n → ∃ c0 ∈ initCaps j, c0.obj = .irq n)

/-- A task waiting to send carries only a frame, one that is fine for it to hold, through an
endpoint it was given send and grant rights on at boot. A task waiting to receive was
given the receive right on that endpoint at boot. -/
def StatusOK (j : Nat) : Status → Prop
  | .sending e m =>
    (∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ c0.rights.w = true ∧ c0.badge = m.badge) ∧
    ∀ g, m.grant = some g → CapOK j g ∧ (∃ b n, g.obj = .frames b n) ∧
      ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ c0.rights.w = true ∧ c0.rights.x = true
  | .receiving e => ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ c0.rights.r = true
  | .waitingIrq n => ∃ c0 ∈ initCaps j, c0.obj = .irq n
  | _ => True

/-- Task `j` is fine. `fb` says whether the framebuffer address is sane; framebuffer frames
are only ever mapped if it is. -/
structure TaskOK (fb : Bool) (j : Nat) (t : Task) : Prop where
  backed : ∀ m ∈ t.maps, ∃ c ∈ t.caps, Covers c m.frame ∧ c.rights = m.rights
  vpnOk : ∀ m ∈ t.maps, m.vpn < userPages
  caps : ∀ c ∈ t.caps, CapOK j c
  status : StatusOK j t.status
  fbMaps : ∀ m ∈ t.maps, m.frame < poolFrames ∨ (fb = true ∧ m.frame < devBase) ∨ devBase ≤ m.frame

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

theorem inv_schedule {s : KState} (hs : Inv s) : Inv (schedule s) := by
  unfold schedule
  split
  · exact ⟨hs.len, hs.tasks⟩
  · exact hs

/-- The registers a task will resume with play no part in the invariant. -/
theorem TaskOK.result {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (r : List Nat) :
    TaskOK fb j { t with result := r } := ⟨h.backed, h.vpnOk, h.caps, h.status, h.fbMaps⟩

theorem TaskOK.setStatus {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (st : Status)
    (hst : StatusOK j st) (r : List Nat) : TaskOK fb j { t with status := st, result := r } :=
  ⟨h.backed, h.vpnOk, h.caps, hst, h.fbMaps⟩

theorem inv_killCurrent {s : KState} (hs : Inv s) : Inv (killCurrent s) := by
  unfold killCurrent
  split
  · rename_i t ht
    exact inv_schedule (inv_setTask hs ((hs.tasks _ t ht).setStatus .dead trivial _))
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

theorem capOK_derive {j : Nat} {c : Cap} {o : Obj} {off cnt : Nat} (h : CapOK j c)
    (ho : subObj c.obj off cnt = some o) (r : Rights) : CapOK j ⟨o, c.rights.meet r, c.badge⟩ := by
  constructor
  · intro f hf
    obtain ⟨hlt, hwx, A, c0, hA, hr, hc0, hcov, hle⟩ := h.1 f (subObj_covers ho hf)
    exact ⟨hlt, not_wx_of_le (meet_le _ _) hwx, A, c0, hA, hr, hc0, hcov,
      RLe.trans (meet_le _ _) hle⟩
  constructor
  · intro e he
    obtain ⟨c0, hc0, hco, hle, hb⟩ := h.2.1 e (subObj_endpoint ho he)
    exact ⟨c0, hc0, hco, RLe.trans (meet_le _ _) hle, hb⟩
  · intro n hn
    exact h.2.2 n (subObj_irq ho hn)

/-- A frame capability that is fine for `A` to hold is fine for `B` to hold, if `A` can pass
frames to `B`. -/
theorem capOK_grant {A B : Nat} {g : Cap} (hg : CapOK A g) (hf : ∃ b n, g.obj = .frames b n)
    (he : Edge A B) : CapOK B g := by
  obtain ⟨b, n, hgf⟩ := hf
  constructor
  · intro f' hf'
    obtain ⟨hlt, hwx, C, c0, hC, hr, hc0, ho, hle⟩ := hg.1 f' hf'
    exact ⟨hlt, hwx, C, c0, hC, Reach.step hr he, hc0, ho, hle⟩
  constructor
  · intro e he'
    rw [hgf] at he'
    cases he'
  · intro n hn
    rw [hgf] at hn
    cases hn

/-- The endpoint rights a task holds now are rights it held at boot. -/
theorem boot_rights {j : Nat} {c : Cap} {e : Nat} (h : CapOK j c) (he : c.obj = .endpoint e) :
    ∃ c0 ∈ initCaps j, c0.obj = .endpoint e ∧ RLe c.rights c0.rights ∧ c0.badge = c.badge :=
  h.2.1 e he

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
    findReceiver e ts k = some j → k ≤ j ∧ ∃ u, nth? ts (j - k) = some u ∧ u.status = .receiving e
  | [], _, _, h => by simp [findReceiver] at h
  | t :: ts, k, j, h => by
    simp only [findReceiver] at h
    split at h
    · rename_i hr
      simp at h; subst h
      refine ⟨Nat.le_refl _, t, by simp [nth?], ?_⟩
      unfold isReceiving at hr
      split at hr
      · rename_i e' hst; simp at hr; subst hr; exact hst
      · simp at hr
    · obtain ⟨hk, u, hu, hst⟩ := findReceiver_spec h
      refine ⟨by omega, u, ?_, hst⟩
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this]; simpa [nth?] using hu

theorem findSender_spec {e : Nat} : ∀ {ts : List Task} {k j : Nat} {m : Msg},
    findSender e ts k = some (j, m) →
      k ≤ j ∧ ∃ u, nth? ts (j - k) = some u ∧ u.status = .sending e m
  | [], _, _, _, h => by simp [findSender] at h
  | t :: ts, k, j, m, h => by
    simp only [findSender] at h
    split at h
    · rename_i m' hm
      simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨Nat.le_refl _, t, by simp [nth?], ?_⟩
      unfold sendingMsg at hm
      split at hm
      · rename_i e' m'' hst
        split at hm
        · rename_i hee; simp at hee hm; subst hee; subst hm; exact hst
        · simp at hm
      · simp at hm
    · obtain ⟨hk, u, hu, hst⟩ := findSender_spec h
      refine ⟨by omega, u, ?_, hst⟩
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this]; simpa [nth?] using hu

/-- What a delivery can change: the receiver's capabilities grow by at most the granted one,
its mappings stay the same, and it becomes ready. -/
theorem deliver_spec {u u' : Task} {m : Msg} {sender : Nat} (hd : deliver u m sender = some u') :
    u'.maps = u.maps ∧ u'.status = .ready ∧
      (u'.caps = u.caps ∨ ∃ c, m.grant = some c ∧ u'.caps = snoc u.caps c) := by
  unfold deliver at hd
  dsimp only at hd
  repeat' split at hd
  all_goals first
    | (simp at hd; done)
    | (simp only [Option.some.injEq] at hd; subst hd
       first
         | exact ⟨rfl, rfl, Or.inl rfl⟩
         | exact ⟨rfl, rfl, Or.inr ⟨_, by assumption, rfl⟩⟩)

/-- Receiving a message leaves a task fine, as long as a granted capability is fine for it. -/
theorem deliver_ok {fb : Bool} {j : Nat} {u u' : Task} {m : Msg} {sender : Nat}
    (hu : TaskOK fb j u) (hg : ∀ g, m.grant = some g → CapOK j g)
    (hd : deliver u m sender = some u') : TaskOK fb j u' := by
  obtain ⟨hmaps, hst, hcaps⟩ := deliver_spec hd
  have hcap : ∀ c ∈ u'.caps, c ∈ u.caps ∨ CapOK j c := by
    intro c hc
    rcases hcaps with h | ⟨g, hg', h⟩
    · rw [h] at hc; exact Or.inl hc
    · rw [h] at hc
      rcases mem_snoc.1 hc with h1 | h1
      · exact Or.inl h1
      · subst h1; exact Or.inr (hg _ hg')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
        refine inv_setTask hs ⟨?_, ?_, ht.caps, ht.status, ?_⟩
        · intro m hm
          rcases mem_app.1 hm with hm | hm
          · obtain ⟨k, hk, -, hf', hr⟩ := mem_runMaps hm
            exact ⟨c, hcm, ⟨base, count, hf, by omega, by omega⟩, hr.symm⟩
          · exact ht.backed m (mem_dropRange hm)
        · intro m hm
          rcases mem_app.1 hm with hm | hm
          · obtain ⟨k, hk, hv, -, -⟩ := mem_runMaps hm
            omega
          · exact ht.vpnOk m (mem_dropRange hm)
        · intro m hm
          rcases mem_app.1 hm with hm | hm
          · obtain ⟨k, hk, -, hf', -⟩ := mem_runMaps hm
            rcases hcond.2 with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · exact Or.inl (by omega)
            · exact Or.inr (Or.inl ⟨h1, by omega⟩)
            · exact Or.inr (Or.inr (by omega))
          · exact ht.fbMaps m (mem_dropRange hm)
      · exact inv_ret hs ht _
    · exact inv_ret hs ht _

theorem inv_sysUnmap {s : KState} {t : Task} {vpn count : Nat} (hs : Inv s) (ht : TaskOK (fbSane s.fbBase) s.cur t) :
    Inv (sysUnmap s t vpn count).state :=
  inv_setTask hs ⟨fun m hm => ht.backed m (mem_dropRange hm),
    fun m hm => ht.vpnOk m (mem_dropRange hm), ht.caps, ht.status,
    fun m hm => ht.fbMaps m (mem_dropRange hm)⟩

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
        refine ⟨?_, ht.vpnOk, ?_, ht.status, ht.fbMaps⟩
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
    (hcur : nth? s.tasks s.cur = some t) : Inv (sysSend s t ci w0 w1 w2 gi call).state := by
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
            obtain ⟨-, u0, hu0, hst⟩ := findReceiver_spec hj
            simp only [Nat.sub_zero] at hu0
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
                  apply inv_setTask hs (deliver_ok huok ?_ hd)
                  intro g' hg'
                  obtain ⟨hgok, hgf, c2, hc2, ho2, hw2, hx2⟩ := hgr g' hg'
                  exact capOK_grant hgok hgf ⟨hA, hB, e, ⟨c2, hc2, ho2, hw2, hx2⟩, ⟨c1, hc1, ho1, hr1⟩⟩
                split
                · exact inv_schedule (inv_setTask hdel (ht.setStatus (.awaiting j) trivial _))
                · exact inv_ret hdel ht _
              · exact inv_ret hs ht _
            · exact inv_ret hs ht _
          · apply inv_schedule
            exact inv_setTask hs (ht.setStatus (.sending e ⟨c.badge, w0, w1, w2, g, call⟩)
              ⟨⟨c0, hc0, ho0, hle0.2.1 hw, hb0⟩, fun g' hg' => hgr g' hg'⟩ _)
      · exact inv_ret hs ht _

theorem inv_sysRecv {s : KState} {t : Task} {ci : Nat} (hs : Inv s)
    (hcur : nth? s.tasks s.cur = some t) : Inv (sysRecv s t ci).state := by
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
          obtain ⟨-, u0, hu0, hst⟩ := findSender_spec hj
          simp only [Nat.sub_zero] at hu0
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
                · exact inv_setTask hs (huok.setStatus (.awaiting s.cur) trivial _)
                · exact inv_setTask hs (huok.setStatus .ready trivial _)
              apply inv_setTask h1
              apply deliver_ok ht _ hd
              intro g hg
              obtain ⟨hgok, hgf, c2, hc2, ho2, hw2, hx2⟩ := hgrant g hg
              exact capOK_grant hgok hgf ⟨hA, hB, e, ⟨c2, hc2, ho2, hw2, hx2⟩,
                ⟨c0, hc0, ho0, hle0.1 hr⟩⟩
            · exact inv_ret hs ht _
          · exact inv_ret hs ht _
        · apply inv_schedule
          exact inv_setTask hs (ht.setStatus (.receiving e) ⟨c0, hc0, ho0, hle0.1 hr⟩ _)
      · exact inv_ret hs ht _

theorem TaskOK.setCallers {fb : Bool} {j : Nat} {t : Task} (h : TaskOK fb j t) (cs : List Nat) :
    TaskOK fb j { t with callers := cs } := ⟨h.backed, h.vpnOk, h.caps, h.status, h.fbMaps⟩

theorem inv_sysReply {s : KState} {t : Task} {slot w0 w1 w2 : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysReply s t slot w0 w1 w2).state := by
  unfold sysReply
  split
  · exact inv_ret hs ht _
  · rename_i j hj
    dsimp only
    split
    · split
      · rename_i u hu
        exact inv_ret (inv_setTask hs ((hs.tasks j u hu).setStatus .ready trivial _))
          (ht.setCallers _) _
      · exact inv_ret hs (ht.setCallers _) _
    · exact inv_ret hs (ht.setCallers _) _

theorem inv_sysIrqWait {s : KState} {t : Task} {ci : Nat} (hs : Inv s)
    (ht : TaskOK (fbSane s.fbBase) s.cur t) : Inv (sysIrqWait s t ci).state := by
  unfold sysIrqWait
  split
  · exact inv_ret hs ht _
  · rename_i c hc
    split
    · rename_i n hn
      split
      · exact inv_ret (s := { s with pending := dropLine n s.pending }) ⟨hs.len, hs.tasks⟩ ht _
      · apply inv_schedule
        obtain ⟨c0, hc0, ho⟩ := (ht.caps c (nth?_mem hc)).2.2 n hn
        exact inv_setTask hs (ht.setStatus (.waitingIrq n) ⟨c0, hc0, ho⟩ _)
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
      exact inv_setTask hs ((hs.tasks j u hu).setStatus .ready trivial _)
    · exact hs
  · split
    · exact hs
    · exact ⟨hs.len, hs.tasks⟩

theorem inv_syscall {s : KState} (hs : Inv s) (num a0 a1 a2 a3 a4 : Nat) :
    Inv (syscall s num a0 a1 a2 a3 a4).state := by
  unfold syscall
  split
  · exact hs
  · rename_i t ht
    have hto := hs.tasks _ _ ht
    split
    · exact inv_sysWrite hs hto
    · exact inv_schedule (inv_setTask hs (hto.result _))
    · exact inv_sysMap hs hto
    · exact inv_sysUnmap hs hto
    · exact inv_sysDerive hs hto
    · exact inv_killCurrent hs
    · exact inv_sysCapInfo hs hto
    · exact inv_ret hs hto _
    · exact inv_sysSend hs ht
    · exact inv_sysRecv hs ht
    · exact inv_sysSend hs ht
    · exact inv_sysReply hs hto
    · exact inv_sysIrqWait hs hto
    · exact inv_sysIrqAck hs hto
    · exact inv_ret hs hto _

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

theorem cases4 {j : Nat} (h : j < numTasks) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
  simp [numTasks] at h; omega

/-- At boot, every frame a task holds is its own (`owner`), read-execute or read-write. -/
theorem initCaps_frame {j f : Nat} {c : Cap} (hj : j < numTasks) (hc : c ∈ initCaps j)
    (hf : Covers c f) : owner f = j ∧ f < devBase + devPages ∧ ¬ WX c.rights := by
  obtain ⟨b, n, ho, h1, h2⟩ := hf
  rcases cases4 hj with rfl | rfl | rfl | rfl | rfl <;>
    simp [initCaps, frameCaps, snoc, runCap, epCap, irqCap] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at ho <;> obtain ⟨rfl, rfl⟩ := ho <;>
    by_cases hfp : f < 2048 <;> by_cases hfd : f < 2648 <;>
    simp [WX, Rights.rx, Rights.rw, owner, poolFrames, framesPerTask, maxTasks, fbPages,
      displayTask, inputTask, devBase, devPages, hfp, hfd] at h1 h2 ⊢ <;> omega

theorem initCap_ok {j : Nat} {c : Cap} (hj : j < numTasks) (hc : c ∈ initCaps j) : CapOK j c := by
  constructor
  · intro f hf
    have ⟨_, hlt, hwx⟩ := initCaps_frame hj hc hf
    exact ⟨hlt, hwx, j, c, hj, Reach.refl j, hc, hf, RLe.refl _⟩
  constructor
  · intro e he
    exact ⟨c, hc, he, RLe.refl _, rfl⟩
  · intro n hn
    exact ⟨c, hc, hn⟩

theorem mkTask_ok {fb : Bool} {j : Nat} (hj : j < numTasks) : TaskOK fb j (mkTask j) := by
  refine ⟨?_, ?_, fun c hc => initCap_ok hj hc, trivial, ?_⟩
  · intro m hm
    simp only [mkTask, initMaps] at hm
    have hcode : runCap (256 * j) 16 Rights.rx ∈ initCaps j := by
      rcases cases4 hj with rfl | rfl | rfl | rfl | rfl <;> simp [initCaps, frameCaps, snoc]
    have hdata : runCap (256 * j + 16) 8 Rights.rw ∈ initCaps j := by
      rcases cases4 hj with rfl | rfl | rfl | rfl | rfl <;> simp [initCaps, frameCaps, snoc]
    have hstack : runCap (256 * j + 24) 4 Rights.rw ∈ initCaps j := by
      rcases cases4 hj with rfl | rfl | rfl | rfl | rfl <;> simp [initCaps, frameCaps, snoc]
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
    have : j < 5 := by simpa [numTasks] using hj
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

/-! ## Reachable states -/

/-- The states the running kernel can be in: `init` (with whatever framebuffer address the
firmware returned), then any sequence of system calls,
timer ticks (`schedule`), faults (`killCurrent`), result loads (`clearResult`) and
interrupts (`irqFired`). -/
inductive Reachable : KState → Prop
  | init (fb : Nat) : Reachable (init fb)
  | syscall {s} (num a0 a1 a2 a3 a4 : Nat) : Reachable s →
      Reachable (syscall s num a0 a1 a2 a3 a4).state
  | tick {s} : Reachable s → Reachable (schedule s)
  | fault {s} : Reachable s → Reachable (killCurrent s)
  | clear {s} (j : Nat) : Reachable s → Reachable (clearResult s j)
  | irq {s} (n : Nat) : Reachable s → Reachable (irqFired s n)

theorem reachable_inv {s : KState} (h : Reachable s) : Inv s := by
  induction h with
  | init fb => exact inv_init fb
  | syscall num a0 a1 a2 a3 a4 _ ih => exact inv_syscall ih num a0 a1 a2 a3 a4
  | tick _ ih => exact inv_schedule ih
  | fault _ ih => exact inv_killCurrent ih
  | clear j _ ih => exact inv_clearResult ih j
  | irq n _ ih => exact inv_irqFired ih n

/-! ## The guarantees -/

/-- **Authority flow.** In every reachable state, a frame task `j` holds a capability to came
along a chain of grant edges from the task that owned it at boot (`owner f`: task `f / 64`
for the pool, the display server for the framebuffer), with no more rights than it had
at boot. -/
theorem frame_flow {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) :
    Reach (owner f) j ∧ ∃ c0 ∈ initCaps (owner f), Covers c0 f ∧ RLe c.rights c0.rights := by
  obtain ⟨-, -, A, c0, hA, hr, hc0, ho, hle⟩ :=
    ((reachable_inv h).tasks j t ht).caps c hc |>.1 f hf
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
  ((reachable_inv h).tasks j t ht).caps c hc |>.2.1 e he

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
  exact ((hto.caps c hc).1 _ hf).2.1

/-- Every mapping is in the user window and names a frame in the pool. -/
theorem maps_in_range {s : KState} (h : Reachable s) {i : Nat} {t : Task}
    (ht : nth? s.tasks i = some t) :
    ∀ m ∈ t.maps, m.vpn < userPages ∧ m.frame < devBase + devPages := by
  have hto := (reachable_inv h).tasks i t ht
  intro m hm
  obtain ⟨c, hc, hf, _⟩ := hto.backed m hm
  exact ⟨hto.vpnOk m hm, ((hto.caps c hc).1 _ hf).1⟩

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

theorem awaitsFrom_spec {ts : List Task} {j server : Nat} (h : awaitsFrom ts j server = true) :
    ∃ u, nth? ts j = some u ∧ u.status = .awaiting server := by
  unfold awaitsFrom at h
  split at h
  · rename_i u hu
    split at h
    · rename_i k hk; simp at h; subst h; exact ⟨u, hu, hk⟩
    · simp at h
  · simp at h

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
        simp only [ret, setTask, nth?_setNth, Ne.symm hj, if_false] at hu'
        by_cases hkj : k = j
        · subst hkj
          obtain ⟨w, hw, hst⟩ := awaitsFrom_spec haw
          rw [hw] at hu; cases hu; exact hst
        · simp [hkj, hu] at hu'; subst hu'; exact absurd rfl hch
      · simp [ret, setTask, nth?_setNth, Ne.symm hj, hu] at hu'; subst hu'; exact absurd rfl hch
    · simp [ret, setTask, nth?_setNth, Ne.symm hj, hu] at hu'; subst hu'; exact absurd rfl hch

/-! ## The demo manifest: who can reach whom -/

/-- The only grant edge in the manifest: alice (0) to the server (1). -/
theorem edge_iff {A B : Nat} : Edge A B ↔ A = 0 ∧ B = 1 := by
  constructor
  · rintro ⟨hA, hB, e, ⟨c, hc, hco, hw, hx⟩, ⟨d, hd, hdo, hr⟩⟩
    rcases cases4 hA with rfl | rfl | rfl | rfl | rfl <;>
      simp [initCaps, frameCaps, snoc, runCap, epCap, irqCap] at hc <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hco hw hx
    subst hco
    rcases cases4 hB with rfl | rfl | rfl | rfl | rfl <;>
      simp [initCaps, frameCaps, snoc, runCap, epCap, irqCap] at hd <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hdo hr
    simp
  · rintro ⟨rfl, rfl⟩
    refine ⟨by decide, by decide, 0, ⟨epCap 0 false true true 1, ?_, rfl, rfl, rfl⟩,
      ⟨epCap 0 true false false 0, ?_, rfl, rfl⟩⟩ <;>
      simp [initCaps, frameCaps, snoc, runCap]

theorem reach_iff {A B : Nat} (h : Reach A B) : A = B ∨ (A = 0 ∧ B = 1) := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ he ih =>
    obtain ⟨hB, hC⟩ := edge_iff.1 he
    subst hB; subst hC
    rcases ih with h | ⟨_, h⟩
    · exact Or.inr ⟨h, rfl⟩
    · cases h

/-- **mallory is confined.** Whatever happens, task 2 holds capabilities only to its own
frames (512 to 767), so it can never map, read or write anyone else's memory. -/
theorem mallory_confined {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 2 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 2 := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨_, h⟩
  · exact h
  · cases h

/-- carol (task 3) holds capabilities only to her own frames (768 to 1023). -/
theorem carol_confined {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 3 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 3 := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨_, h⟩
  · exact h
  · cases h

/-- alice (task 0) is never given anyone's memory: she only ever holds her own frames. -/
theorem alice_confined {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 0 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 0 := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨_, h⟩
  · exact h
  · cases h

/-- The display server (task 1) holds only its own frames, the framebuffer, and frames alice
granted it. -/
theorem server_frames {s : KState} (h : Reachable s) {t : Task} (ht : nth? s.tasks 1 = some t)
    {c : Cap} (hc : c ∈ t.caps) {f : Nat} (hf : Covers c f) : owner f = 1 ∨ owner f = 0 := by
  rcases reach_iff (frame_flow h ht hc hf).1 with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-! ## Interrupts and devices -/

/-- Interrupt capabilities never move: a task holds one only if it held it at boot. -/
theorem irqs_fixed {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) {n : Nat} (hn : c.obj = .irq n) :
    ∃ c0 ∈ initCaps j, c0.obj = .irq n :=
  ((reachable_inv h).tasks j t ht).caps c hc |>.2.2 n hn

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
      simp only [setTask, nth?_setNth] at hu'
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
  have hj := (reachable_inv h).lt ht
  rcases cases4 hj with rfl | rfl | rfl | rfl | rfl <;>
    simp [initCaps, frameCaps, snoc, runCap, epCap, irqCap] at hc0 <;>
    rcases hc0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at ho <;> rfl

/-- **The UART belongs to the input driver.** No other task can ever hold a capability to
the UART's registers. -/
theorem uart_confined {s : KState} (h : Reachable s) {j : Nat} {t : Task}
    (ht : nth? s.tasks j = some t) {c : Cap} (hc : c ∈ t.caps) (hf : Covers c devBase) :
    j = inputTask := by
  have hr := (frame_flow h ht hc hf).1
  have : owner devBase = inputTask := by decide
  rw [this] at hr
  rcases reach_iff hr with h1 | ⟨h0, _⟩
  · exact h1.symm
  · cases h0

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
    · rfl
    all_goals exfalso
    all_goals first
      | (simp at h; done)
      | (unfold sysMap at h; repeat' split at h
         all_goals simp at h
         done)
      | (unfold sysUnmap at h; simp at h; done)
      | (unfold sysDerive at h; repeat' split at h
         all_goals simp at h
         done)
      | (unfold sysCapInfo at h; repeat' split at h
         all_goals simp at h
         done)
      | (unfold sysSend at h; repeat' (first | split at h | dsimp only at h)
         all_goals simp at h
         done)
      | (unfold sysRecv at h; repeat' (first | split at h | dsimp only at h)
         all_goals simp at h
         done)
      | (unfold sysReply at h; repeat' (first | split at h | dsimp only at h)
         all_goals simp at h
         done)
      | (unfold sysIrqWait at h; repeat' split at h
         all_goals simp at h
         done)
      | (unfold sysIrqAck at h; repeat' split at h
         all_goals simp at h
         done)

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

/-! ## Scheduling -/

theorem findReady_ready : ∀ {ts : List Task} {i fuel j : Nat},
    findReady ts i fuel = some j → isReady ts j = true
  | ts, i, 0, j, h => by simp [findReady] at h
  | ts, i, fuel + 1, j, h => by
    simp only [findReady] at h
    split at h
    · simp at h; subst h; assumption
    · exact findReady_ready h

/-- If the search finds nothing, none of the `fuel` tasks it looked at is ready. -/
theorem findReady_none : ∀ {ts : List Task} {i fuel : Nat},
    findReady ts i fuel = none → ∀ k < fuel, isReady ts ((i + k) % len ts) = false
  | ts, i, 0, _, k, hk => by omega
  | ts, i, fuel + 1, h, k, hk => by
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

/-- **The scheduler never runs a waiting or stopped task while a ready one exists.** -/
theorem schedule_picks_ready (s : KState) (h : ∃ i, isReady s.tasks i = true) :
    isReady (schedule s).tasks (schedule s).cur = true := by
  obtain ⟨i, hi⟩ := h
  unfold schedule
  split
  · rename_i j hj
    exact findReady_ready hj
  · rename_i hnone
    obtain ⟨k, hk, hkj⟩ := hits_every (s.cur + 1) i (len s.tasks) (isReady_lt hi)
    have := findReady_none hnone k hk
    rw [hkj, hi] at this
    exact absurd this (by simp)

end LeanOS
