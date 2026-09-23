import LeanOS.Kernel

/-!
# What is proved about the kernel

Every theorem here is about the definitions in `LeanOS/Kernel.lean`, the same definitions
compiled into the running kernel. The states considered are all the states the kernel can
reach: start from `init n`, then apply any sequence of system calls (with any arguments),
timer ticks and faults.

For every reachable state:

* `isolation`: no physical frame appears in two different tasks' address spaces.
* `caps_isolated`: no two tasks hold capabilities to the same frame.
* `maps_backed`: every page a task can see is backed by a capability it holds, with the
  same rights.
* `no_write_execute`: no page is ever both writable and executable.
* `maps_in_range`: every mapping has a page number inside the user window and a frame
  number inside the frame pool, so the machine layer's bounds checks never fire.

About single steps:

* `derive_never_amplifies`: a derived capability names the same frame as its parent and
  allows nothing its parent does not.
* `write_reads_only_readable`: when a `write` asks the machine layer to print user memory,
  every byte lies in a page the calling task has mapped readable.
* `schedule_picks_alive`: if any task is alive, the scheduler picks a live task.

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

/-! ## The invariant -/

/-- What holds of every reachable state. -/
structure Inv (s : KState) : Prop where
  /-- No two tasks hold capabilities to the same frame. -/
  disjoint : ∀ i j t u, i ≠ j → nth? s.tasks i = some t → nth? s.tasks j = some u →
    ∀ c ∈ t.caps, ∀ d ∈ u.caps, c.frame ≠ d.frame
  /-- Every mapping is backed by one of the task's own capabilities, with its rights. -/
  backed : ∀ i t, nth? s.tasks i = some t →
    ∀ m ∈ t.maps, ∃ c ∈ t.caps, c.frame = m.frame ∧ c.rights = m.rights
  /-- No capability is both writable and executable. -/
  noWX : ∀ i t, nth? s.tasks i = some t → ∀ c ∈ t.caps, ¬ WX c.rights
  /-- Page numbers stay in the user window. -/
  vpnOk : ∀ i t, nth? s.tasks i = some t → ∀ m ∈ t.maps, m.vpn < userPages
  /-- Frame numbers stay in the pool: four frames per task. -/
  frameOk : ∀ i t, nth? s.tasks i = some t → ∀ c ∈ t.caps, c.frame < 4 * len s.tasks

/-- The new version `t'` of a task `t` only has capabilities that some capability of `t`
already covered: same frame, no more rights. -/
def CapsSub (t' t : Task) : Prop :=
  ∀ c' ∈ t'.caps, ∃ c ∈ t.caps, c.frame = c'.frame ∧ RLe c'.rights c.rights

/-- The invariant survives replacing the current task by `t'`, as long as `t'` gains no
frame and no right, backs its mappings, and keeps them in the window. Every system call
that changes a task goes through this. -/
theorem inv_withTask {s : KState} {t t' : Task} (hs : Inv s)
    (ht : nth? s.tasks s.cur = some t) (hsub : CapsSub t' t)
    (hback : ∀ m ∈ t'.maps, ∃ c ∈ t'.caps, c.frame = m.frame ∧ c.rights = m.rights)
    (hvpn : ∀ m ∈ t'.maps, m.vpn < userPages) : Inv (withTask s t') := by
  -- Any task of the new state is either `t'` at `s.cur`, or an old task somewhere else.
  have look : ∀ j b, nth? (withTask s t').tasks j = some b →
      (s.cur = j ∧ b = t') ∨ (s.cur ≠ j ∧ nth? s.tasks j = some b) := by
    intro j b h
    simp only [withTask, nth?_setNth] at h
    by_cases hj : s.cur = j
    · subst hj; simp [ht] at h; exact Or.inl ⟨rfl, h.symm⟩
    · simp [hj] at h; exact Or.inr ⟨hj, h⟩
  have hlen : len (withTask s t').tasks = len s.tasks := by simp [withTask, len_setNth]
  constructor
  · intro i j a b hij ha hb c hc d hd
    rcases look i a ha with ⟨hi, ha'⟩ | ⟨_, ha'⟩
    · rcases look j b hb with ⟨hj, _⟩ | ⟨_, hb'⟩
      · exact absurd (hi.symm.trans hj) hij
      · subst ha'
        obtain ⟨c0, hc0, hf, _⟩ := hsub c hc
        rw [← hf]; subst hi
        exact hs.disjoint _ j t b hij ht hb' c0 hc0 d hd
    · rcases look j b hb with ⟨hj, hb'⟩ | ⟨_, hb'⟩
      · subst hb'
        obtain ⟨d0, hd0, hf, _⟩ := hsub d hd
        rw [← hf]; subst hj
        exact hs.disjoint i _ a t hij ha' ht c hc d0 hd0
      · exact hs.disjoint i j a b hij ha' hb' c hc d hd
  · intro i a ha m hm
    rcases look i a ha with ⟨_, ha⟩ | ⟨_, ha⟩
    · subst ha; exact hback m hm
    · exact hs.backed i a ha m hm
  · intro i a ha c hc
    rcases look i a ha with ⟨_, ha⟩ | ⟨_, ha⟩
    · subst ha
      obtain ⟨c0, hc0, _, hle⟩ := hsub c hc
      exact not_wx_of_le hle (hs.noWX _ t ht c0 hc0)
    · exact hs.noWX i a ha c hc
  · intro i a ha m hm
    rcases look i a ha with ⟨_, ha⟩ | ⟨_, ha⟩
    · subst ha; exact hvpn m hm
    · exact hs.vpnOk i a ha m hm
  · intro i a ha c hc
    rw [hlen]
    rcases look i a ha with ⟨_, ha⟩ | ⟨_, ha⟩
    · subst ha
      obtain ⟨c0, hc0, hf, _⟩ := hsub c hc
      rw [← hf]; exact hs.frameOk _ t ht c0 hc0
    · exact hs.frameOk i a ha c hc

/-- Choosing another task changes nothing the invariant talks about. -/
theorem inv_schedule {s : KState} (hs : Inv s) : Inv (schedule s) := by
  unfold schedule
  split
  · exact ⟨hs.disjoint, hs.backed, hs.noWX, hs.vpnOk, hs.frameOk⟩
  · exact hs

theorem inv_killCurrent {s : KState} (hs : Inv s) : Inv (killCurrent s) := by
  unfold killCurrent
  split
  · rename_i t ht
    apply inv_schedule
    exact inv_withTask (t' := { t with alive := false }) hs ht
      (fun c hc => ⟨c, hc, rfl, RLe.refl _⟩)
      (fun m hm => hs.backed _ t ht m hm)
      (fun m hm => hs.vpnOk _ t ht m hm)
  · exact inv_schedule hs

/-! ## System calls preserve the invariant -/

theorem inv_sysMap {s : KState} {t : Task} {ci vpn : Nat} (hs : Inv s)
    (ht : nth? s.tasks s.cur = some t) : Inv (sysMap s t ci vpn).state := by
  unfold sysMap
  split
  · exact hs
  · rename_i c hc
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have hcm := nth?_mem hc
      refine inv_withTask hs ht (fun c' hc' => ⟨c', hc', rfl, RLe.refl _⟩) ?_ ?_
      · intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with hm | hm
        · subst hm; exact ⟨c, hcm, rfl, rfl⟩
        · exact hs.backed _ t ht m (mem_dropVpn hm).1
      · intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with hm | hm
        · subst hm; exact hcond.1
        · exact hs.vpnOk _ t ht m (mem_dropVpn hm).1
    · exact hs

theorem inv_sysUnmap {s : KState} {t : Task} {vpn : Nat} (hs : Inv s)
    (ht : nth? s.tasks s.cur = some t) : Inv (sysUnmap s t vpn).state := by
  unfold sysUnmap okRemap
  exact inv_withTask hs ht (fun c' hc' => ⟨c', hc', rfl, RLe.refl _⟩)
    (fun m hm => hs.backed _ t ht m (mem_dropVpn hm).1)
    (fun m hm => hs.vpnOk _ t ht m (mem_dropVpn hm).1)

theorem inv_sysDerive {s : KState} {t : Task} {ci bits : Nat} (hs : Inv s)
    (ht : nth? s.tasks s.cur = some t) : Inv (sysDerive s t ci bits).state := by
  unfold sysDerive
  split
  · exact hs
  · rename_i c hc
    split
    · refine inv_withTask hs ht ?_ ?_ ?_
      · intro c' hc'
        rcases mem_snoc.1 hc' with h | h
        · exact ⟨c', h, rfl, RLe.refl _⟩
        · subst h; exact ⟨c, nth?_mem hc, rfl, meet_le _ _⟩
      · intro m hm
        obtain ⟨c0, hc0, h1, h2⟩ := hs.backed _ t ht m hm
        exact ⟨c0, mem_snoc.2 (Or.inl hc0), h1, h2⟩
      · exact hs.vpnOk _ t ht
    · exact hs

/-- `write` never changes the state. -/
theorem sysWrite_state (s : KState) (t : Task) (va n : Nat) : (sysWrite s t va n).state = s := by
  unfold sysWrite
  split
  · rfl
  · split <;> rfl

theorem inv_sysWrite {s : KState} {t : Task} {va n : Nat} (hs : Inv s) :
    Inv (sysWrite s t va n).state := by
  rw [sysWrite_state]; exact hs

theorem inv_syscall {s : KState} (hs : Inv s) (num a0 a1 : Nat) :
    Inv (syscall s num a0 a1).state := by
  unfold syscall
  split
  · exact hs
  · rename_i t ht
    split
    · exact inv_sysWrite hs
    · exact inv_schedule hs
    · exact inv_sysMap hs ht
    · exact inv_sysUnmap hs ht
    · exact inv_sysDerive hs ht
    · exact inv_killCurrent hs
    · unfold sysCapInfo; split <;> exact hs
    · exact hs
    · exact hs

/-! ## The initial state satisfies the invariant -/

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

/-- Task `i` starts out holding frames `4i` to `4i+3` and nothing else. -/
theorem mkTask_caps {i : Nat} {c : Cap} (h : c ∈ (mkTask i).caps) :
    4 * i ≤ c.frame ∧ c.frame < 4 * i + 4 := by
  simp [mkTask] at h
  rcases h with h | h | h | h <;> subst h <;> simp <;> omega

/-- The invariant holds for `N` fresh tasks, for any `N`. -/
theorem inv_fresh (N : Nat) : Inv ⟨mkTasksFrom 0 N, 0⟩ := by
  have look : ∀ i t, nth? (mkTasksFrom 0 N) i = some t → i < N ∧ t = mkTask i := by
    intro i t h
    simp only [nth?_mkTasksFrom, Nat.zero_add] at h
    split at h
    · simp at h; exact ⟨by assumption, h.symm⟩
    · simp at h
  constructor
  · intro i j a b hij ha hb c hc d hd
    obtain ⟨_, rfl⟩ := look i a ha
    obtain ⟨_, rfl⟩ := look j b hb
    have h1 := mkTask_caps hc
    have h2 := mkTask_caps hd
    omega
  · intro i t ht m hm
    obtain ⟨_, rfl⟩ := look i t ht
    simp [mkTask] at hm
    rcases hm with h | h | h <;> subst h <;> simp [mkTask]
  · intro i t ht c hc
    obtain ⟨_, rfl⟩ := look i t ht
    simp [mkTask] at hc
    rcases hc with h | h | h | h <;> subst h <;> simp [WX, Rights.rx, Rights.rw]
  · intro i t ht m hm
    obtain ⟨_, rfl⟩ := look i t ht
    simp [mkTask] at hm
    rcases hm with h | h | h <;> subst h <;> simp [userPages]
  · intro i t ht c hc
    obtain ⟨hi, rfl⟩ := look i t ht
    have := mkTask_caps hc
    simp only [len_mkTasksFrom]
    omega

theorem inv_init (n : Nat) : Inv (init n) := inv_fresh _

/-! ## Reachable states -/

/-- The states the running kernel can be in: the machine layer only ever calls `init`
once, then `syscall`, `schedule` (timer ticks) and `killCurrent` (faults). -/
inductive Reachable : KState → Prop
  | init (n : Nat) : Reachable (init n)
  | syscall {s} (num a0 a1 : Nat) : Reachable s → Reachable (syscall s num a0 a1).state
  | tick {s} : Reachable s → Reachable (schedule s)
  | fault {s} : Reachable s → Reachable (killCurrent s)

theorem reachable_inv {s : KState} (h : Reachable s) : Inv s := by
  induction h with
  | init n => exact inv_init n
  | syscall num a0 a1 _ ih => exact inv_syscall ih num a0 a1
  | tick _ ih => exact inv_schedule ih
  | fault _ ih => exact inv_killCurrent ih

/-! ## The guarantees -/

/-- **Isolation.** In every reachable state, no physical frame is visible in the address
spaces of two different tasks. -/
theorem isolation {s : KState} (h : Reachable s) {i j : Nat} {t u : Task} (hij : i ≠ j)
    (ht : nth? s.tasks i = some t) (hu : nth? s.tasks j = some u) :
    ∀ m ∈ t.maps, ∀ m' ∈ u.maps, m.frame ≠ m'.frame := by
  have hs := reachable_inv h
  intro m hm m' hm'
  obtain ⟨c, hc, hcf, _⟩ := hs.backed i t ht m hm
  obtain ⟨d, hd, hdf, _⟩ := hs.backed j u hu m' hm'
  rw [← hcf, ← hdf]
  exact hs.disjoint i j t u hij ht hu c hc d hd

theorem caps_isolated {s : KState} (h : Reachable s) {i j : Nat} {t u : Task} (hij : i ≠ j)
    (ht : nth? s.tasks i = some t) (hu : nth? s.tasks j = some u) :
    ∀ c ∈ t.caps, ∀ d ∈ u.caps, c.frame ≠ d.frame :=
  (reachable_inv h).disjoint i j t u hij ht hu

theorem maps_backed {s : KState} (h : Reachable s) {i : Nat} {t : Task}
    (ht : nth? s.tasks i = some t) :
    ∀ m ∈ t.maps, ∃ c ∈ t.caps, c.frame = m.frame ∧ c.rights = m.rights :=
  (reachable_inv h).backed i t ht

/-- **W^X.** No page of any task is ever both writable and executable. -/
theorem no_write_execute {s : KState} (h : Reachable s) {i : Nat} {t : Task}
    (ht : nth? s.tasks i = some t) : ∀ m ∈ t.maps, ¬ (m.rights.w = true ∧ m.rights.x = true) := by
  have hs := reachable_inv h
  intro m hm
  obtain ⟨c, hc, _, hr⟩ := hs.backed i t ht m hm
  rw [← hr]
  exact hs.noWX i t ht c hc

/-- The machine layer's page-table bounds checks (`vpn < 512`, `frame < NFRAMES`) never fire
for a machine with at most `MAX_TASKS` tasks. -/
theorem maps_in_range {s : KState} (h : Reachable s) {i : Nat} {t : Task}
    (ht : nth? s.tasks i = some t) :
    ∀ m ∈ t.maps, m.vpn < userPages ∧ m.frame < 4 * len s.tasks := by
  have hs := reachable_inv h
  intro m hm
  obtain ⟨c, hc, hf, _⟩ := hs.backed i t ht m hm
  exact ⟨hs.vpnOk i t ht m hm, hf ▸ hs.frameOk i t ht c hc⟩

/-- **No amplification.** A derived capability names its parent's frame and allows nothing
the parent does not. -/
theorem derive_never_amplifies (c : Cap) (bits : Nat) :
    let d : Cap := ⟨c.frame, c.rights.meet (Rights.ofBits bits)⟩
    d.frame = c.frame ∧ RLe d.rights c.rights :=
  ⟨rfl, meet_le _ _⟩

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

@[simp] theorem okR_outLen (s : KState) (v : Nat) : (okR s v).outLen = 0 := rfl
@[simp] theorem errR_outLen (s : KState) (c : Nat) : (errR s c).outLen = 0 := rfl
@[simp] theorem okRemap_outLen (s : KState) : (okRemap s).outLen = 0 := rfl
@[simp] theorem okSwitch_outLen (s : KState) : (okSwitch s).outLen = 0 := rfl

/-- The only system call that asks the machine layer to print is `write`. -/
theorem outLen_pos {s : KState} {num a0 a1 : Nat} (h : 0 < (syscall s num a0 a1).outLen) :
    ∃ t, nth? s.tasks s.cur = some t ∧ syscall s num a0 a1 = sysWrite s t a0 a1 := by
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
      | (unfold sysMap at h; split at h <;> (try split at h) <;> simp at h; done)
      | (unfold sysUnmap at h; simp at h; done)
      | (unfold sysDerive at h; split at h <;> (try split at h) <;> simp at h; done)
      | (unfold sysCapInfo at h; split at h <;> simp at h; done)

/-- When a system call asks the machine layer to print user memory, every byte of it is in
the user window, in a page the calling task has mapped with read rights. -/
theorem write_reads_only_readable (s : KState) (num a0 a1 : Nat)
    (hout : 0 < (syscall s num a0 a1).outLen) :
    ∃ t, nth? s.tasks s.cur = some t ∧
      ∀ a, (syscall s num a0 a1).outVa ≤ a →
        a < (syscall s num a0 a1).outVa + (syscall s num a0 a1).outLen →
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
      simp only [okPrint] at ha1 ha2
      refine ⟨by omega, readableAt_spec (allReadable_spec hall ?_ ?_)⟩
      · exact Nat.div_le_div_right (by omega)
      · have : (a - userBase) / pageSize ≤ (a0 + a1 - 1 - userBase) / pageSize :=
          Nat.div_le_div_right (by omega)
        omega
    · intro a h1 h2; simp at h2; omega

/-! ## Scheduling -/

theorem findAlive_alive : ∀ {ts : List Task} {i fuel j : Nat},
    findAlive ts i fuel = some j → isAlive ts j = true
  | ts, i, 0, j, h => by simp [findAlive] at h
  | ts, i, fuel + 1, j, h => by
    simp only [findAlive] at h
    split at h
    · simp at h; subst h; assumption
    · exact findAlive_alive h

/-- If the search finds nothing, none of the `fuel` tasks it looked at is alive. -/
theorem findAlive_none : ∀ {ts : List Task} {i fuel : Nat},
    findAlive ts i fuel = none → ∀ k < fuel, isAlive ts ((i + k) % len ts) = false
  | ts, i, 0, _, k, hk => by omega
  | ts, i, fuel + 1, h, k, hk => by
    simp only [findAlive] at h
    split at h
    · simp at h
    · rename_i hnot
      cases k with
      | zero => simpa using hnot
      | succ k =>
        have := findAlive_none h k (by omega)
        rwa [Nat.add_assoc, Nat.mod_add_mod, Nat.add_comm 1 k] at this

theorem isAlive_lt {ts : List Task} {j : Nat} (h : isAlive ts j = true) : j < len ts := by
  unfold isAlive at h
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

/-- **The scheduler never picks a stopped task while a live one exists.** -/
theorem schedule_picks_alive (s : KState) (h : ∃ i, isAlive s.tasks i = true) :
    isAlive (schedule s).tasks (schedule s).cur = true := by
  obtain ⟨i, hi⟩ := h
  unfold schedule
  split
  · rename_i j hj
    exact findAlive_alive hj
  · rename_i hnone
    obtain ⟨k, hk, hkj⟩ := hits_every (s.cur + 1) i (len s.tasks) (isAlive_lt hi)
    have := findAlive_none hnone k hk
    rw [hkj, hi] at this
    exact absurd this (by simp)

end LeanOS
