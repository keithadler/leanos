import LeanOS.Proofs
import LeanOS.Arm

/-!
# The hardware tables give user mode exactly its mappings

The theorem `walk_eq_view`: if the machine layer stores the words the kernel computes
(`l1Word`, `l2Word`, `l3Word`) in three page-aligned tables, then for every virtual
address the MMU's answer for EL0, as modelled in `LeanOS/Arm.lean`, is exactly
`el0View`: nothing outside the 2 MiB user window, and inside it the frame and rights the
task's mapping names, or nothing.

Combined with `isolation`, this means user code cannot touch the kernel, the peripherals,
or another task's frames. The hypotheses are exactly what `build_user_pages` and
`tables_init` in `arch/kmain.c` do, so the page-table encoding is no longer trusted C.
-/

namespace LeanOS

/-- What a task's address space should look like from user mode: the user window, page
by page, from its mappings; nothing anywhere else. -/
def el0View (s : KState) (i va : Nat) : Option (Nat × Arm.Perm) :=
  if userBase ≤ va ∧ va < userBase + userPages * pageSize then
    match findVpn (mapsOf s i) ((va - userBase) / pageSize) with
    | some m =>
      if m.rights.r then some (framePA m.frame + va % pageSize, ⟨m.rights.r, m.rights.w, m.rights.x⟩)
      else none
    | none => none
  else none

/-! ## The number of tasks never changes -/

theorem len_withTask (s : KState) (t : Task) : len (withTask s t).tasks = len s.tasks := by
  simp [withTask, len_setNth]

theorem len_schedule (s : KState) : len (schedule s).tasks = len s.tasks := by
  unfold schedule; split <;> rfl

theorem len_killCurrent (s : KState) : len (killCurrent s).tasks = len s.tasks := by
  unfold killCurrent; split <;> simp [len_schedule, len_setNth]

theorem len_syscall (s : KState) (num a0 a1 : Nat) :
    len (syscall s num a0 a1).state.tasks = len s.tasks := by
  unfold syscall
  split
  · rfl
  · split
    · rw [sysWrite_state]
    · exact len_schedule s
    · unfold sysMap; split
      · rfl
      · split
        · exact len_withTask _ _
        · rfl
    · exact len_withTask _ _
    · unfold sysDerive; split
      · rfl
      · split
        · exact len_withTask _ _
        · rfl
    · exact len_killCurrent s
    · unfold sysCapInfo; split <;> rfl
    · rfl
    · rfl

theorem len_mkTasksFrom' (k n : Nat) : len (mkTasksFrom k n) = n := len_mkTasksFrom k n

theorem reachable_len {s : KState} (h : Reachable s) : len s.tasks ≤ maxTasks := by
  induction h with
  | init n =>
    simp only [init, len_mkTasksFrom']
    split
    · assumption
    · exact Nat.le_refl _
  | syscall num a0 a1 _ ih => rw [len_syscall]; exact ih
  | tick _ ih => rw [len_schedule]; exact ih
  | fault _ ih => rw [len_killCurrent]; exact ih

/-- In a reachable state every mapped frame is inside the pool of `4 * maxTasks` frames. -/
theorem reachable_frames {s : KState} (h : Reachable s) (i : Nat) :
    ∀ m ∈ mapsOf s i, m.frame < 4 * maxTasks := by
  intro m hm
  unfold mapsOf at hm
  split at hm
  · rename_i t ht
    have := (maps_in_range h ht m hm).2
    have := reachable_len h
    omega
  · simp at hm

theorem findVpn_mem : ∀ {ms : List Mapping} {v : Nat} {m : Mapping},
    findVpn ms v = some m → m ∈ ms ∧ m.vpn = v
  | [], _, _, h => by simp [findVpn] at h
  | x :: ms, v, m, h => by
    simp only [findVpn] at h
    split at h
    · rename_i hx; simp at h; subst h; exact ⟨List.mem_cons_self .., by simpa using hx⟩
    · have := findVpn_mem h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-! ## Reading the descriptors back -/

/-- The descriptor for a readable mapping, with its two choices spelled out. -/
theorem pageDesc_read (m : Mapping) (hr : m.rights.r = true) :
    pageDesc m = 67108864 + m.frame * 4096 + 3 + 4 + (if m.rights.w then 64 else 192) + 768 +
      1024 + 2048 + 9007199254740992 + (if m.rights.x then 0 else 18014398509481984) := by
  simp only [pageDesc, hr, if_true, framePA, frameBase, pageSize, dValid, dTableOrPage,
    attrNormal, apUserRW, apUserRO, shInner, accessFlag, notGlobal, privNoExec, userNoExec]
  all_goals omega

/-- Every field of such a descriptor, for either choice of AP (`a`) and UXN (`u`). -/
theorem desc_fields (f a u : Nat) (hf : f < 16) (ha : a = 64 ∨ a = 192)
    (hu : u = 0 ∨ u = 18014398509481984) :
    Arm.field (67108864 + f * 4096 + 3 + 4 + a + 768 + 1024 + 2048 + 9007199254740992 + u) 0 2 = 3 ∧
    Arm.field (67108864 + f * 4096 + 3 + 4 + a + 768 + 1024 + 2048 + 9007199254740992 + u) 10 1 = 1 ∧
    Arm.field (67108864 + f * 4096 + 3 + 4 + a + 768 + 1024 + 2048 + 9007199254740992 + u) 6 2 =
      a / 64 ∧
    Arm.field (67108864 + f * 4096 + 3 + 4 + a + 768 + 1024 + 2048 + 9007199254740992 + u) 54 1 =
      u / 18014398509481984 ∧
    Arm.outAddr (67108864 + f * 4096 + 3 + 4 + a + 768 + 1024 + 2048 + 9007199254740992 + u) 12 =
      67108864 + f * 4096 := by
  simp only [Arm.field, Arm.outAddr, Nat.reducePow, Nat.reduceSub]
  omega

/-- A readable page descriptor, read back field by field. -/
theorem leaf_pageDesc (m : Mapping) (hr : m.rights.r = true) (hf : m.frame < 16) (va : Nat) :
    Arm.field (pageDesc m) 0 2 = 3 ∧
    Arm.leaf (pageDesc m) 12 va =
      some (framePA m.frame + va % pageSize, ⟨true, m.rights.w, m.rights.x⟩) := by
  rw [pageDesc_read m hr]
  obtain ⟨hty, haf, hap, hux, hout⟩ := desc_fields m.frame (if m.rights.w then 64 else 192)
    (if m.rights.x then 0 else 18014398509481984) hf (by split <;> simp) (by split <;> simp)
  refine ⟨hty, ?_⟩
  unfold Arm.leaf
  rw [haf, hap, hux, hout]
  cases m.rights.w <;> cases m.rights.x <;> simp [framePA, frameBase, pageSize]

/-! ## The walk -/

/-- **The MMU gives user mode exactly its mappings.** If the machine layer has stored the
kernel's words in three page-aligned tables at physical addresses `l1`, `l2`, `l3` (below
2^48), then the EL0 translation of every virtual address `va` is `el0View`. -/
theorem walk_eq_view {s : KState} (h : Reachable s) (i : Nat)
    (mem : Arm.Mem) (l1 l2 l3 : Nat)
    (hl2 : l2 % 4096 = 0) (hl3 : l3 % 4096 = 0) (hl2' : l2 < 2 ^ 48) (hl3' : l3 < 2 ^ 48)
    (h1 : ∀ k < 512, mem (l1 + 8 * k) = l1Word l2 k)
    (h2 : ∀ k < 512, mem (l2 + 8 * k) = l2Word l3 k)
    (h3 : ∀ k < 512, mem (l3 + 8 * k) = l3Word s i k)
    (va : Nat) : Arm.walkEL0 mem l1 va = el0View s i va := by
  have hfr := reachable_frames h i
  unfold Arm.walkEL0 el0View
  by_cases hva : 2 ^ 39 ≤ va
  · have : ¬ (userBase ≤ va ∧ va < userBase + userPages * pageSize) := by
      simp [userBase, userPages, pageSize] at hva ⊢; omega
    simp [hva, this]
  simp only [hva, if_false]
  have hk1 : Arm.field va 30 9 < 512 := by simp [Arm.field]; omega
  rw [h1 _ hk1]
  by_cases h2k : Arm.field va 30 9 = 2
  · -- the user window's gigabyte: go through the level-2 table
    have hd1 : l1Word l2 (Arm.field va 30 9) = l2 + 3 := by
      simp [l1Word, h2k, dValid, dTableOrPage]
    rw [hd1]
    have ht1 : Arm.field (l2 + 3) 0 2 = 3 := by simp [Arm.field]; omega
    have ho1 : Arm.outAddr (l2 + 3) 12 = l2 := by simp [Arm.outAddr, Arm.field]; omega
    simp only [ht1, ho1]
    simp only [show (3 : Nat) = 1 ↔ False by decide, if_false, if_true]
    have hk2 : Arm.field va 21 9 < 512 := by simp [Arm.field]; omega
    rw [h2 _ hk2]
    by_cases h0 : Arm.field va 21 9 = 0
    · have hd2 : l2Word l3 (Arm.field va 21 9) = l3 + 3 := by
        simp [l2Word, h0, dValid, dTableOrPage]
      rw [hd2]
      have ht2 : Arm.field (l3 + 3) 0 2 = 3 := by simp [Arm.field]; omega
      have ho2 : Arm.outAddr (l3 + 3) 12 = l3 := by simp [Arm.outAddr, Arm.field]; omega
      simp only [ht2, ho2]
      simp only [show (3 : Nat) = 1 ↔ False by decide, if_false, if_true]
      have hk3 : Arm.field va 12 9 < 512 := by simp [Arm.field]; omega
      rw [h3 _ hk3]
      -- inside the window, and the page index is the level-3 index
      have hin : userBase ≤ va ∧ va < userBase + userPages * pageSize := by
        simp [Arm.field] at h2k h0; simp [userBase, userPages, pageSize]; omega
      have hvpn : (va - userBase) / pageSize = Arm.field va 12 9 := by
        simp [Arm.field] at h2k h0 ⊢; simp [userBase, pageSize]; omega
      simp only [hin, and_self, if_true, hvpn]
      unfold l3Word
      split
      · rename_i m hm
        have hmem := (findVpn_mem hm).1
        have hf : m.frame < 16 := by have := hfr m hmem; simp [maxTasks] at this; omega
        by_cases hr : m.rights.r = true
        · obtain ⟨hty, hleaf⟩ := leaf_pageDesc m hr hf va
          rw [hm]
          simp [hty, hleaf, hr, pageSize]
        · have : pageDesc m = 0 := by simp [pageDesc, hr]
          rw [hm]
          simp [this, hr, Arm.field]
      · rename_i hm
        rw [hm]
        simp [Arm.field]
    · -- the rest of that gigabyte: level-2 entries other than 0 are empty
      have hd2 : l2Word l3 (Arm.field va 21 9) = 0 := by simp [l2Word, h0]
      have hout : ¬ (userBase ≤ va ∧ va < userBase + userPages * pageSize) := by
        simp [Arm.field] at h2k h0; simp [userBase, userPages, pageSize]; omega
      rw [hd2]
      simp [hout, Arm.field]
  · -- every other gigabyte holds only kernel entries, which user mode cannot use
    have hout : ¬ (userBase ≤ va ∧ va < userBase + userPages * pageSize) := by
      simp [Arm.field] at h2k; simp [userBase, userPages, pageSize]; omega
    simp only [hout, if_false]
    have hd1 : l1Word l2 (Arm.field va 30 9) = kernelL1Word (Arm.field va 30 9) := by
      simp [l1Word, h2k]
    rw [hd1]
    unfold kernelL1Word
    by_cases hz : Arm.field va 30 9 = 0
    · simp only [hz, if_true]
      simp [Arm.leaf, Arm.field, dValid, attrNormal, shInner, accessFlag, userNoExec]
    · by_cases h3k : Arm.field va 30 9 = 3
      · simp only [h3k, hz, if_true, if_false, show (3 : Nat) = 0 ↔ False by decide]
        simp [Arm.leaf, Arm.field, dValid, attrDevice, accessFlag, privNoExec, userNoExec]
      · simp only [hz, h3k, if_false]
        simp [Arm.field]

/-! ## Consequences -/

/-- Anything user mode can reach comes from one of the task's own mappings. -/
theorem el0View_some {s : KState} {i va pa : Nat} {p : Arm.Perm}
    (hv : el0View s i va = some (pa, p)) :
    ∃ t m, nth? s.tasks i = some t ∧ m ∈ t.maps ∧ m.rights.r = true ∧
      pa = framePA m.frame + va % pageSize ∧ p = ⟨m.rights.r, m.rights.w, m.rights.x⟩ := by
  unfold el0View at hv
  split at hv
  · split at hv
    · rename_i m hm
      split at hv
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        unfold mapsOf at hm
        split at hm
        · rename_i t ht
          exact ⟨t, m, ht, (findVpn_mem hm).1, hr, rfl, rfl⟩
        · simp [findVpn] at hm
      · simp at hv
    · simp at hv
  · simp at hv

/-- The hypotheses under which the machine layer's tables for task `i` are the kernel's:
three page-aligned tables at `l1`, `l2`, `l3` holding exactly the computed words. -/
structure Installed (s : KState) (i : Nat) (mem : Arm.Mem) (l1 l2 l3 : Nat) : Prop where
  l2_aligned : l2 % 4096 = 0
  l3_aligned : l3 % 4096 = 0
  l2_lt : l2 < 2 ^ 48
  l3_lt : l3 < 2 ^ 48
  l1_words : ∀ k < 512, mem (l1 + 8 * k) = l1Word l2 k
  l2_words : ∀ k < 512, mem (l2 + 8 * k) = l2Word l3 k
  l3_words : ∀ k < 512, mem (l3 + 8 * k) = l3Word s i k

theorem Installed.walk {s : KState} {i : Nat} {mem : Arm.Mem} {l1 l2 l3 : Nat}
    (h : Reachable s) (hi : Installed s i mem l1 l2 l3) (va : Nat) :
    Arm.walkEL0 mem l1 va = el0View s i va :=
  walk_eq_view h i mem l1 l2 l3 hi.l2_aligned hi.l3_aligned hi.l2_lt hi.l3_lt
    hi.l1_words hi.l2_words hi.l3_words va

/-- User mode can only ever reach physical addresses inside the frame pool: never the
kernel image, its heap, its tables, or the peripherals, which all lie outside it. -/
theorem el0_only_frame_pool {s : KState} (h : Reachable s) {i : Nat} {mem : Arm.Mem}
    {l1 l2 l3 : Nat} (hi : Installed s i mem l1 l2 l3)
    {va pa : Nat} {p : Arm.Perm} (hw : Arm.walkEL0 mem l1 va = some (pa, p)) :
    frameBase ≤ pa ∧ pa < frameBase + 4 * maxTasks * pageSize := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, rfl, -⟩ := el0View_some hw
  have := (maps_in_range h ht m hm).2
  have := reachable_len h
  have : va % pageSize < pageSize := Nat.mod_lt _ (by decide)
  simp [framePA, maxTasks, pageSize] at *
  omega

/-- No address user mode can reach is both writable and executable. -/
theorem el0_no_write_execute {s : KState} (h : Reachable s) {i : Nat} {mem : Arm.Mem}
    {l1 l2 l3 : Nat} (hi : Installed s i mem l1 l2 l3)
    {va pa : Nat} {p : Arm.Perm} (hw : Arm.walkEL0 mem l1 va = some (pa, p)) :
    ¬ (p.w = true ∧ p.x = true) := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, -, rfl⟩ := el0View_some hw
  exact no_write_execute h ht m hm

/-- **Isolation, down to the hardware.** Two different tasks never reach the same physical
page from user mode. -/
theorem el0_isolation {s : KState} (h : Reachable s) {i j : Nat} (hij : i ≠ j)
    {mem mem' : Arm.Mem} {l1 l2 l3 l1' l2' l3' : Nat}
    (hi : Installed s i mem l1 l2 l3) (hj : Installed s j mem' l1' l2' l3')
    {va va' pa pa' : Nat} {p p' : Arm.Perm}
    (hw : Arm.walkEL0 mem l1 va = some (pa, p)) (hw' : Arm.walkEL0 mem' l1' va' = some (pa', p')) :
    pa / pageSize ≠ pa' / pageSize := by
  rw [hi.walk h] at hw
  rw [hj.walk h] at hw'
  obtain ⟨t, m, ht, hm, -, rfl, -⟩ := el0View_some hw
  obtain ⟨u, m', hu, hm', -, rfl, -⟩ := el0View_some hw'
  have hne := isolation h hij ht hu m hm m' hm'
  have e : ∀ f v, (framePA f + v % pageSize) / pageSize = frameBase / pageSize + f := by
    intro f v
    have : v % pageSize < pageSize := Nat.mod_lt _ (by decide)
    simp [framePA, frameBase, pageSize] at *; omega
  rw [e, e]; omega

end LeanOS
