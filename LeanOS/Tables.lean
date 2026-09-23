import LeanOS.Proofs
import LeanOS.Arm

/-!
# The hardware tables give user mode exactly its mappings

The theorem `walk_eq_view`: if the machine layer stores the words the kernel computes
(`l1Word`, `l2Word`, `l3Word`) in three page-aligned tables, then for every virtual
address the MMU's answer for EL0, as modelled in `LeanOS/Arm.lean`, is exactly
`el0View`: nothing outside the 32 MiB user window, and inside it the frame and rights the
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

/-- In a reachable state every mapped frame is inside the pool. -/
theorem reachable_frames {s : KState} (h : Reachable s) (i : Nat) :
    ∀ m ∈ mapsOf s i, m.frame < poolFrames := by
  intro m hm
  unfold mapsOf at hm
  split at hm
  · rename_i t ht
    exact (maps_in_range h ht m hm).2
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
theorem desc_fields (f a u : Nat) (hf : f < 512) (ha : a = 64 ∨ a = 192)
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
theorem leaf_pageDesc (m : Mapping) (hr : m.rights.r = true) (hf : m.frame < 512) (va : Nat) :
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
kernel's words in its page-aligned tables at physical addresses `l1`, `l2` and `l3` onward
(below 2^47), then the EL0 translation of every virtual address `va` is `el0View`. -/
theorem walk_eq_view {s : KState} (h : Reachable s) (i : Nat)
    (mem : Arm.Mem) (l1 l2 l3 : Nat)
    (hl2 : l2 % 4096 = 0) (hl3 : l3 % 4096 = 0) (hl2' : l2 < 2 ^ 47) (hl3' : l3 < 2 ^ 47)
    (h1 : ∀ k < 512, mem (l1 + 8 * k) = l1Word l2 k)
    (h2 : ∀ k < 512, mem (l2 + 8 * k) = l2Word l3 k)
    (h3 : ∀ k < userPages, mem (l3 + 8 * k) = l3Word s i k)
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
    by_cases h0 : Arm.field va 21 9 < l3Tables
    · -- one of the 16 level-3 tables
      have hd2 : l2Word l3 (Arm.field va 21 9) = l3 + Arm.field va 21 9 * 4096 + 3 := by
        simp [l2Word, h0, dValid, dTableOrPage, pageSize]
      rw [hd2]
      have h16 : Arm.field va 21 9 < 16 := by simpa [l3Tables] using h0
      have ht2 : Arm.field (l3 + Arm.field va 21 9 * 4096 + 3) 0 2 = 3 := by
        simp only [Arm.field] at h16 ⊢; simp; omega
      have ho2 : Arm.outAddr (l3 + Arm.field va 21 9 * 4096 + 3) 12 =
          l3 + Arm.field va 21 9 * 4096 := by
        simp only [Arm.outAddr, Arm.field] at h16 ⊢; simp; omega
      simp only [ht2, ho2]
      simp only [show (3 : Nat) = 1 ↔ False by decide, if_false, if_true]
      have hk3 : Arm.field va 12 9 < 512 := by simp [Arm.field]; omega
      -- the level-3 entry is entry `vpn` of the task's 8192-word array
      have hidx : Arm.field va 21 9 * 512 + Arm.field va 12 9 < userPages := by
        simp [userPages]; omega
      have haddr : l3 + Arm.field va 21 9 * 4096 + 8 * Arm.field va 12 9 =
          l3 + 8 * (Arm.field va 21 9 * 512 + Arm.field va 12 9) := by omega
      rw [haddr, h3 _ hidx]
      have hin : userBase ≤ va ∧ va < userBase + userPages * pageSize := by
        simp [Arm.field] at h2k h16; simp [userBase, userPages, pageSize]; omega
      have hvpn : (va - userBase) / pageSize = Arm.field va 21 9 * 512 + Arm.field va 12 9 := by
        simp [Arm.field] at h2k h16 ⊢; simp [userBase, pageSize]; omega
      simp only [hin, and_self, if_true, hvpn]
      unfold l3Word
      split
      · rename_i m hm
        have hmem := (findVpn_mem hm).1
        have hf : m.frame < 512 := by
          have := hfr m hmem; simp [poolFrames, framesPerTask, maxTasks] at this; omega
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
    · -- the rest of that gigabyte: level-2 entries past the 16 tables are empty
      have hd2 : l2Word l3 (Arm.field va 21 9) = 0 := by simp [l2Word, h0]
      have hout : ¬ (userBase ≤ va ∧ va < userBase + userPages * pageSize) := by
        simp [Arm.field, l3Tables] at h2k h0; simp [userBase, userPages, pageSize]; omega
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
      · simp only [h3k, if_true, if_false, show (3 : Nat) = 0 ↔ False by decide]
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

/-- The hypotheses under which the machine layer's tables for task `i` are the kernel's: a
level-1 and a level-2 table at `l1` and `l2`, and the 16 level-3 tables one after another
from `l3`, all page-aligned and holding exactly the computed words. -/
structure Installed (s : KState) (i : Nat) (mem : Arm.Mem) (l1 l2 l3 : Nat) : Prop where
  l2_aligned : l2 % 4096 = 0
  l3_aligned : l3 % 4096 = 0
  l2_lt : l2 < 2 ^ 47
  l3_lt : l3 < 2 ^ 47
  l1_words : ∀ k < 512, mem (l1 + 8 * k) = l1Word l2 k
  l2_words : ∀ k < 512, mem (l2 + 8 * k) = l2Word l3 k
  l3_words : ∀ k < userPages, mem (l3 + 8 * k) = l3Word s i k

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
    frameBase ≤ pa ∧ pa < frameBase + poolFrames * pageSize := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, rfl, -⟩ := el0View_some hw
  have := (maps_in_range h ht m hm).2
  have : va % pageSize < pageSize := Nat.mod_lt _ (by decide)
  simp [framePA, poolFrames, maxTasks, pageSize] at *
  omega

/-- No address user mode can reach is both writable and executable. -/
theorem el0_no_write_execute {s : KState} (h : Reachable s) {i : Nat} {mem : Arm.Mem}
    {l1 l2 l3 : Nat} (hi : Installed s i mem l1 l2 l3)
    {va pa : Nat} {p : Arm.Perm} (hw : Arm.walkEL0 mem l1 va = some (pa, p)) :
    ¬ (p.w = true ∧ p.x = true) := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, -, rfl⟩ := el0View_some hw
  exact no_write_execute h ht m hm

/-- The physical page user mode reaches is the frame's page. -/
theorem framePA_page (f v : Nat) :
    (framePA f + v % pageSize) / pageSize = frameBase / pageSize + f := by
  have : v % pageSize < pageSize := Nat.mod_lt _ (by decide)
  simp [framePA, frameBase, pageSize] at *; omega

/-- **Authority flow, down to the hardware.** If task `i`'s user mode can reach a physical
page, the task that owned that page at boot can pass frames to `i` along grant edges. -/
theorem el0_flow {s : KState} (h : Reachable s) {i : Nat} {mem : Arm.Mem}
    {l1 l2 l3 : Nat} (hi : Installed s i mem l1 l2 l3)
    {va pa : Nat} {p : Arm.Perm} (hw : Arm.walkEL0 mem l1 va = some (pa, p)) :
    Reach ((pa / pageSize - frameBase / pageSize) / 64) i := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, rfl, -⟩ := el0View_some hw
  rw [framePA_page, Nat.add_sub_cancel_left]
  exact mapping_flow h ht hm

/-- **Shared pages need a grant path.** Two different tasks reach the same physical page only
if the page's owner at boot can reach both of them. In the demo manifest that means only
alice and the server, only on alice's pages. -/
theorem el0_shared {s : KState} (h : Reachable s) {i j : Nat}
    {mem mem' : Arm.Mem} {l1 l2 l3 l1' l2' l3' : Nat}
    (hi : Installed s i mem l1 l2 l3) (hj : Installed s j mem' l1' l2' l3')
    {va va' pa pa' : Nat} {p p' : Arm.Perm}
    (hw : Arm.walkEL0 mem l1 va = some (pa, p)) (hw' : Arm.walkEL0 mem' l1' va' = some (pa', p'))
    (hsame : pa / pageSize = pa' / pageSize) :
    ∃ A, Reach A i ∧ Reach A j := by
  have ha := el0_flow h hi hw
  have hb := el0_flow h hj hw'
  rw [hsame] at ha
  exact ⟨_, ha, hb⟩

/-- mallory's user mode never reaches a physical page any other task can reach. -/
theorem el0_mallory_isolated {s : KState} (h : Reachable s) {j : Nat} (hj2 : j ≠ 2)
    {mem mem' : Arm.Mem} {l1 l2 l3 l1' l2' l3' : Nat}
    (hi : Installed s 2 mem l1 l2 l3) (hj : Installed s j mem' l1' l2' l3')
    {va va' pa pa' : Nat} {p p' : Arm.Perm}
    (hw : Arm.walkEL0 mem l1 va = some (pa, p)) (hw' : Arm.walkEL0 mem' l1' va' = some (pa', p')) :
    pa / pageSize ≠ pa' / pageSize := by
  intro hsame
  obtain ⟨A, ha, hb⟩ := el0_shared h hi hj hw hw' hsame
  rcases reach_iff ha with rfl | ⟨_, h2⟩
  · rcases reach_iff hb with h3 | ⟨h0, h1⟩
    · exact hj2 h3.symm
    · cases h0
  · cases h2

end LeanOS
