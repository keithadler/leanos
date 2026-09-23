import LeanOS.Proofs
import LeanOS.Arm

/-!
# The hardware tables give user mode exactly its mappings

The theorem `walk_eq_view`: if the machine layer stores the words the kernel computes
(`l1Word`, `l2Word`, `l3Word`) in its page-aligned tables, then for every virtual
address the MMU's answer for EL0, as modelled in `LeanOS/Arm.lean`, is exactly
`el0View`: nothing outside the 32 MiB user window, and inside it the frame and rights the
task's mapping names, or nothing.

Combined with the authority-flow theorems, this means user code cannot touch the kernel or
the peripherals, and reaches another task's memory only along grant edges. The hypotheses are exactly what `build_user_pages` and
`tables_init` in `arch/kmain.c` do, so the page-table encoding is no longer trusted C.
-/

namespace LeanOS

/-- What a task's address space should look like from user mode: the user window, page
by page, from its mappings; nothing anywhere else. -/
def el0View (s : KState) (i va : Nat) : Option (Nat × Arm.Perm) :=
  if userBase ≤ va ∧ va < userBase + userPages * pageSize then
    match findVpn (mapsOf s i) ((va - userBase) / pageSize) with
    | some m =>
      if m.rights.r then some (physOf s m.frame + va % pageSize, ⟨m.rights.r, m.rights.w, m.rights.x⟩)
      else none
    | none => none
  else none

/-- In a reachable state every mapped frame is in the pool, or in the framebuffer and the
framebuffer is sane. -/
theorem reachable_frames {s : KState} (h : Reachable s) (i : Nat) :
    ∀ m ∈ mapsOf s i, m.frame < poolFrames ∨ (fbSane s.fbBase = true ∧ m.frame < poolFrames + fbPages) := by
  intro m hm
  unfold mapsOf at hm
  split at hm
  · rename_i t ht
    rcases ((reachable_inv h).tasks i t ht).fbMaps m hm with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1, (maps_in_range h ht m hm).2⟩
  · simp at hm

theorem physOf_pool {s : KState} {f : Nat} (hf : f < poolFrames) :
    physOf s f = 67108864 + f * 4096 := by
  unfold physOf; rw [if_pos hf]; rfl

theorem physOf_fb {s : KState} {f : Nat} (hf : ¬ f < poolFrames) :
    physOf s f = s.fbBase + (f - 512) * 4096 := by
  unfold physOf; rw [if_neg hf]; rfl

theorem fbSane_spec {b : Nat} (h : fbSane b = true) :
    b % 4096 = 0 ∧ 69206016 ≤ b ∧ b + 1228800 ≤ 68719476736 := by
  unfold fbSane at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  simp only [pageSize, frameBase, poolFrames, framesPerTask, maxTasks, fbPages] at h
  omega

theorem poolFrames_eq : poolFrames = 512 := rfl
theorem fbPages_eq : fbPages = 300 := rfl

/-- The physical address of a frame that may be mapped: page-aligned and below 2^36. -/
theorem physOf_ok {s : KState} {f : Nat}
    (hf : f < poolFrames ∨ (fbSane s.fbBase = true ∧ f < poolFrames + fbPages)) :
    physOf s f % 4096 = 0 ∧ physOf s f + 4096 ≤ 2 ^ 36 := by
  simp only [Nat.reducePow]
  by_cases hp : f < poolFrames
  · rw [physOf_pool hp]; rw [poolFrames_eq] at hp; omega
  · rw [physOf_fb hp]
    rcases hf with hf | ⟨hs, hf⟩
    · exact absurd hf hp
    · have := fbSane_spec hs
      simp only [poolFrames_eq, fbPages_eq] at hf hp
      omega

theorem findVpn_mem : ∀ {ms : List Mapping} {v : Nat} {m : Mapping},
    findVpn ms v = some m → m ∈ ms ∧ m.vpn = v
  | [], _, _, h => by simp [findVpn] at h
  | x :: ms, v, m, h => by
    simp only [findVpn] at h
    split at h
    · rename_i hx; simp at h; subst h; exact ⟨List.mem_cons_self .., by simpa using hx⟩
    · have := findVpn_mem h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-! ## Reading the descriptors back -/

/-- The descriptor for a readable mapping, with its choices spelled out. -/
theorem pageDesc_read (s : KState) (m : Mapping) (hr : m.rights.r = true) :
    pageDesc s m = physOf s m.frame + 3 + (if m.frame < poolFrames then 4 else 8) +
      (if m.rights.w then 64 else 192) + 768 + 1024 + 2048 + 9007199254740992 +
      (if m.rights.x then 0 else 18014398509481984) := by
  simp only [pageDesc, hr, if_true, dValid, dTableOrPage, attrNormal, attrNoCache, apUserRW,
    apUserRO, shInner, accessFlag, notGlobal, privNoExec, userNoExec]
  all_goals omega

/-- Every field of such a descriptor, for any page-aligned address `P` below 2^36 and any
choice of memory type (`a`), AP (`w`) and UXN (`u`). -/
theorem desc_fields (P a w u : Nat) (hP : P % 4096 = 0) (hlt : P + 4096 ≤ 2 ^ 36)
    (ha : a = 4 ∨ a = 8) (hw : w = 64 ∨ w = 192) (hu : u = 0 ∨ u = 18014398509481984) :
    Arm.field (P + 3 + a + w + 768 + 1024 + 2048 + 9007199254740992 + u) 0 2 = 3 ∧
    Arm.field (P + 3 + a + w + 768 + 1024 + 2048 + 9007199254740992 + u) 10 1 = 1 ∧
    Arm.field (P + 3 + a + w + 768 + 1024 + 2048 + 9007199254740992 + u) 6 2 = w / 64 ∧
    Arm.field (P + 3 + a + w + 768 + 1024 + 2048 + 9007199254740992 + u) 54 1 =
      u / 18014398509481984 ∧
    Arm.outAddr (P + 3 + a + w + 768 + 1024 + 2048 + 9007199254740992 + u) 12 = P := by
  simp only [Arm.field, Arm.outAddr, Nat.reducePow, Nat.reduceSub]
  omega

/-- A readable page descriptor, read back field by field. -/
theorem leaf_pageDesc (s : KState) (m : Mapping) (hr : m.rights.r = true)
    (hf : m.frame < poolFrames ∨ (fbSane s.fbBase = true ∧ m.frame < poolFrames + fbPages))
    (va : Nat) :
    Arm.field (pageDesc s m) 0 2 = 3 ∧
    Arm.leaf (pageDesc s m) 12 va =
      some (physOf s m.frame + va % pageSize, ⟨true, m.rights.w, m.rights.x⟩) := by
  rw [pageDesc_read s m hr]
  obtain ⟨hal, hlt⟩ := physOf_ok hf
  obtain ⟨hty, haf, hap, hux, hout⟩ := desc_fields (physOf s m.frame)
    (if m.frame < poolFrames then 4 else 8) (if m.rights.w then 64 else 192)
    (if m.rights.x then 0 else 18014398509481984) hal hlt
    (by split <;> simp) (by split <;> simp) (by split <;> simp)
  refine ⟨hty, ?_⟩
  unfold Arm.leaf
  rw [haf, hap, hux, hout]
  cases m.rights.w <;> cases m.rights.x <;> simp [pageSize]

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
        have hf := hfr m hmem
        by_cases hr : m.rights.r = true
        · obtain ⟨hty, hleaf⟩ := leaf_pageDesc s m hr hf va
          rw [hm]
          simp [hty, hleaf, hr, pageSize]
        · have : pageDesc s m = 0 := by simp [pageDesc, hr]
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
      pa = physOf s m.frame + va % pageSize ∧ p = ⟨m.rights.r, m.rights.w, m.rights.x⟩ := by
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

/-- User mode can only ever reach physical addresses inside the frame pool or, if the
firmware gave a sane one, the framebuffer: never the kernel image, its heap, its tables,
or the peripherals. -/
theorem el0_only_pool_or_fb {s : KState} (h : Reachable s) {i : Nat} {mem : Arm.Mem}
    {l1 l2 l3 : Nat} (hi : Installed s i mem l1 l2 l3)
    {va pa : Nat} {p : Arm.Perm} (hw : Arm.walkEL0 mem l1 va = some (pa, p)) :
    (frameBase ≤ pa ∧ pa < frameBase + poolFrames * pageSize) ∨
    (fbSane s.fbBase = true ∧ s.fbBase ≤ pa ∧ pa < s.fbBase + fbPages * pageSize) := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, rfl, -⟩ := el0View_some hw
  have hmm : m ∈ mapsOf s i := by simp [mapsOf, ht]; exact hm
  have hva : va % 4096 < 4096 := Nat.mod_lt _ (by decide)
  simp only [frameBase, pageSize, poolFrames_eq, fbPages_eq]
  by_cases hp : m.frame < poolFrames
  · left; rw [physOf_pool hp]; rw [poolFrames_eq] at hp; omega
  · rcases reachable_frames h i m hmm with hf | ⟨hs, hf⟩
    · exact absurd hf hp
    · right; refine ⟨hs, ?_⟩
      have := fbSane_spec hs
      rw [physOf_fb hp]; simp only [poolFrames_eq, fbPages_eq] at hf hp; omega

/-- No address user mode can reach is both writable and executable. -/
theorem el0_no_write_execute {s : KState} (h : Reachable s) {i : Nat} {mem : Arm.Mem}
    {l1 l2 l3 : Nat} (hi : Installed s i mem l1 l2 l3)
    {va pa : Nat} {p : Arm.Perm} (hw : Arm.walkEL0 mem l1 va = some (pa, p)) :
    ¬ (p.w = true ∧ p.x = true) := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, -, rfl⟩ := el0View_some hw
  exact no_write_execute h ht m hm

/-- **Authority flow, down to the hardware.** If task `i`'s user mode can reach a physical
address, it lies in a frame whose owner at boot can pass frames to `i` along grant edges. -/
theorem el0_flow {s : KState} (h : Reachable s) {i : Nat} {mem : Arm.Mem}
    {l1 l2 l3 : Nat} (hi : Installed s i mem l1 l2 l3)
    {va pa : Nat} {p : Arm.Perm} (hw : Arm.walkEL0 mem l1 va = some (pa, p)) :
    ∃ f, (f < poolFrames ∨ (fbSane s.fbBase = true ∧ f < poolFrames + fbPages)) ∧
      pa / pageSize = physOf s f / pageSize ∧ Reach (owner f) i := by
  rw [hi.walk h] at hw
  obtain ⟨t, m, ht, hm, -, rfl, -⟩ := el0View_some hw
  have hmm : m ∈ mapsOf s i := by simp [mapsOf, ht]; exact hm
  refine ⟨m.frame, reachable_frames h i m hmm, ?_, mapping_flow h ht hm⟩
  have := (physOf_ok (reachable_frames h i m hmm)).1
  have : va % 4096 < 4096 := Nat.mod_lt _ (by decide)
  simp only [pageSize]; omega

/-- Different frames that may be mapped live in different physical pages: the framebuffer
lies past the pool, so the two never overlap. -/
theorem physOf_inj {s : KState} {f g : Nat}
    (hf : f < poolFrames ∨ (fbSane s.fbBase = true ∧ f < poolFrames + fbPages))
    (hg : g < poolFrames ∨ (fbSane s.fbBase = true ∧ g < poolFrames + fbPages))
    (h : physOf s f / pageSize = physOf s g / pageSize) : f = g := by
  simp only [pageSize] at h
  by_cases hfp : f < poolFrames <;> by_cases hgp : g < poolFrames
  · rw [physOf_pool hfp, physOf_pool hgp] at h; omega
  · rw [physOf_pool hfp, physOf_fb hgp] at h
    rcases hg with hg | ⟨hs, _⟩
    · exact absurd hg hgp
    · have := fbSane_spec hs; simp only [poolFrames_eq] at hfp hgp; omega
  · rw [physOf_fb hfp, physOf_pool hgp] at h
    rcases hf with hf | ⟨hs, _⟩
    · exact absurd hf hfp
    · have := fbSane_spec hs; simp only [poolFrames_eq] at hfp hgp; omega
  · rw [physOf_fb hfp, physOf_fb hgp] at h
    rcases hf with hf | ⟨hs, _⟩
    · exact absurd hf hfp
    · have := fbSane_spec hs; simp only [poolFrames_eq] at hfp hgp; omega

/-- **Shared pages need a grant path.** Two tasks reach the same physical page only if that
page's owner at boot can reach both of them. -/
theorem el0_shared {s : KState} (h : Reachable s) {i j : Nat}
    {mem mem' : Arm.Mem} {l1 l2 l3 l1' l2' l3' : Nat}
    (hi : Installed s i mem l1 l2 l3) (hj : Installed s j mem' l1' l2' l3')
    {va va' pa pa' : Nat} {p p' : Arm.Perm}
    (hw : Arm.walkEL0 mem l1 va = some (pa, p)) (hw' : Arm.walkEL0 mem' l1' va' = some (pa', p'))
    (hsame : pa / pageSize = pa' / pageSize) :
    ∃ A, Reach A i ∧ Reach A j := by
  obtain ⟨f, hf, hpf, hri⟩ := el0_flow h hi hw
  obtain ⟨g, hg, hpg, hrj⟩ := el0_flow h hj hw'
  have : f = g := physOf_inj hf hg (by rw [← hpf, ← hpg, hsame])
  subst this
  exact ⟨_, hri, hrj⟩

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
