/-
The proof that the journal (LeanOS/JournalModel.lean, the model of user/fs.c's) never
leaves a change half done: `crash_atomic`.
-/
import LeanOS.JournalModel

namespace LeanOS.Journal

/-! ## Lemmas about writes -/

theorem applyW_append (ws vs : List (Nat × Blk)) (d : Disk) :
    applyW (ws ++ vs) d = applyW vs (applyW ws d) := by
  induction ws generalizing d with
  | nil => rfl
  | cons w ws ih => obtain ⟨b, v⟩ := w; simp [applyW, ih]

/-- A block no write touches keeps its value. -/
theorem applyW_other : ∀ (ws : List (Nat × Blk)) (d : Disk) (x : Nat),
    (∀ p ∈ ws, p.1 ≠ x) → applyW ws d x = d x
  | .nil, _, _, _ => rfl
  | (b, v) :: ws, d, x, h => by
    simp only [applyW]
    rw [applyW_other ws _ x (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    have : b ≠ x := h (b, v) List.mem_cons_self
    simp [upd, Ne.symm this]

/-- After a list of writes, a block holds the last write to it, whatever it held before:
so applying all of `t` over a disk that differs only where `t` writes gives the same. -/
theorem applyW_congr : ∀ (ws : List (Nat × Blk)) (a b : Disk) (x : Nat),
    ((∃ p ∈ ws, p.1 = x) ∨ a x = b x) → applyW ws a x = applyW ws b x
  | .nil, a, b, x, h => by
    rcases h with ⟨p, hp, _⟩ | h
    · simp at hp
    · exact h
  | (c, v) :: ws, a, b, x, h => by
    simp only [applyW]
    apply applyW_congr ws
    by_cases hc : c = x
    · subst hc; right; simp [upd]
    · rcases h with ⟨p, hp, hpx⟩ | h
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact absurd hpx hc
        · exact Or.inl ⟨p, hp, hpx⟩
      · right; simp [upd, Ne.symm hc, h]

theorem applyW_take_then_all (t : List (Nat × Blk)) (m : Nat) (d : Disk) (x : Nat) :
    applyW t (applyW (t.take m) d) x = applyW t d x := by
  apply applyW_congr
  by_cases h : ∃ p ∈ t, p.1 = x
  · exact Or.inl h
  · right
    apply applyW_other
    intro p hp hpx
    exact h ⟨p, List.mem_of_mem_take hp, hpx⟩

theorem mem_jw : ∀ {J i : Nat} {vs : List Blk} {p : Nat × Blk}, p ∈ jw J i vs → J + 1 + i ≤ p.1
  | _, _, .nil, _, h => by simp [jw] at h
  | J, i, v :: vs, p, h => by
    simp only [jw, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · have := mem_jw h; omega

theorem length_jw : ∀ (J i : Nat) (vs : List Blk), (jw J i vs).length = vs.length
  | _, _, .nil => rfl
  | J, i, _ :: vs => by simp [jw, length_jw J (i + 1) vs]

theorem mem_jw_lt : ∀ {J i : Nat} {vs : List Blk} {p : Nat × Blk}, p ∈ jw J i vs → p.1 < J + 1 + i + vs.length
  | _, _, .nil, _, h => by simp [jw] at h
  | J, i, v :: vs, p, h => by
    simp only [jw, List.mem_cons] at h
    rcases h with rfl | h
    · simp only [List.length_cons]; omega
    · have := mem_jw_lt h; simp only [List.length_cons] at this ⊢; omega

/-- The journal's copies, read back after all of them are written (and anything written
outside the journal since): exactly the transaction's contents. -/
theorem readJ_jw : ∀ (J i : Nat) (vs : List Blk) (d : Disk),
    readJ (applyW (jw J i vs) d) J i vs.length = vs
  | _, _, .nil, _ => rfl
  | J, i, v :: vs, d => by
    simp only [jw, applyW, List.length_cons, readJ]
    congr 1
    · rw [applyW_other]
      · simp [upd]
      · intro p hp; have := mem_jw hp; omega
    · exact readJ_jw J (i + 1) vs (upd d (J + 1 + i) v)

theorem readJ_congr : ∀ (J i n : Nat) (a b : Disk), (∀ k, i ≤ k → k < i + n → a (J + 1 + k) = b (J + 1 + k)) →
    readJ a J i n = readJ b J i n
  | _, _, 0, _, _, _ => rfl
  | J, i, n + 1, a, b, h => by
    simp only [readJ]
    rw [h i (Nat.le_refl _) (by omega), readJ_congr J (i + 1) n a b (fun k h1 h2 => h k (by omega) (by omega))]

theorem zip_map (t : List (Nat × Blk)) : (t.map Prod.fst).zip (t.map Prod.snd) = t := by
  induction t with
  | nil => rfl
  | cons p t ih => obtain ⟨a, b⟩ := p; simp [ih]

theorem upd_home {J L : Nat} {d : Disk} {v : Blk} {x : Nat} (hx : x < J ∨ J + L < x) : upd d J v x = d x := by
  have : x ≠ J := by omega
  simp [upd, this]

/-! ## What recovery does -/

theorem recover_clean (csum : List Blk → Nat) (J : Nat) (d : Disk) (h : d J = clean) :
    recover csum J d = upd d J clean := by
  unfold recover; rw [h]; simp [clean]

theorem recover_commit (csum : List Blk → Nat) (J : Nat) (d : Disk) {n : Nat} {ts : List Nat} {s : Nat}
    (h : d J = .header n ts s) (hc : n ≠ 0 ∧ ts.length = n ∧ csum (readJ d J 0 n) = s) :
    recover csum J d = upd (applyW (ts.zip (readJ d J 0 n)) d) J clean := by
  unfold recover; rw [h]; exact if_pos hc

theorem recover_nothing (csum : List Blk → Nat) (J : Nat) (d : Disk) {ts : List Nat} {s : Nat}
    (h : d J = .header 0 ts s) : recover csum J d = upd d J clean := by
  unfold recover; rw [h]; exact if_neg (fun hc => hc.1 rfl)

/-! ## The theorem -/

/-- **A power cut cannot leave a change half done.** For a transaction whose targets lie
outside the journal (blocks `J` to `J + L`, with room for it), on a disk whose journal is
clean: cut the protocol after any number of writes `k`, recover, and every block outside
the journal holds what it held before the transaction, or what it holds after it. -/
theorem crash_atomic (csum : List Blk → Nat) (J L : Nat) (t : List (Nat × Blk)) (d : Disk)
    (hclean : d J = clean) (hroom : t.length ≤ L)
    (hout : ∀ p ∈ t, p.1 < J ∨ J + L < p.1) (k : Nat) :
    HomeEq J L (recover csum J (applyW ((protocol csum J t).take k) d)) d ∨
    HomeEq J L (recover csum J (applyW ((protocol csum J t).take k) d)) (applyW t d) := by
  have hlen : (jw J 0 (t.map Prod.snd)).length = t.length := by simp [length_jw]
  have hjw_in : ∀ p ∈ jw J 0 (t.map Prod.snd), J < p.1 ∧ p.1 ≤ J + L := by
    intro p hp
    have a := mem_jw hp
    have b := mem_jw_lt hp
    simp only [List.length_map] at b
    constructor <;> omega
  have hP : protocol csum J t = jw J 0 (t.map Prod.snd) ++
      (J, .header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) :: (t ++ (J, clean) :: .nil) := rfl
  -- the disk just after the commit
  have hjwJ : applyW (jw J 0 (t.map Prod.snd)) d J = clean := by
    rw [applyW_other _ _ _ (fun p hp => by have := (hjw_in p hp).1; omega)]; exact hclean
  by_cases hk1 : k ≤ t.length
  · -- the cut came while the journal was being written: the header is still clean
    left
    rw [hP, List.take_append_of_le_length (by omega)]
    have hJ : applyW ((jw J 0 (t.map Prod.snd)).take k) d J = clean := by
      rw [applyW_other _ _ _ (fun p hp => by have := (hjw_in p (List.mem_of_mem_take hp)).1; omega)]
      exact hclean
    rw [recover_clean _ _ _ hJ]
    intro x hx
    rw [upd_home hx, applyW_other]
    intro p hp; have := hjw_in p (List.mem_of_mem_take hp); omega
  · right
    -- d1: the journal written and committed
    have hd1J : upd (applyW (jw J 0 (t.map Prod.snd)) d) J
        (.header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) J =
        .header t.length (t.map Prod.fst) (csum (t.map Prod.snd)) := by simp [upd]
    have hd1read : readJ (upd (applyW (jw J 0 (t.map Prod.snd)) d) J
        (.header t.length (t.map Prod.fst) (csum (t.map Prod.snd)))) J 0 t.length = t.map Prod.snd := by
      rw [readJ_congr J 0 t.length _ (applyW (jw J 0 (t.map Prod.snd)) d)
        (fun i _ _ => by have : J + 1 + i ≠ J := by omega
                         simp [upd, this])]
      have := readJ_jw J 0 (t.map Prod.snd) d
      rwa [List.length_map] at this
    have hd1home : HomeEq J L (upd (applyW (jw J 0 (t.map Prod.snd)) d) J
        (.header t.length (t.map Prod.fst) (csum (t.map Prod.snd)))) d := by
      intro x hx
      rw [upd_home hx, applyW_other]
      intro p hp; have := hjw_in p hp; omega
    generalize hd1 : upd (applyW (jw J 0 (t.map Prod.snd)) d) J
        (.header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) = d1 at hd1J hd1read hd1home
    by_cases hk2 : k ≤ t.length + 1 + t.length
    · -- the cut came during the writes home: m of them made it
      have hk : k = (jw J 0 (t.map Prod.snd)).length + ((k - t.length - 1) + 1) := by omega
      rw [hP, hk, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
        List.take_succ_cons, List.take_append_of_le_length (by omega), applyW_append]
      simp only [applyW]
      rw [hd1]
      generalize hm : k - t.length - 1 = m
      have hJ : applyW (t.take m) d1 J = .header t.length (t.map Prod.fst) (csum (t.map Prod.snd)) := by
        rw [applyW_other _ _ _ (fun p hp => by have := hout p (List.mem_of_mem_take hp); omega)]
        exact hd1J
      have hread : readJ (applyW (t.take m) d1) J 0 t.length = t.map Prod.snd := by
        rw [← hd1read]
        apply readJ_congr
        intro i _ hi
        apply applyW_other
        intro p hp heq
        have := hout p (List.mem_of_mem_take hp)
        omega
      by_cases hn : t.length = 0
      · -- an empty transaction changes nothing
        have ht : t = .nil := List.length_eq_zero_iff.1 hn
        subst ht
        rw [recover_nothing _ _ _ hJ]
        intro x hx
        rw [upd_home hx]
        simp only [applyW, List.take_nil]
        exact hd1home x hx
      · rw [recover_commit _ _ _ hJ ⟨hn, by simp, by rw [hread]⟩, hread, zip_map]
        intro x hx
        rw [upd_home hx, applyW_take_then_all]
        apply applyW_congr
        by_cases h : ∃ p ∈ t, p.1 = x
        · exact Or.inl h
        · exact Or.inr (hd1home x hx)
    · -- the cut came after the last home write: all of it is there, the header clean
      rw [List.take_of_length_le (by rw [hP]; simp [length_jw]; omega), hP, applyW_append]
      simp only [applyW, applyW_append]
      rw [hd1]
      have hJ : upd (applyW t d1) J clean J = clean := by simp [upd]
      rw [recover_clean _ _ _ hJ]
      intro x hx
      rw [upd_home hx, upd_home hx]
      apply applyW_congr
      by_cases h : ∃ p ∈ t, p.1 = x
      · exact Or.inl h
      · exact Or.inr (hd1home x hx)

end LeanOS.Journal
