import LeanOS.Proofs

/-!
# How big the kernel's state can get

The kernel's state is a tree of lists: the tasks, each task's capabilities, mappings, reply
slots, result registers and measurement, the pending interrupts, the USB channel shadows,
and what the other cores run. The runtime keeps it on the kernel heap, which has a fixed
size (TRUST.md). This file proves that no sequence of system calls, with any arguments,
can make any of those lists grow past a fixed length, and so that the whole state never
needs more than `stateMax` heap objects (`stateSize_le`).

* `task_bounded`: in every reachable state, every task holds at most `maxCaps` (64)
  capabilities, at most `userPages` (8192) mappings (no two of them for the same virtual
  page, and all of them in the window), at most `maxCallers` (8) reply slots, and at most
  `maxResult` (7) result registers.
* `state_bounded`: when the machine layer calls the kernel as it does (`Driven`), as well:
  exactly `numTasks` tasks, each measured with at most eight words, at most one pending
  entry for each of the `irqLines`, eight USB channel shadows of each kind, and three other
  cores.
* `stateSize_le`: so the state is at most `stateMax` heap objects.

`Reachable` lets a boot check hand over any list of words as a measurement, and lets any
number be an interrupt line. The machine layer does neither: `exVerify` always passes the
eight words of a SHA-256, and only the lines `irq_init` enables (`irqLines`) can fire. Those
two are the only lists whose length depends on what the machine layer says rather than on
the system calls, so `Driven` is `Reachable` with just those two steps narrowed, and every
`Driven` state is `Reachable` (`Driven.reachable`).

What this bounds is the live state between two kernel entries, not the memory a step uses
while it computes the next state; see TRUST.md.
-/

namespace LeanOS

/-! ## Facts about lists -/

theorem len_eq_length {α : Type} : ∀ l : List α, len l = l.length
  | [] => rfl
  | _ :: l => by simp [len, len_eq_length l]

theorem len_snoc {α : Type} (l : List α) (v : α) : len (snoc l v) = len l + 1 := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [snoc, len, ih]

theorem snoc_eq_append {α : Type} : ∀ (l : List α) (v : α), snoc l v = l ++ [v]
  | [], _ => rfl
  | a :: l, v => by simp [snoc, snoc_eq_append l v]

theorem hasLine_of_mem {n : Nat} : ∀ {l : List Nat}, n ∈ l → hasLine n l = true
  | [], h => by simp at h
  | x :: l, h => by
    simp only [hasLine, Bool.or_eq_true, beq_iff_eq]
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hasLine_of_mem h)

theorem app_eq_append {α : Type} : ∀ l l' : List α, app l l' = l ++ l'
  | [], _ => rfl
  | a :: l, l' => by simp [app, app_eq_append l l']

theorem dropRange_sublist (vpn count : Nat) : ∀ ms : List Mapping, (dropRange vpn count ms).Sublist ms
  | [] => .slnil
  | m :: ms => by
    unfold dropRange
    split
    · exact (dropRange_sublist vpn count ms).cons m
    · exact (dropRange_sublist vpn count ms).cons_cons m

theorem keepBacked_sublist (cs : List Cap) : ∀ ms : List Mapping, (keepBacked cs ms).Sublist ms
  | [] => .slnil
  | m :: ms => by
    unfold keepBacked
    split
    · exact (keepBacked_sublist cs ms).cons_cons m
    · exact (keepBacked_sublist cs ms).cons m

theorem dropMaps_sublist (k : Nat) : ∀ ms : List Mapping, (dropMaps k ms).Sublist ms
  | [] => .slnil
  | m :: ms => by
    unfold dropMaps
    split
    · exact (dropMaps_sublist k ms).cons m
    · exact (dropMaps_sublist k ms).cons_cons m

theorem dropCaps_sublist (k : Nat) : ∀ cs : List Cap, (dropCaps k cs).Sublist cs
  | [] => .slnil
  | c :: cs => by
    unfold dropCaps
    split
    · exact (dropCaps_sublist k cs).cons c
    · exact (dropCaps_sublist k cs).cons_cons c

theorem removeNth_sublist {α : Type} : ∀ (l : List α) (i : Nat), (removeNth l i).Sublist l
  | [], _ => .slnil
  | a :: l, 0 => (List.Sublist.refl l).cons a
  | a :: l, i + 1 => (removeNth_sublist l i).cons_cons a

theorem dropLine_sublist (n : Nat) : ∀ l : List Nat, (dropLine n l).Sublist l
  | [] => .slnil
  | x :: l => by
    unfold dropLine
    split
    · exact (dropLine_sublist n l).cons x
    · exact (dropLine_sublist n l).cons_cons x

theorem len_forgetCaller (k : Nat) : ∀ l : List Nat, len (forgetCaller k l) = len l
  | [] => rfl
  | _ :: l => by simp [forgetCaller, len, len_forgetCaller k l]

theorem len_le_of_sublist {α : Type} {l l' : List α} (h : l.Sublist l') : len l ≤ len l' := by
  rw [len_eq_length, len_eq_length]; exact h.length_le

theorem mem_setNth {α : Type} : ∀ {l : List α} {i : Nat} {v a : α}, a ∈ setNth l i v → a ∈ l ∨ a = v
  | [], _, _, _, h => by simp [setNth] at h
  | x :: l, 0, v, a, h => by
    simp only [setNth, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl (List.mem_cons_of_mem _ h)
  | x :: l, i + 1, v, a, h => by
    simp only [setNth, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl (h ▸ List.mem_cons_self ..)
    · rcases mem_setNth h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

/-- A list of distinct numbers is at most one longer once one number is taken out. -/
theorem length_le_filter_ne (y : Nat) : ∀ l : List Nat, l.Pairwise (· ≠ ·) →
    l.length ≤ (l.filter (· != y)).length + 1
  | [], _ => by simp
  | x :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases hx : x = y
    · subst hx
      have : l.filter (· != x) = l :=
        List.filter_eq_self.2 (fun a ha => by simpa using (h.1 a ha).symm)
      simp [this]
    · have := length_le_filter_ne y l h.2
      simp [hx]; omega

/-- **Pigeonholes.** Distinct numbers, all taken from `L`, are at most as many as `L`. -/
theorem length_le_of_distinct : ∀ (L l : List Nat), l.Pairwise (· ≠ ·) → (∀ x ∈ l, x ∈ L) →
    l.length ≤ L.length
  | [], [], _, _ => Nat.le_refl _
  | [], x :: _, _, hs => by simpa using hs x (List.mem_cons_self ..)
  | y :: L, l, h, hs => by
    have h1 := length_le_filter_ne y l h
    have h2 := length_le_of_distinct L (l.filter (· != y)) (h.sublist List.filter_sublist)
      (fun x hx => by
        rw [List.mem_filter] at hx
        rcases List.mem_cons.1 (hs x hx.1) with h' | h'
        · simp [h'] at hx
        · exact h')
    simp only [List.length_cons]; omega

/-! ## Mappings for different pages -/

/-- No two mappings are for the same virtual page. -/
abbrev Distinct (ms : List Mapping) : Prop := ms.Pairwise (fun a b => a.vpn ≠ b.vpn)

theorem runMaps_distinct (base : Nat) (r : Rights) : ∀ (k vpn : Nat), Distinct (runMaps vpn base r k)
  | 0, _ => by simp [runMaps]
  | k + 1, vpn => by
    simp only [runMaps, Distinct, List.pairwise_cons]
    refine ⟨fun m hm => ?_, runMaps_distinct (base + 1) r k (vpn + 1)⟩
    obtain ⟨j, -, hv, -⟩ := mem_runMaps hm
    omega
termination_by k => k

/-- Mappings for distinct pages, all in the window, are at most as many as its pages. -/
theorem len_le_of_distinct {ms : List Mapping} (hd : Distinct ms) (hv : ∀ m ∈ ms, m.vpn < userPages) :
    len ms ≤ userPages := by
  have := length_le_of_distinct (List.range userPages) (ms.map (·.vpn))
    (hd.map _ (fun _ _ h => h))
    (fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
      exact List.mem_range.2 (hv m hm))
  simpa [len_eq_length] using this

/-- `map`: the new run's pages are all in the range it drops, so they are fresh. -/
theorem distinct_map {ms : List Mapping} (h : Distinct ms) (vpn base : Nat) (r : Rights) (count : Nat) :
    Distinct (app (runMaps vpn base r count) (dropRange vpn count ms)) := by
  rw [app_eq_append]
  refine List.pairwise_append.2 ⟨runMaps_distinct base r count vpn,
    h.sublist (dropRange_sublist _ _ _), fun a ha b hb => ?_⟩
  obtain ⟨k, hk, hv, -⟩ := mem_runMaps ha
  have := (mem_dropRange.1 hb).2
  omega

theorem initMaps_distinct (i : Nat) : Distinct (initMaps i) := by
  simp only [initMaps, app_eq_append, Distinct]
  refine List.pairwise_append.2 ⟨runMaps_distinct _ _ _ _, List.pairwise_append.2
    ⟨runMaps_distinct _ _ _ _, runMaps_distinct _ _ _ _, fun a ha b hb => ?_⟩, fun a ha b hb => ?_⟩
  · obtain ⟨k, hk, hv, -⟩ := mem_runMaps ha
    obtain ⟨k', hk', hv', -⟩ := mem_runMaps hb
    simp only [userPages] at hv'; omega
  · obtain ⟨k, hk, hv, -⟩ := mem_runMaps ha
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨k', hk', hv', -⟩ := mem_runMaps hb; omega
    · obtain ⟨k', hk', hv', -⟩ := mem_runMaps hb; simp only [userPages] at hv'; omega

/-! ## The invariant -/

/-- The most result registers a call leaves: `time` and a delivered message leave seven. -/
def maxResult : Nat := 7

/-- Shows `len l ≤ n` for a list whose length can be read off its constructors. -/
macro "len_le" : tactic => `(tactic| exact Nat.le_of_ble_eq_true rfl)

theorem len_initCaps (i : Nat) : len (initCaps i) ≤ maxCaps := by
  unfold initCaps; split <;> len_le

/-- Task `t` is small. `hp` says which measurements a task may hold: under `Reachable`, any
list at all; when the machine layer calls the kernel as it does (`Driven`), eight words. -/
structure TaskSmall (hp : List Nat → Prop) (t : Task) : Prop where
  caps : len t.caps ≤ maxCaps
  maps : Distinct t.maps
  callers : len t.callers ≤ maxCallers
  result : len t.result ≤ maxResult
  hash : hp t.hash

/-- The state is small. `lp` says which interrupt lines may fire. -/
structure Small (hp : List Nat → Prop) (lp : Nat → Prop) (s : KState) : Prop where
  tasks : ∀ t ∈ s.tasks, TaskSmall hp t
  pending : s.pending.Pairwise (· ≠ ·)
  lines : ∀ n ∈ s.pending, lp n
  usbDma : len s.usbDma = 8
  usbSize : len s.usbSize = 8
  busy : len s.busy ≤ 3

section
variable {hp : List Nat → Prop} {lp : Nat → Prop}

theorem TaskSmall.res {t : Task} (h : TaskSmall hp t) {r : List Nat} (hr : len r ≤ maxResult) :
    TaskSmall hp { t with result := r } := ⟨h.caps, h.maps, h.callers, hr, h.hash⟩

theorem TaskSmall.st {t : Task} (h : TaskSmall hp t) (st : Status) {r : List Nat} (hr : len r ≤ maxResult) :
    TaskSmall hp { t with status := st, result := r } := ⟨h.caps, h.maps, h.callers, hr, h.hash⟩

theorem Small.task {s : KState} (hs : Small hp lp s) {j : Nat} {t : Task} (h : nth? s.tasks j = some t) :
    TaskSmall hp t := hs.tasks t (nth?_mem h)

theorem small_setTask {s : KState} (hs : Small hp lp s) {j : Nat} {t : Task} (ht : TaskSmall hp t) :
    Small hp lp (setTask s j t) :=
  ⟨fun u hu => (mem_setNth hu).elim (hs.tasks u) (fun h => h ▸ ht), hs.pending, hs.lines, hs.usbDma,
    hs.usbSize, hs.busy⟩

theorem small_schedule {s : KState} (hs : Small hp lp s) : Small hp lp (schedule s) := by
  unfold schedule
  split
  · exact ⟨hs.tasks, hs.pending, hs.lines, hs.usbDma, hs.usbSize, hs.busy⟩
  · exact hs

theorem small_ret {s : KState} (hs : Small hp lp s) {t : Task} (ht : TaskSmall hp t) {r : List Nat}
    (hr : len r ≤ maxResult) : Small hp lp (ret s t r).state :=
  small_setTask hs (ht.res hr)

theorem deliver_small {u u' : Task} {m : Msg} {sender : Nat} (hu : TaskSmall hp u)
    (hd : deliver u m sender = some u') : TaskSmall hp u' := by
  unfold deliver at hd
  dsimp only at hd
  repeat' split at hd
  all_goals first
    | (simp at hd; done)
    | (simp only [Option.some.injEq] at hd; subst hd
       exact ⟨by first | exact hu.caps | (rw [len_snoc]; exact Nat.succ_le_of_lt ‹_›), hu.maps,
         by assumption, by len_le, hu.hash⟩)

/-! ## Every step keeps the state small -/

section calls
variable {s : KState} {t : Task} (hs : Small hp lp s) (ht : TaskSmall hp t)
include hs ht

theorem small_sysWrite {va n : Nat} : Small hp lp (sysWrite s t va n).state := by
  unfold sysWrite
  split
  · exact small_ret hs ht (by len_le)
  · split
    · exact small_setTask hs (ht.res (by len_le))
    · exact small_ret hs ht (by len_le)

theorem small_sysMap {ci vpn : Nat} : Small hp lp (sysMap s t ci vpn).state := by
  unfold sysMap
  split
  · exact small_ret hs ht (by len_le)
  · split
    · split
      · exact small_setTask hs ⟨ht.caps, distinct_map ht.maps _ _ _ _, ht.callers, by len_le, ht.hash⟩
      · exact small_ret hs ht (by len_le)
    · exact small_ret hs ht (by len_le)

theorem small_sysUnmap {vpn count : Nat} : Small hp lp (sysUnmap s t vpn count).state :=
  small_setTask hs ⟨ht.caps, ht.maps.sublist (dropRange_sublist _ _ _), ht.callers, by len_le, ht.hash⟩

theorem small_sysDerive {ci bits off cnt : Nat} : Small hp lp (sysDerive s t ci bits off cnt).state := by
  unfold sysDerive
  split
  · exact small_ret hs ht (by len_le)
  · split
    · exact small_ret hs ht (by len_le)
    · split
      · rename_i hc
        apply small_ret hs _ (by len_le)
        exact ⟨by rw [len_snoc]; exact Nat.succ_le_of_lt hc, ht.maps, ht.callers, ht.result, ht.hash⟩
      · exact small_ret hs ht (by len_le)

theorem small_sysCapInfo {ci : Nat} : Small hp lp (sysCapInfo s t ci).state := by
  unfold sysCapInfo
  split
  · exact small_ret hs ht (by len_le)
  · split <;> exact small_ret hs ht (by len_le)

theorem small_sysReply {slot w0 w1 w2 : Nat} : Small hp lp (sysReply s t slot w0 w1 w2).state := by
  have ht' : TaskSmall hp { t with callers := setNth t.callers slot noTask } :=
    ⟨ht.caps, ht.maps, by rw [len_setNth]; exact ht.callers, ht.result, ht.hash⟩
  unfold sysReply
  split
  · exact small_ret hs ht (by len_le)
  · dsimp only
    split
    · split
      · rename_i u hu
        exact small_ret (small_setTask hs ((hs.task hu).st _ (by len_le))) ht' (by len_le)
      · exact small_ret hs ht' (by len_le)
    · exact small_ret hs ht' (by len_le)

theorem small_sysIrqWait {ci : Nat} : Small hp lp (sysIrqWait s t ci).state := by
  unfold sysIrqWait
  split
  · exact small_ret hs ht (by len_le)
  · split
    · split
      · rename_i n _ _
        exact small_ret (s := { s with pending := dropLine n s.pending })
          ⟨hs.tasks, hs.pending.sublist (dropLine_sublist _ _),
            fun x hx => hs.lines x ((dropLine_sublist _ _).subset hx), hs.usbDma, hs.usbSize, hs.busy⟩
          ht (by len_le)
      · exact small_schedule (small_setTask hs (ht.st _ (by len_le)))
    · exact small_ret hs ht (by len_le)

theorem small_sysIrqAck {ci : Nat} : Small hp lp (sysIrqAck s t ci).state := by
  unfold sysIrqAck
  split
  · exact small_ret hs ht (by len_le)
  · split <;> exact small_ret hs ht (by len_le)

theorem small_sysBootInfo {i : Nat} : Small hp lp (sysBootInfo s t i).state := by
  unfold sysBootInfo
  split <;> exact small_ret hs ht (by len_le)

theorem small_sysDrop {ci : Nat} : Small hp lp (sysDrop s t ci).state := by
  unfold sysDrop
  split
  · exact small_ret hs ht (by len_le)
  · exact small_setTask hs ⟨Nat.le_trans (len_le_of_sublist (removeNth_sublist _ _)) ht.caps,
      ht.maps.sublist (keepBacked_sublist _ _), ht.callers, by len_le, ht.hash⟩

theorem small_sysBlock {ci idx va : Nat} {w : Bool} : Small hp lp (sysBlock s t ci idx va w).state := by
  unfold sysBlock
  repeat' split
  all_goals first
    | exact small_ret hs ht (by len_le)
    | exact small_setTask hs (ht.res (by len_le))

theorem small_sysPower {ci a : Nat} : Small hp lp (sysPower s t ci a).state := by
  unfold sysPower
  repeat' split
  all_goals first
    | exact small_ret hs ht (by len_le)
    | exact small_setTask hs (ht.res (by len_le))

theorem small_sysBoard {ci w v : Nat} : Small hp lp (sysBoard s t ci w v).state := by
  unfold sysBoard
  repeat' (first | split | dsimp only)
  all_goals first
    | exact small_ret hs ht (by len_le)
    | exact small_setTask hs (ht.res (by len_le))

theorem small_sysUsb {ci op reg v : Nat} : Small hp lp (sysUsb s t ci op reg v).state := by
  unfold sysUsb usbReply
  split
  · exact small_ret hs ht (by len_le)
  split
  all_goals try exact small_ret hs ht (by len_le)
  repeat' (first | apply of_ite (P := fun r : Reply => Small hp lp r.state) | dsimp only)
  all_goals first
    | exact small_ret hs ht (by len_le)
    | exact small_setTask hs (ht.res (by len_le))
    | exact small_ret (s := { s with usbDma := setNth s.usbDma (chanOf reg) v })
        ⟨hs.tasks, hs.pending, hs.lines, by rw [len_setNth]; exact hs.usbDma, hs.usbSize, hs.busy⟩ ht (by len_le)
    | exact small_ret (s := { s with usbSize := setNth s.usbSize (chanOf reg) v })
        ⟨hs.tasks, hs.pending, hs.lines, hs.usbDma, by rw [len_setNth]; exact hs.usbSize, hs.busy⟩ ht (by len_le)

theorem small_sysStop {ci : Nat} : Small hp lp (sysStop s t ci).state := by
  unfold sysStop
  split
  · exact small_ret hs ht (by len_le)
  · split
    · split
      · rename_i u hu
        split
        · exact small_ret (small_setTask hs ((hs.task hu).st _ (by len_le))) ht (by len_le)
        · exact small_ret hs ht (by len_le)
      · exact small_ret hs ht (by len_le)
    · exact small_ret hs ht (by len_le)

theorem small_sysSetWall {ci secs : Nat} : Small hp lp (sysSetWall s t ci secs).state := by
  unfold sysSetWall
  split
  · exact small_ret hs ht (by len_le)
  · split
    · split
      · exact small_ret (s := { s with wall := secs - s.now * tickMs / 1000 })
          ⟨hs.tasks, hs.pending, hs.lines, hs.usbDma, hs.usbSize, hs.busy⟩ ht (by len_le)
      · exact small_ret hs ht (by len_le)
    · exact small_ret hs ht (by len_le)

theorem small_sysSleep {ms : Nat} : Small hp lp (sysSleep s t ms).state := by
  unfold sysSleep
  dsimp only
  split
  · exact small_schedule (small_setTask hs (ht.res (by len_le)))
  · exact small_schedule (small_setTask hs (ht.st _ (by len_le)))

theorem small_sysSend {ci w0 w1 w2 gi : Nat} {call : Bool} :
    Small hp lp (sysSend s t ci w0 w1 w2 gi call).state := by
  unfold sysSend
  split
  · exact small_ret hs ht (by len_le)
  · split
    rotate_left
    · exact small_ret hs ht (by len_le)
    · split
      · split
        · exact small_ret hs ht (by len_le)
        · dsimp only
          split
          · split
            · rename_i u hu
              split
              · rename_i u' hd
                split
                · exact small_schedule (small_setTask (small_setTask hs (deliver_small (hs.task hu) hd))
                    (ht.st _ (by len_le)))
                · exact small_ret (small_setTask hs (deliver_small (hs.task hu) hd)) ht (by len_le)
              · exact small_ret hs ht (by len_le)
            · exact small_ret hs ht (by len_le)
          · exact small_schedule (small_setTask hs (ht.st _ (by len_le)))
      · exact small_ret hs ht (by len_le)

theorem small_sysRecv {ci : Nat} {block : Bool} {deadline : Nat} :
    Small hp lp (sysRecv s t ci block deadline).state := by
  unfold sysRecv
  split
  · exact small_ret hs ht (by len_le)
  · split
    rotate_left
    · exact small_ret hs ht (by len_le)
    · split
      · split
        · split
          · rename_i u hu
            split
            · rename_i t' hd
              dsimp only
              refine small_setTask (small_setTask hs ?_) (deliver_small ht hd)
              split
              · exact (hs.task hu).st _ (by len_le)
              · exact (hs.task hu).st _ (by len_le)
            · exact small_ret hs ht (by len_le)
          · exact small_ret hs ht (by len_le)
        · split
          · exact small_schedule (small_setTask hs (ht.st _ (by len_le)))
          · exact small_ret hs ht (by len_le)
      · exact small_ret hs ht (by len_le)

end calls

/-! ### Starting a program -/

theorem TaskSmall.revoke {t : Task} (h : TaskSmall hp t) (k : Nat) : TaskSmall hp (revokeTask k t) :=
  ⟨Nat.le_trans (len_le_of_sublist (dropCaps_sublist _ _)) h.caps, h.maps.sublist (dropMaps_sublist _ _),
    by simp only [revokeTask, len_forgetCaller]; exact h.callers, h.result, h.hash⟩

theorem mkTask_small (hnil : hp .nil) (i : Nat) : TaskSmall hp (mkTask i) :=
  ⟨len_initCaps i, initMaps_distinct i, by len_le, by len_le, hnil⟩

theorem mem_revokeAll {k : Nat} : ∀ {ts : List Task} {u : Task}, u ∈ revokeAll k ts → ∃ t ∈ ts, u = revokeTask k t
  | [], _, h => by simp [revokeAll] at h
  | t :: ts, u, h => by
    simp only [revokeAll, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨t, List.mem_cons_self .., h⟩
    · obtain ⟨t', ht', e⟩ := mem_revokeAll h
      exact ⟨t', List.mem_cons_of_mem _ ht', e⟩

theorem small_sysStart {s : KState} {t : Task} (hs : Small hp lp s) (ht : TaskSmall hp t) (hnil : hp .nil)
    {ci src len : Nat} : Small hp lp (sysStart s t ci src len).state := by
  unfold sysStart
  split <;> (try exact small_ret hs ht (by len_le))
  split <;> (try exact small_ret hs ht (by len_le))
  rename_i k _
  split <;> (try exact small_ret hs ht (by len_le))
  split <;> (try exact small_ret hs ht (by len_le))
  have h0 : Small hp lp { s with tasks := revokeAll k s.tasks } :=
    ⟨fun u hu => by
      obtain ⟨t0, ht0, rfl⟩ := mem_revokeAll hu
      exact (hs.tasks t0 ht0).revoke k, hs.pending, hs.lines, hs.usbDma, hs.usbSize, hs.busy⟩
  have h1 := small_setTask (j := k) h0 (mkTask_small hnil k)
  dsimp only
  split
  · rename_i t1 ht1
    exact small_setTask h1 ((h1.task ht1).res (by len_le))
  · exact small_ret hs ht (by len_le)

/-! ### The other steps -/

theorem small_killCurrent {s : KState} (hs : Small hp lp s) : Small hp lp (killCurrent s) := by
  unfold killCurrent
  split
  · rename_i t ht; exact small_schedule (small_setTask hs ((hs.task ht).st _ (by len_le)))
  · exact small_schedule hs

theorem small_syscall {s : KState} (hs : Small hp lp s) (hnil : hp .nil) (num a0 a1 a2 a3 a4 : Nat) :
    Small hp lp (syscall s num a0 a1 a2 a3 a4).state := by
  unfold syscall
  split
  · exact hs
  · rename_i t hc
    have ht := hs.task hc
    split
    · unfold runCall
      split
      · exact small_sysWrite hs ht
      · exact small_schedule (small_setTask hs (ht.res (by len_le)))
      · exact small_sysMap hs ht
      · exact small_sysUnmap hs ht
      · exact small_sysDerive hs ht
      · exact small_killCurrent hs
      · exact small_sysCapInfo hs ht
      · exact small_ret hs ht (by len_le)
      · exact small_sysSend hs ht
      · exact small_sysRecv hs ht
      · exact small_sysSend hs ht
      · exact small_sysReply hs ht
      · exact small_sysIrqWait hs ht
      · exact small_sysIrqAck hs ht
      · exact small_sysBootInfo hs ht
      · exact small_sysStart hs ht hnil
      · exact small_sysDrop hs ht
      · exact small_sysBlock hs ht
      · exact small_sysBlock hs ht
      · exact small_sysStart hs ht hnil
      · exact small_sysSleep hs ht
      · exact small_sysPower hs ht
      · exact small_ret hs ht (by len_le)
      · exact small_sysBoard hs ht
      · exact small_sysUsb hs ht
      · exact small_sysRecv hs ht
      · exact small_sysStop hs ht
      · exact small_sysSetWall hs ht
      · exact small_ret hs ht (by len_le)
    · exact hs

theorem mem_wakeSleepers {now : Nat} : ∀ {ts : List Task} {u : Task}, u ∈ wakeSleepers now ts →
    ∃ t ∈ ts, u = wakeTask now t
  | [], _, h => by simp [wakeSleepers] at h
  | t :: ts, u, h => by
    simp only [wakeSleepers, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨t, List.mem_cons_self .., h⟩
    · obtain ⟨t', ht', e⟩ := mem_wakeSleepers h
      exact ⟨t', List.mem_cons_of_mem _ ht', e⟩

theorem TaskSmall.wake {t : Task} (h : TaskSmall hp t) (now : Nat) : TaskSmall hp (wakeTask now t) := by
  unfold wakeTask
  split
  · split
    · exact h.st _ (by len_le)
    · exact h
  · split
    · exact h.st _ (by len_le)
    · exact h
  · exact h

theorem small_tick {s : KState} (hs : Small hp lp s) : Small hp lp (tick s) := by
  unfold tick
  apply small_schedule
  refine ⟨fun u hu => ?_, hs.pending, hs.lines, hs.usbDma, hs.usbSize, hs.busy⟩
  obtain ⟨t, ht, rfl⟩ := mem_wakeSleepers hu
  exact (hs.tasks t ht).wake _

theorem small_clearResult {s : KState} (hs : Small hp lp s) (j : Nat) : Small hp lp (clearResult s j) := by
  unfold clearResult
  split
  · rename_i t ht; exact small_setTask hs ((hs.task ht).res (by len_le))
  · exact hs

theorem small_ioFailed {s : KState} (hs : Small hp lp s) : Small hp lp (ioFailed s) := by
  unfold ioFailed
  split
  · rename_i t ht; exact small_setTask hs ((hs.task ht).res (by len_le))
  · exact hs

theorem small_boardDone {s : KState} (hs : Small hp lp s) (a b c d e : Nat) :
    Small hp lp (boardDone s a b c d e) := by
  unfold boardDone
  split
  · rename_i t ht; exact small_setTask hs ((hs.task ht).res (by len_le))
  · exact hs

theorem small_usbDone {s : KState} (hs : Small hp lp s) (v : Nat) : Small hp lp (usbDone s v) := by
  unfold usbDone
  split
  · rename_i t ht; exact small_setTask hs ((hs.task ht).res (by len_le))
  · exact hs

theorem small_enter {s : KState} (hs : Small hp lp s) (c b0 b1 b2 : Nat) :
    Small hp lp (enter s c b0 b1 b2) :=
  ⟨hs.tasks, hs.pending, hs.lines, hs.usbDma, hs.usbSize, by len_le⟩

theorem small_irqFired {s : KState} (hs : Small hp lp s) (n : Nat) (hn : lp n) :
    Small hp lp (irqFired s n) := by
  unfold irqFired
  split
  · split
    · rename_i u hu; exact small_setTask hs ((hs.task hu).st _ (by len_le))
    · exact hs
  · split
    · exact hs
    · rename_i hno
      have hnot : n ∉ s.pending := fun hm => hno (hasLine_of_mem hm)
      refine ⟨hs.tasks, ?_, fun x hx => ?_, hs.usbDma, hs.usbSize, hs.busy⟩
      · rw [snoc_eq_append]
        exact List.pairwise_append.2 ⟨hs.pending, List.pairwise_singleton _ _,
          fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun e => hnot (e ▸ ha)⟩
      · rcases mem_snoc.1 hx with h | h
        · exact hs.lines x h
        · exact h ▸ hn

theorem small_verify {s : KState} (hs : Small hp lp s) (i : Nat) {h : List Nat} (hh : hp h) :
    Small hp lp (verify s i h) := by
  unfold verify
  split
  · rename_i t ht
    have := hs.task ht
    split
    · split
      · exact small_setTask hs ⟨this.caps, this.maps, this.callers, this.result, hh⟩
      · exact small_setTask hs ⟨this.caps, this.maps, this.callers, this.result, hh⟩
    · exact hs
  · exact hs

theorem mem_mkTasksFrom : ∀ {k n : Nat} {t : Task}, t ∈ mkTasksFrom k n → ∃ i, t = mkTask i
  | _, 0, _, h => by simp [mkTasksFrom] at h
  | k, n + 1, t, h => by
    simp only [mkTasksFrom, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, h⟩
    · exact mem_mkTasksFrom h

theorem small_init (hnil : hp .nil) (fb : Nat) : Small hp lp (init fb) :=
  ⟨fun t ht => by obtain ⟨i, rfl⟩ := mem_mkTasksFrom ht; exact mkTask_small hnil i,
    List.Pairwise.nil, fun _ h => by simp [init] at h, rfl, rfl, by len_le⟩

end

/-! ## Reachable states are small -/

theorem nth?_of_mem {α : Type} : ∀ {l : List α} {a : α}, a ∈ l → ∃ j, nth? l j = some a
  | [], _, h => by simp at h
  | x :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, rfl⟩
    · obtain ⟨j, hj⟩ := nth?_of_mem h; exact ⟨j + 1, hj⟩

/-- Every reachable state is small, whatever measurements and interrupt lines the machine
layer hands over. -/
theorem small_reachable {s : KState} (h : Reachable s) : Small (fun _ => True) (fun _ => True) s := by
  induction h with
  | init fb => exact small_init trivial fb
  | syscall num a0 a1 a2 a3 a4 _ ih => exact small_syscall ih trivial num a0 a1 a2 a3 a4
  | tick _ ih => exact small_tick ih
  | fault _ ih => exact small_killCurrent ih
  | clear j _ ih => exact small_clearResult ih j
  | irq n _ ih => exact small_irqFired ih n trivial
  | verify i h _ ih => exact small_verify ih i trivial
  | ioFail _ ih => exact small_ioFailed ih
  | board a b c d e _ ih => exact small_boardDone ih a b c d e
  | usb v _ ih => exact small_usbDone ih v
  | enter c b0 b1 b2 _ ih => exact small_enter ih c b0 b1 b2
  | resched _ ih => exact small_schedule ih

/-- **Every task's lists are bounded.** In every reachable state, every task holds at most
`maxCaps` (64) capabilities, at most `userPages` (8192) mappings, no two of them for the
same virtual page, at most `maxCallers` (8) reply slots, and at most `maxResult` (7) result
registers. -/
theorem task_bounded {s : KState} (h : Reachable s) {t : Task} (ht : t ∈ s.tasks) :
    len t.caps ≤ maxCaps ∧ len t.maps ≤ userPages ∧ t.maps.Pairwise (fun a b => a.vpn ≠ b.vpn) ∧
      len t.callers ≤ maxCallers ∧ len t.result ≤ maxResult := by
  have hs := (small_reachable h).tasks t ht
  obtain ⟨j, hj⟩ := nth?_of_mem ht
  exact ⟨hs.caps, len_le_of_distinct hs.maps ((reachable_inv h).tasks j t hj).vpnOk, hs.maps, hs.callers,
    hs.result⟩

/-! ## The machine layer's inputs -/

/-- The states the kernel reaches when the machine layer calls it as it does: `Reachable`,
except that a boot check hands over the eight words of a SHA-256, as `exVerify` always does,
and an interrupt is on one of `irqLines`, the only lines `irq_init` enables (TRUST.md). -/
inductive Driven : KState → Prop
  | init (fb : Nat) : Driven (init fb)
  | syscall {s} (num a0 a1 a2 a3 a4 : Nat) : Driven s → Driven (syscall s num a0 a1 a2 a3 a4).state
  | tick {s} : Driven s → Driven (tick s)
  | fault {s} : Driven s → Driven (killCurrent s)
  | clear {s} (j : Nat) : Driven s → Driven (clearResult s j)
  | irq {s} (n : Nat) : n ∈ irqLines → Driven s → Driven (irqFired s n)
  | verify {s} (i w0 w1 w2 w3 w4 w5 w6 w7 : Nat) : Driven s →
      Driven (verify s i (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: .nil))
  | ioFail {s} : Driven s → Driven (ioFailed s)
  | board {s} (a b c d e : Nat) : Driven s → Driven (boardDone s a b c d e)
  | usb {s} (v : Nat) : Driven s → Driven (usbDone s v)
  | enter {s} (c b0 b1 b2 : Nat) : Driven s → Driven (enter s c b0 b1 b2)
  | resched {s} : Driven s → Driven (schedule s)

/-- So every theorem about reachable states holds for them. -/
theorem Driven.reachable {s : KState} (h : Driven s) : Reachable s := by
  induction h with
  | init fb => exact .init fb
  | syscall num a0 a1 a2 a3 a4 _ ih => exact .syscall num a0 a1 a2 a3 a4 ih
  | tick _ ih => exact .tick ih
  | fault _ ih => exact .fault ih
  | clear j _ ih => exact .clear j ih
  | irq n _ _ ih => exact .irq n ih
  | verify i w0 w1 w2 w3 w4 w5 w6 w7 _ ih => exact .verify i _ ih
  | ioFail _ ih => exact .ioFail ih
  | board a b c d e _ ih => exact .board a b c d e ih
  | usb v _ ih => exact .usb v ih
  | enter c b0 b1 b2 _ ih => exact .enter c b0 b1 b2 ih
  | resched _ ih => exact .resched ih

theorem small_driven {s : KState} (h : Driven s) :
    Small (fun hash => len hash ≤ 8) (fun n => n ∈ irqLines) s := by
  induction h with
  | init fb => exact small_init (by len_le) fb
  | syscall num a0 a1 a2 a3 a4 _ ih => exact small_syscall ih (by len_le) num a0 a1 a2 a3 a4
  | tick _ ih => exact small_tick ih
  | fault _ ih => exact small_killCurrent ih
  | clear j _ ih => exact small_clearResult ih j
  | irq n hn _ ih => exact small_irqFired ih n hn
  | verify i _ _ _ _ _ _ _ _ _ ih => exact small_verify ih i (by len_le)
  | ioFail _ ih => exact small_ioFailed ih
  | board a b c d e _ ih => exact small_boardDone ih a b c d e
  | usb v _ ih => exact small_usbDone ih v
  | enter c b0 b1 b2 _ ih => exact small_enter ih c b0 b1 b2
  | resched _ ih => exact small_schedule ih

/-- **The state is bounded.** When the machine layer calls the kernel as it does, the state
has exactly `numTasks` tasks, each within `task_bounded`'s limits and measured with at most
eight words; at most one pending entry for each interrupt line; eight DMA addresses and
eight transfer sizes for the USB channels; and at most three other cores. -/
theorem state_bounded {s : KState} (h : Driven s) :
    len s.tasks = numTasks ∧
      (∀ t ∈ s.tasks, len t.caps ≤ maxCaps ∧ len t.maps ≤ userPages ∧ len t.callers ≤ maxCallers ∧
        len t.result ≤ maxResult ∧ len t.hash ≤ 8) ∧
      len s.pending ≤ len irqLines ∧ len s.usbDma = 8 ∧ len s.usbSize = 8 ∧ len s.busy ≤ 3 := by
  have hs := small_driven h
  refine ⟨(reachable_inv h.reachable).len, fun t ht => ?_, ?_, hs.usbDma, hs.usbSize, hs.busy⟩
  · obtain ⟨h1, h2, -, h3, h4⟩ := task_bounded h.reachable ht
    exact ⟨h1, h2, h3, h4, (hs.tasks t ht).hash⟩
  · rw [len_eq_length, len_eq_length]
    exact length_le_of_distinct _ _ hs.pending hs.lines

/-! ## The whole state, in heap objects

How the runtime (`rt/runtime.c` with Lean's `lean.h`) stores the state: every list cell is
one heap object, and so is every structure (`KState`, `Task`, `Cap`, `Obj`, `Rights`,
`Mapping`, `Msg`, an `Option`'s `some`, a `Status` with fields). A number below 2^63 (the
runtime stops the machine at a larger one), a `Bool`, and a constructor without fields
(`none`, `ready`, `power`, ...) are stored in the pointer itself and take no object. So
`stateSize` counts the objects the state can need: a capability as three (the `Cap`, its
`Obj` and its `Rights`, whatever the kind; fewer when the object has no fields), a mapping as
two, and each list cell as one. Objects shared between two places are counted twice, so the
runtime needs at most this many. -/

/-- One object per cell of the list, and `f a` for what element `a` holds. -/
def listObjs {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => 1 + f a + listObjs f l

/-- A capability: the `Cap`, its `Obj`, its `Rights`. -/
def capObjs : Nat := 3
/-- A mapping: the `Mapping` and its `Rights`. -/
def mapObjs : Nat := 2

/-- A message: the `Msg`, and a granted capability in its `some`. -/
def msgObjs (m : Msg) : Nat :=
  1 + match m.grant with
    | some _ => 1 + capObjs
    | none => 0

/-- A status: one object, and a waiting sender's message besides. (`unverified`, `ready`
and `dead` take none; one is an upper bound.) -/
def statusObjs : Status → Nat
  | .sending _ m => 1 + msgObjs m
  | _ => 1

/-- A task: the `Task`, and what its lists and its status hold. -/
def taskObjs (t : Task) : Nat :=
  1 + listObjs (fun _ => capObjs) t.caps + listObjs (fun _ => mapObjs) t.maps + statusObjs t.status +
    listObjs (fun _ => 0) t.result + listObjs (fun _ => 0) t.callers + listObjs (fun _ => 0) t.hash

/-- The heap objects state `s` can take (at most). -/
def stateSize (s : KState) : Nat :=
  1 + listObjs taskObjs s.tasks + listObjs (fun _ => 0) s.pending + listObjs (fun _ => 0) s.usbDma +
    listObjs (fun _ => 0) s.usbSize + listObjs (fun _ => 0) s.busy

/-- The most one task takes: 1 + 64 × 4 + 8192 × 3 + 6 + 7 + 8 + 8. -/
def taskMax : Nat := 24862

/-- The most the state takes: 1 + 18 × (1 + `taskMax`) + 2 + 8 + 8 + 3. -/
def stateMax : Nat := 447556

theorem listObjs_le {α : Type} {f : α → Nat} {k : Nat} :
    ∀ {l : List α}, (∀ a ∈ l, f a ≤ k) → listObjs f l ≤ len l * (1 + k)
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    have h1 := h a (List.mem_cons_self ..)
    have h2 := listObjs_le (l := l) (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [listObjs, len, Nat.succ_mul]; omega

theorem statusObjs_le (st : Status) : statusObjs st ≤ 6 := by
  unfold statusObjs msgObjs capObjs
  split
  · split <;> omega
  · omega

theorem taskObjs_le {t : Task} (hc : len t.caps ≤ maxCaps) (hm : len t.maps ≤ userPages)
    (hr : len t.result ≤ maxResult) (hcl : len t.callers ≤ maxCallers) (hh : len t.hash ≤ 8) :
    taskObjs t ≤ taskMax := by
  have h1 := listObjs_le (f := fun _ => capObjs) (k := capObjs) (l := t.caps) (fun _ _ => Nat.le_refl _)
  have h2 := listObjs_le (f := fun _ => mapObjs) (k := mapObjs) (l := t.maps) (fun _ _ => Nat.le_refl _)
  have h3 := listObjs_le (f := fun _ => 0) (k := 0) (l := t.result) (fun _ _ => Nat.le_refl _)
  have h4 := listObjs_le (f := fun _ => 0) (k := 0) (l := t.callers) (fun _ _ => Nat.le_refl _)
  have h5 := listObjs_le (f := fun _ => 0) (k := 0) (l := t.hash) (fun _ _ => Nat.le_refl _)
  have h6 := statusObjs_le t.status
  simp only [maxCaps, userPages, maxResult, maxCallers, capObjs, mapObjs] at *
  unfold taskObjs taskMax capObjs mapObjs
  omega

/-- **The state fits in a fixed number of heap objects.** When the machine layer calls the
kernel as it does, the state never takes more than `stateMax` (447,556) heap objects,
whatever system calls the tasks make. -/
theorem stateSize_le {s : KState} (h : Driven s) : stateSize s ≤ stateMax := by
  obtain ⟨hn, ht, hp, hd, hz, hb⟩ := state_bounded h
  have h1 := listObjs_le (f := taskObjs) (k := taskMax) (l := s.tasks) (fun t ht' => by
    obtain ⟨a, b, c, d, e⟩ := ht t ht'; exact taskObjs_le a b d c e)
  have h2 := listObjs_le (f := fun _ => 0) (k := 0) (l := s.pending) (fun _ _ => Nat.le_refl _)
  have h3 := listObjs_le (f := fun _ => 0) (k := 0) (l := s.usbDma) (fun _ _ => Nat.le_refl _)
  have h4 := listObjs_le (f := fun _ => 0) (k := 0) (l := s.usbSize) (fun _ _ => Nat.le_refl _)
  have h5 := listObjs_le (f := fun _ => 0) (k := 0) (l := s.busy) (fun _ _ => Nat.le_refl _)
  have hl : len irqLines = 2 := rfl
  simp only [numTasks, taskMax] at hn h1
  rw [hn] at h1
  unfold stateSize stateMax
  omega

end LeanOS
