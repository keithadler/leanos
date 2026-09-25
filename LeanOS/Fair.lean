import LeanOS.Bounds

/-!
# Receiving is fair

Several tasks can be blocked sending to the same endpoint, waiting for its server to
receive. A receive takes one of them (`sysRecv`). Which one used to be the lowest-numbered,
so programs in low slots that kept a server busy could keep a program in a higher slot
waiting for good. Now each endpoint remembers the task it took a message from last
(`KState.served`), and the next receive looks from the task after it on, wrapping around
(`findSender`): round robin, as the scheduler does for tasks that are ready.

* `recv_in_turn`: a receive on endpoint `e` takes the message of the first task blocked
  sending to `e`, counting from the task after the one `e` served last and wrapping around.
  That task is no longer blocked, and `e` now remembers it; no other endpoint's changes.
* `recv_misses_nobody`: a receive finds no message only if no task is blocked sending to
  its endpoint.
* `served_only_by_recv`: nothing else moves what an endpoint remembers.
* `recv_bounded_wait`: bounded waiting. While task `j` stays blocked sending to endpoint
  `e`, the receivers on `e` take fewer than `numTasks` (18) messages, and in fact at most as
  many as there are tasks between the one `e` served last and `j` (`recv_wait_ahead`).

What this is about is the order in which waiting senders are served. It does not say that a
server ever calls `recv` (that is the server's code), or that a sender is scheduled.
-/

namespace LeanOS

/-! ## One step of the kernel -/

/-- One step of the kernel: exactly the steps `Reachable` allows from a state. -/
inductive Step : KState → KState → Prop
  | syscall (s : KState) (num a0 a1 a2 a3 a4 : Nat) : Step s (syscall s num a0 a1 a2 a3 a4).state
  | tick (s : KState) : Step s (tick s)
  | fault (s : KState) : Step s (killCurrent s)
  | clear (s : KState) (j : Nat) : Step s (clearResult s j)
  | irq (s : KState) (n : Nat) : Step s (irqFired s n)
  | verify (s : KState) (i : Nat) (h : List Nat) : Step s (verify s i h)
  | ioFail (s : KState) : Step s (ioFailed s)
  | board (s : KState) (a b c d e : Nat) : Step s (boardDone s a b c d e)
  | usb (s : KState) (v : Nat) : Step s (usbDone s v)
  | enter (s : KState) (c b0 b1 b2 : Nat) : Step s (enter s c b0 b1 b2)
  | resched (s : KState) : Step s (schedule s)

theorem Reachable.step {s s' : KState} (h : Reachable s) (hs : Step s s') : Reachable s' := by
  cases hs with
  | syscall num a0 a1 a2 a3 a4 => exact .syscall num a0 a1 a2 a3 a4 h
  | tick => exact .tick h
  | fault => exact .fault h
  | clear j => exact .clear j h
  | irq n => exact .irq n h
  | verify i hh => exact .verify i hh h
  | ioFail => exact .ioFail h
  | board a b c d e => exact .board a b c d e h
  | usb v => exact .usb v h
  | enter c b0 b1 b2 => exact .enter c b0 b1 b2 h
  | resched => exact .resched h

/-! ## Waiting senders, and the order a receive looks at them -/

/-- Task `k` is blocked sending to endpoint `e`. -/
def SendingOn (s : KState) (e k : Nat) : Prop :=
  ∃ u m, nth? s.tasks k = some u ∧ u.status = .sending e m

/-- How many tasks a receive on endpoint `e` looks at before task `k`: it starts with the
task after the one `e` served last, and wraps around after the last task. -/
def ahead (s : KState) (e k : Nat) : Nat :=
  (k + numTasks - (lastServed s e + 1) % numTasks) % numTasks

/-- Step `s → s'` takes task `k`'s waiting message on endpoint `e`: it is the running task's
`recv` or `recvt`, through a capability to `e` with the receive right, the search from the
task after the one `e` served last found `k`, and the message was delivered. -/
def Takes (e k : Nat) (s s' : KState) : Prop :=
  ∃ t ci block deadline c m t', nth? s.tasks s.cur = some t ∧ t.status = .ready ∧
    nth? t.caps ci = some c ∧ c.obj = .endpoint e ∧ c.rights.r = true ∧
    findSender e s.tasks (lastServed s e + 1) (len s.tasks) = some (k, m) ∧
    deliver t m k = some t' ∧ s' = (sysRecv s t ci block deadline).state

/-- A run of steps from `s` to `s'` during which task `j` stays blocked sending to endpoint
`e`, in every state of the run (`s` and `s'` too), with `n` steps counted that take a waiting
message on `e`. (A step that takes one need not be counted, so `n` is at most the number of
such steps.) -/
inductive WaitRun (e j : Nat) : KState → Nat → KState → Prop
  | stay {s : KState} : SendingOn s e j → WaitRun e j s 0 s
  | step {s s' s'' : KState} {n : Nat} : SendingOn s e j → Step s s' → WaitRun e j s' n s'' →
      WaitRun e j s n s''
  | take {s s' s'' : KState} {n k : Nat} : SendingOn s e j → Step s s' → Takes e k s s' →
      WaitRun e j s' n s'' → WaitRun e j s (n + 1) s''

theorem WaitRun.head {e j n : Nat} {s s' : KState} (h : WaitRun e j s n s') : SendingOn s e j := by
  cases h <;> assumption

/-! ## The search -/

theorem sendingAt_of {e : Nat} {ts : List Task} {k : Nat} {u : Task} {m : Msg}
    (hu : nth? ts k = some u) (hst : u.status = .sending e m) : sendingAt e ts k = some m := by
  simp [sendingAt, hu, hst, sendingMsg]

theorem sendingOn_iff {s : KState} {e k : Nat} : SendingOn s e k ↔ ∃ m, sendingAt e s.tasks k = some m :=
  ⟨fun ⟨_, m, hu, hst⟩ => ⟨m, sendingAt_of hu hst⟩,
   fun ⟨m, h⟩ => let ⟨u, hu, hst⟩ := sendingAt_spec h; ⟨u, m, hu, hst⟩⟩

/-- What the search finds: the task it reaches after `d` others, blocked sending, and none of
those `d` is. -/
theorem findSender_first {e : Nat} {ts : List Task} : ∀ {i fuel k : Nat} {m : Msg},
    findSender e ts i fuel = some (k, m) →
      ∃ d < fuel, (i + d) % len ts = k ∧ sendingAt e ts k = some m ∧
        ∀ d' < d, sendingAt e ts ((i + d') % len ts) = none
  | _, 0, _, _, h => by simp [findSender] at h
  | i, fuel + 1, k, m, h => by
    simp only [findSender] at h
    split at h
    · rename_i m' hm
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by omega, by simp, hm, fun _ h => by omega⟩
    · rename_i hnone
      obtain ⟨d, hd, hk, hm, hbefore⟩ := findSender_first h
      refine ⟨d + 1, by omega, ?_, hm, fun d' hd' => ?_⟩
      · rwa [Nat.add_assoc, Nat.mod_add_mod, Nat.add_comm 1 d] at hk
      · cases d' with
        | zero => simpa using hnone
        | succ d' =>
          have := hbefore d' (by omega)
          rwa [Nat.add_assoc, Nat.mod_add_mod, Nat.add_comm 1 d', ← Nat.add_assoc] at this

/-- If the search finds nothing, none of the `fuel` tasks it looked at is blocked sending. -/
theorem findSender_none {e : Nat} {ts : List Task} : ∀ {i fuel : Nat},
    findSender e ts i fuel = none → ∀ d < fuel, sendingAt e ts ((i + d) % len ts) = none
  | _, 0, _, d, hd => by omega
  | i, fuel + 1, h, d, hd => by
    simp only [findSender] at h
    split at h
    · simp at h
    · rename_i hnone
      cases d with
      | zero => simpa using hnone
      | succ d =>
        have := findSender_none h d (by omega)
        rwa [Nat.add_assoc, Nat.mod_add_mod, Nat.add_comm 1 d] at this

/-- Task `k` is the one the search reaches after `ahead s e k` others. -/
theorem ahead_spec (s : KState) (e : Nat) {k : Nat} (hk : k < numTasks) :
    ahead s e k < numTasks ∧ (lastServed s e + 1 + ahead s e k) % numTasks = k := by
  unfold ahead; simp only [numTasks] at *; omega

theorem ahead_of {s : KState} {e k d : Nat} (hd : d < numTasks)
    (h : (lastServed s e + 1 + d) % numTasks = k) : ahead s e k = d := by
  unfold ahead; simp only [numTasks] at *; omega

/-! ## Nothing but a receive moves what an endpoint remembers -/

theorem schedule_served (s : KState) : (schedule s).served = s.served := by
  unfold schedule; split <;> rfl

theorem killCurrent_served (s : KState) : (killCurrent s).served = s.served := by
  unfold killCurrent; split <;> exact schedule_served _

/-- Closes `r.state.served = s.served` for a reply whose state is the old one, changed only
in other fields, possibly then rescheduled. -/
local macro "served_leaf" : tactic => `(tactic| first
  | rfl
  | exact (schedule_served _).trans rfl
  | exact (killCurrent_served _).trans rfl)

section calls
variable (s : KState) (t : Task)

theorem sysWrite_served (va n : Nat) : (sysWrite s t va n).state.served = s.served := by
  unfold sysWrite; repeat' split
  all_goals served_leaf

theorem sysMap_served (ci vpn : Nat) : (sysMap s t ci vpn).state.served = s.served := by
  unfold sysMap; repeat' split
  all_goals served_leaf

theorem sysDerive_served (ci bits offset count : Nat) :
    (sysDerive s t ci bits offset count).state.served = s.served := by
  unfold sysDerive; repeat' split
  all_goals served_leaf

theorem sysCapInfo_served (ci : Nat) : (sysCapInfo s t ci).state.served = s.served := by
  unfold sysCapInfo; repeat' split
  all_goals served_leaf

theorem sysSend_served (ci w0 w1 w2 gi : Nat) (call : Bool) :
    (sysSend s t ci w0 w1 w2 gi call).state.served = s.served := by
  unfold sysSend; repeat' (first | split | dsimp only)
  all_goals served_leaf

theorem sysReply_served (slot w0 w1 w2 : Nat) : (sysReply s t slot w0 w1 w2).state.served = s.served := by
  unfold sysReply; repeat' (first | split | dsimp only)
  all_goals served_leaf

theorem sysIrqWait_served (ci : Nat) : (sysIrqWait s t ci).state.served = s.served := by
  unfold sysIrqWait; repeat' split
  all_goals served_leaf

theorem sysIrqAck_served (ci : Nat) : (sysIrqAck s t ci).state.served = s.served := by
  unfold sysIrqAck; repeat' split
  all_goals served_leaf

theorem sysBootInfo_served (i : Nat) : (sysBootInfo s t i).state.served = s.served := by
  unfold sysBootInfo; split
  all_goals served_leaf

theorem sysStart_served (ci src len : Nat) : (sysStart s t ci src len).state.served = s.served := by
  unfold sysStart; repeat' (first | split | dsimp only)
  all_goals served_leaf

theorem sysDrop_served (ci : Nat) : (sysDrop s t ci).state.served = s.served := by
  unfold sysDrop; split
  all_goals served_leaf

theorem sysBlock_served (ci idx va : Nat) (w : Bool) : (sysBlock s t ci idx va w).state.served = s.served := by
  unfold sysBlock; repeat' split
  all_goals served_leaf

theorem sysSleep_served (ms : Nat) : (sysSleep s t ms).state.served = s.served := by
  unfold sysSleep; dsimp only; split
  all_goals served_leaf

theorem sysPower_served (ci a : Nat) : (sysPower s t ci a).state.served = s.served := by
  unfold sysPower; repeat' split
  all_goals served_leaf

theorem sysBoard_served (ci w v : Nat) : (sysBoard s t ci w v).state.served = s.served := by
  unfold sysBoard; repeat' (first | split | dsimp only)
  all_goals served_leaf

theorem sysUsb_served (ci op reg v : Nat) : (sysUsb s t ci op reg v).state.served = s.served := by
  unfold sysUsb usbReply
  split
  · rfl
  · split
    -- a tree of `if`s: cheaper to push the field through than to split
    all_goals first
      | rfl
      | simp only [apply_ite Reply.state, apply_ite KState.served, ret, setTask, ite_self]

theorem sysStop_served (ci : Nat) : (sysStop s t ci).state.served = s.served := by
  unfold sysStop; repeat' split
  all_goals served_leaf

theorem sysSetWall_served (ci secs : Nat) : (sysSetWall s t ci secs).state.served = s.served := by
  unfold sysSetWall; repeat' split
  all_goals served_leaf

end calls

/-- A receive either leaves every endpoint's memory alone or takes a waiting message. -/
theorem sysRecv_served {s : KState} {t : Task} (ht : nth? s.tasks s.cur = some t) (hready : t.status = .ready)
    (ci : Nat) (block : Bool) (deadline : Nat) :
    (sysRecv s t ci block deadline).state.served = s.served ∨
      ∃ e k, Takes e k s (sysRecv s t ci block deadline).state := by
  by_cases H : ∃ e k, Takes e k s (sysRecv s t ci block deadline).state
  · exact Or.inr H
  left
  unfold sysRecv
  split
  · rfl
  · rename_i c hc
    split
    · rename_i e he
      split
      · rename_i hr
        split
        · rename_i k m hk
          split
          · split
            · rename_i t' hd
              exact absurd ⟨e, k, t, ci, block, deadline, c, m, t', ht, hready, hc, he, hr, hk, hd, rfl⟩ H
            · rfl
          · rfl
        · split <;> served_leaf
      · rfl
    · rfl

theorem runCall_served {s : KState} {t : Task} (ht : nth? s.tasks s.cur = some t) (hready : t.status = .ready)
    (num a0 a1 a2 a3 a4 : Nat) :
    (runCall s t num a0 a1 a2 a3 a4).state.served = s.served ∨
      ∃ e k, Takes e k s (runCall s t num a0 a1 a2 a3 a4).state := by
  unfold runCall
  split
  all_goals first
    | exact sysRecv_served ht hready _ _ _
    | left
      first
        | served_leaf
        | exact sysWrite_served .. | exact sysMap_served .. | exact sysDerive_served ..
        | exact sysCapInfo_served .. | exact sysSend_served .. | exact sysReply_served ..
        | exact sysIrqWait_served .. | exact sysIrqAck_served .. | exact sysBootInfo_served ..
        | exact sysStart_served .. | exact sysDrop_served .. | exact sysBlock_served ..
        | exact sysSleep_served .. | exact sysPower_served .. | exact sysBoard_served ..
        | exact sysUsb_served .. | exact sysStop_served .. | exact sysSetWall_served ..

/-- **Only a receive moves what an endpoint remembers.** A step of the kernel either leaves
every endpoint's last-served task as it was, or is a receive that takes a waiting message. -/
theorem served_only_by_recv {s s' : KState} (h : Step s s') :
    s'.served = s.served ∨ ∃ e k, Takes e k s s' := by
  cases h with
  | syscall num a0 a1 a2 a3 a4 =>
    unfold syscall
    split
    · exact Or.inl rfl
    · rename_i t ht
      split
      · rename_i hready
        exact runCall_served ht hready num a0 a1 a2 a3 a4
      · exact Or.inl rfl
  | tick => exact Or.inl (schedule_served _)
  | fault => exact Or.inl (killCurrent_served _)
  | clear j => left; unfold clearResult; split <;> rfl
  | irq n =>
    left; unfold irqFired; repeat' split
    all_goals rfl
  | verify i hh =>
    left; unfold verify; repeat' split
    all_goals rfl
  | ioFail => left; unfold ioFailed; split <;> rfl
  | board => left; unfold boardDone; split <;> rfl
  | usb => left; unfold usbDone; split <;> rfl
  | enter => exact Or.inl rfl
  | resched => exact Or.inl (schedule_served _)

/-! ## A receive takes the next waiting sender in turn -/

theorem nth?_of_lt {α : Type} : ∀ {l : List α} {i : Nat}, i < len l → ∃ a, nth? l i = some a
  | [], _, h => by simp [len] at h
  | a :: _, 0, _ => ⟨a, rfl⟩
  | _ :: l, i + 1, h => by simp only [len] at h; exact nth?_of_lt (l := l) (by omega)

/-- **A receive takes the next waiting sender in turn.** When a receive on endpoint `e` takes
task `k`'s message: `k` was blocked sending to `e`; no task the search looked at before it
(the tasks after the one `e` served last, up to `k`, wrapping around) was; `e` now remembers
`k`, and every other endpoint what it remembered; and `k` is no longer blocked sending. -/
theorem recv_in_turn {s s' : KState} (h : Reachable s) {e k : Nat} (hk : Takes e k s s') :
    SendingOn s e k ∧
      (∀ d < ahead s e k, ¬ SendingOn s e ((lastServed s e + 1 + d) % numTasks)) ∧
      lastServed s' e = k ∧ (∀ e', e' ≠ e → lastServed s' e' = lastServed s e') ∧
      ¬ SendingOn s' e k := by
  obtain ⟨t, ci, block, deadline, c, m, t', ht, hready, hc, he, hr, hf, hd, rfl⟩ := hk
  have hs := reachable_inv h
  have hlen : len s.tasks = numTasks := hs.len
  obtain ⟨d, hd18, hpos, hm, hbefore⟩ := findSender_first hf
  rw [hlen] at hpos hbefore hd18
  have hkd : ahead s e k = d := ahead_of hd18 hpos
  obtain ⟨u, hu, hst⟩ := sendingAt_spec hm
  -- the endpoint is one of the manifest's: its receive right was given at boot
  have hel : e < len s.served := by
    rw [(small_reachable h).served]
    obtain ⟨c0, hc0, ho0, hle0, -⟩ := boot_rights ((hs.tasks _ _ ht).caps c (nth?_mem hc)) he
    rcases recv_owner (hs.lt ht) hc0 ho0 (hle0.1 hr) with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain ⟨v, hv⟩ := nth?_of_lt hel
  have hkc : k ≠ s.cur := by
    rintro rfl; rw [ht] at hu; cases hu; rw [hready] at hst; cases hst
  refine ⟨⟨u, m, hu, hst⟩, fun d' hd' hsend => ?_, ?_, fun e' he' => ?_, ?_⟩
  · obtain ⟨m', hm'⟩ := sendingOn_iff.1 hsend
    rw [hbefore d' (hkd ▸ hd')] at hm'; cases hm'
  all_goals simp only [sysRecv, hc, he, hr, hf, hu, hd, ite_true]
  · simp [lastServed, serve, setTask, nth?_setNth, hv]
  · simp [lastServed, serve, setTask, nth?_setNth, Ne.symm he']
  · rintro ⟨u', m', hu', hst'⟩
    simp only [serve, setTask, nth?_setNth, Ne.symm hkc, if_false, if_true, hu, Option.map_some] at hu'
    cases hu'
    split at hst' <;> cases hst'

/-- **A receive misses nobody.** A receive finds no message to take (and waits, or times
out) only if no task is blocked sending to its endpoint. -/
theorem recv_misses_nobody {s : KState} (h : Reachable s) {e : Nat}
    (hf : findSender e s.tasks (lastServed s e + 1) (len s.tasks) = none) (k : Nat) :
    ¬ SendingOn s e k := by
  intro hsend
  obtain ⟨u, m, hu, hst⟩ := hsend
  have hlen : len s.tasks = numTasks := (reachable_inv h).len
  have hlt : k < numTasks := hlen ▸ nth?_lt hu
  obtain ⟨d, hd, hdk⟩ := hits_every (lastServed s e + 1) k numTasks hlt
  have := findSender_none hf d (by rw [hlen]; exact hd)
  rw [hlen, hdk, sendingAt_of hu hst] at this
  cases this

/-! ## Bounded waiting -/

theorem sendingOn_lt {s : KState} (h : Reachable s) {e j : Nat} (hj : SendingOn s e j) : j < numTasks := by
  obtain ⟨u, m, hu, -⟩ := hj
  exact (reachable_inv h).lt hu

/-- A take on `e` that leaves `j` waiting moves `e`'s search strictly closer to `j`. -/
theorem take_ahead_lt {s s' : KState} (h : Reachable s) {e j k : Nat} (hk : Takes e k s s')
    (hj : SendingOn s e j) (hj' : SendingOn s' e j) : ahead s' e j < ahead s e j := by
  obtain ⟨hsk, hbefore, hlast, -, hgone⟩ := recv_in_turn h hk
  have hjn := sendingOn_lt h hj
  have hkn := sendingOn_lt h hsk
  have hjk : j ≠ k := by rintro rfl; exact hgone hj'
  obtain ⟨-, hjpos⟩ := ahead_spec s e hjn
  obtain ⟨hk18, hkpos⟩ := ahead_spec s e hkn
  have hlt : ahead s e k < ahead s e j := by
    rcases Nat.lt_trichotomy (ahead s e j) (ahead s e k) with hl | hl | hl
    · have := hbefore _ hl; rw [hjpos] at this; exact absurd hj this
    · exact absurd (hjpos.symm.trans (hl ▸ hkpos)) hjk
    · exact hl
  unfold ahead at *
  rw [hlast]
  simp only [numTasks] at *
  omega

/-- No step moves `e`'s search away from a task still waiting. -/
theorem step_ahead_le {s s' : KState} (h : Reachable s) (hs : Step s s') {e j : Nat}
    (hj : SendingOn s e j) (hj' : SendingOn s' e j) : ahead s' e j ≤ ahead s e j := by
  rcases served_only_by_recv hs with hsv | ⟨e', k, hk⟩
  · simp [ahead, lastServed, hsv]
  · by_cases hee : e' = e
    · subst hee; exact Nat.le_of_lt (take_ahead_lt h hk hj hj')
    · obtain ⟨-, -, -, hother, -⟩ := recv_in_turn h hk
      simp [ahead, hother e (Ne.symm hee)]

/-- **Bounded waiting, exactly.** While task `j` stays blocked sending to endpoint `e`, the
receivers on `e` take at most as many messages as the search looks at tasks before `j`. -/
theorem recv_wait_ahead {e j n : Nat} {s s' : KState} (hr : WaitRun e j s n s') (h : Reachable s) :
    n ≤ ahead s e j := by
  induction hr with
  | stay => exact Nat.zero_le _
  | step hj hs hrest ih =>
    exact Nat.le_trans (ih (h.step hs)) (step_ahead_le h hs hj hrest.head)
  | take hj hs hk hrest ih =>
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih (h.step hs)) (take_ahead_lt h hk hj hrest.head))

/-- **Bounded waiting.** While task `j` stays blocked sending to endpoint `e`, its receivers
take fewer than `numTasks` (18) messages on `e`. So once `e` has taken 18 messages, every
task that was waiting to send to it before the first has been served, or has stopped
waiting some other way. -/
theorem recv_bounded_wait {e j n : Nat} {s s' : KState} (h : Reachable s) (hr : WaitRun e j s n s') :
    n < numTasks :=
  Nat.lt_of_le_of_lt (recv_wait_ahead hr h) (ahead_spec s e (sendingOn_lt h hr.head)).1

end LeanOS
