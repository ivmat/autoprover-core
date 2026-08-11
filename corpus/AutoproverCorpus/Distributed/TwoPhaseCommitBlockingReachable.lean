/-
  AutoproverCorpus.Distributed.TwoPhaseCommitBlockingReachable

  Two-phase commit blocking as a REACHABLE execution of the explicit state machine, with the
  crash as an event of the machine rather than a missing case.

  Attribution: Classical (Gray, 1978; Skeen, 1981).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.TwoPhaseCommitMachine

namespace AutoproverCorpus.TwoPhaseCommitBlockingReachable

open AutoproverCorpus.TwoPhaseCommitMachine

/-! ### The trace: two participants prepare, then the coordinator crashes before collecting
    or deciding anything. -/

def s0 : GlobalState P2 := initState P2

def s1 : GlobalState P2 :=
  { s0 with
    pstate := fun q => if q = (0 : P2) then PState.prepared else s0.pstate q
    inFlight := Msg.vote 0 Vote.yes :: s0.inFlight }

theorem step_s0_s1 : Step participants2 s0 s1 :=
  Step.partVote 0 Vote.yes (by decide)

def s2 : GlobalState P2 :=
  { s1 with
    pstate := fun q => if q = (1 : P2) then PState.prepared else s1.pstate q
    inFlight := Msg.vote 1 Vote.yes :: s1.inFlight }

theorem step_s1_s2 : Step participants2 s1 s2 :=
  Step.partVote 1 Vote.yes (by decide)

/-- **The reached blocked configuration.** Coordinator crashes with nothing collected and
    nothing logged — the real, reachable crash EVENT (`Step.coordCrash`), not an absent
    constructor. -/
def blocked : GlobalState P2 := { s2 with cstate := CState.crashed }

theorem step_s2_blocked : Step participants2 s2 blocked :=
  Step.coordCrash

/-- **`blocked` is genuinely REACHED**: a real three-step derivation from `initState`. -/
theorem blocked_reachable : Reachable participants2 blocked :=
  Reachable.step
    (Reachable.step (Reachable.step Reachable.init step_s0_s1) step_s1_s2)
    step_s2_blocked

theorem blocked_prepared0 : blocked.pstate 0 = PState.prepared := by decide

theorem blocked_prepared1 : blocked.pstate 1 = PState.prepared := by decide

theorem blocked_crashed : blocked.cstate = CState.crashed := by decide

theorem blocked_clog_none : blocked.clog = none := by decide

theorem blocked_inFlight :
    blocked.inFlight = [Msg.vote 1 Vote.yes, Msg.vote 0 Vote.yes] := by decide

/-! ### 1. The blocking result, at the reached config -/

/-- No decision message of any kind sits in `inFlight` at `blocked` — nothing was ever
    broadcast, since the coordinator crashed before deciding. This is a concrete fact about
    the reached state's own field, not an absent case. -/
theorem blocked_no_decision_msg (p : P2) (d : Decision) :
    Msg.decision p d ∉ blocked.inFlight := by
  rw [blocked_inFlight]
  intro hmem
  rw [List.mem_cons, List.mem_cons] at hmem
  rcases hmem with h | h | h
  · cases h
  · cases h
  · cases h

theorem no_enabled_decide {p : P2} (hprep : blocked.pstate p = PState.prepared) :
    ¬ ∃ s', Step participants2 blocked s' ∧
      (s'.pstate p = PState.committed ∨ s'.pstate p = PState.aborted) := by
  rintro ⟨s', hst, hcase⟩
  cases hst with
  | partVote q _ _ =>
      dsimp only at hcase
      by_cases hpq : p = q
      · rw [if_pos hpq] at hcase
        rcases hcase with h | h <;> exact absurd h (by decide)
      · rw [if_neg hpq] at hcase
        rw [hprep] at hcase
        rcases hcase with h | h <;> exact absurd h (by decide)
  | coordCollect _ _ _ _ =>
      dsimp only at hcase
      rw [hprep] at hcase
      rcases hcase with h | h <;> exact absurd h (by decide)
  | coordDecideCommit hcollecting _ =>
      rw [blocked_crashed] at hcollecting
      exact absurd hcollecting (by decide)
  | coordDecideAbort hcollecting _ =>
      rw [blocked_crashed] at hcollecting
      exact absurd hcollecting (by decide)
  | coordCrash =>
      dsimp only at hcase
      rw [hprep] at hcase
      rcases hcase with h | h <;> exact absurd h (by decide)
  | coordRecoverToLogged _ hlog =>
      rw [blocked_clog_none] at hlog
      cases hlog
  | coordRecoverToCollecting _ _ =>
      dsimp only at hcase
      rw [hprep] at hcase
      rcases hcase with h | h <;> exact absurd h (by decide)
  | deliverDecision q d hmem _ =>
      exact blocked_no_decision_msg q d hmem

/-! ### 2. The contrast: recovery re-drives the SAME votes and the SAME participant decides -/

def recovered : GlobalState P2 := { blocked with cstate := CState.collecting }

theorem step_blocked_recovered : Step participants2 blocked recovered :=
  Step.coordRecoverToCollecting (by decide) (by decide)

/-- The recovered coordinator re-collects participant 0's vote — the SAME message that has
    sat in `inFlight`, unconsumed, since before the crash. -/
def re_collected0 : GlobalState P2 :=
  { recovered with
    votes := fun q => if q = (0 : P2) then some Vote.yes else recovered.votes q }

theorem step_recovered_re_collected0 : Step participants2 recovered re_collected0 :=
  Step.coordCollect 0 Vote.yes (by decide) (by decide)

/-- ...and participant 1's vote likewise. -/
def re_collected1 : GlobalState P2 :=
  { re_collected0 with
    votes := fun q => if q = (1 : P2) then some Vote.yes else re_collected0.votes q }

theorem step_re_collected0_re_collected1 : Step participants2 re_collected0 re_collected1 :=
  Step.coordCollect 1 Vote.yes (by decide) (by decide)

theorem re_collected1_allYes :
    ∀ p ∈ participants2, re_collected1.votes p = some Vote.yes := by decide

/-- The re-driven coordinator now decides COMMIT (both re-collected votes are `yes`) and
    broadcasts fresh decision messages. -/
def re_decided : GlobalState P2 :=
  { re_collected1 with
    cstate := CState.decided Decision.commit
    clog := some Decision.commit
    inFlight :=
      re_collected1.inFlight ++ participants2.map (fun p => Msg.decision p Decision.commit) }

theorem step_re_collected1_re_decided : Step participants2 re_collected1 re_decided :=
  Step.coordDecideCommit (by decide) re_collected1_allYes

/-- Participant 0 — the SAME participant that was stuck at `blocked` — receives the fresh
    decision and genuinely commits. -/
def re_delivered0 : GlobalState P2 :=
  { re_decided with
    pstate := fun q =>
      if q = (0 : P2) then
        (if Decision.commit = Decision.commit then PState.committed else PState.aborted)
      else re_decided.pstate q }

theorem step_re_decided_re_delivered0 : Step participants2 re_decided re_delivered0 :=
  Step.deliverDecision 0 Decision.commit (by decide) (by decide)

/-- **`re_delivered0` is genuinely REACHED from `blocked`**: five further real `Step`s,
    recovery included. -/
theorem re_delivered0_reachable : Reachable participants2 re_delivered0 :=
  Reachable.step
    (Reachable.step
      (Reachable.step
        (Reachable.step
          (Reachable.step blocked_reachable step_blocked_recovered)
          step_recovered_re_collected0)
        step_re_collected0_re_collected1)
      step_re_collected1_re_decided)
    step_re_decided_re_delivered0

/-- **THE CONTRAST, concretely.** The participant that `no_enabled_decide` shows CANNOT
    decide at `blocked` DOES decide once the coordinator recovers and re-drives. -/
theorem re_delivered0_committed : re_delivered0.pstate 0 = PState.committed := by decide

/-! ### 3. Bundled: blocked under crash, live under recovery -/

theorem blocked_then_live :
    Reachable participants2 blocked ∧
    blocked.pstate 0 = PState.prepared ∧
    (¬ ∃ s', Step participants2 blocked s' ∧
      (s'.pstate 0 = PState.committed ∨ s'.pstate 0 = PState.aborted)) ∧
    Reachable participants2 re_delivered0 ∧
    re_delivered0.pstate 0 = PState.committed :=
  ⟨blocked_reachable, blocked_prepared0, no_enabled_decide blocked_prepared0,
    re_delivered0_reachable, re_delivered0_committed⟩

end AutoproverCorpus.TwoPhaseCommitBlockingReachable
