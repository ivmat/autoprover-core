/-
  AutoproverCorpus.Processes.DiagnosabilityUnbounded

  Non-diagnosability for ALL bounds: an automaton whose fault is followed only by unobservable
  events is not N-diagnosable for any N.

  Attribution: Classical (Sampath et al., 1995); unbounded negative form.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Processes.Diagnosability

namespace AutoproverCorpus.DiagnosabilityUnbounded

open AutoproverCorpus.Diagnosability

/-! ### The looping automaton -/

/-- Two states: `init` (before the fault) and `looped` (after the fault, or after the
    matching fault-free unobservable step — both branches land here, since the self-loop
    keeps re-entering the same state). -/
inductive LState where
  | init | looped
deriving DecidableEq

/-- Two events: `fault` (the distinguished fault event) and `tau` (an unobservable event
    usable both as the fault-free alternative at `init` and as the self-loop at `looped`). -/
inductive LEvent where
  | fault | tau
deriving DecidableEq

/-- Both events are unobservable — the alphabet split that makes the fault permanently
    invisible. -/
def observableNone : LEvent → Bool
  | _ => false

def isFaultLoop : LEvent → Bool
  | .fault => true
  | .tau => false

/-- `init --fault--> looped`, `init --tau--> looped` (the fault-free alternative at the
    SAME step), and `looped --tau--> looped` (the unobservable self-loop that lets the
    fault branch run arbitrarily long while staying indistinguishable from the fault-free
    branch, which also self-loops at `looped` after its first `tau`). -/
inductive loopStep : LState → LEvent → LState → Prop where
  | faultStep : loopStep .init .fault .looped
  | branchStep : loopStep .init .tau .looped
  | selfLoop : loopStep .looped .tau .looped

/-! ### (a)-(d) The arbitrarily-long run family, for every `N` -/

/-- The fault run of post-fault length `N`: `fault` followed by `N` copies of `tau`,
    chasing the self-loop. -/
def faultRunEvents (N : Nat) : List LEvent :=
  .fault :: List.replicate N .tau

/-- The fault-free run of the SAME length `N + 1`: `N + 1` copies of `tau` (the first
    `tau` takes the `branchStep`, the rest chase the self-loop). -/
def faultFreeRunEvents (N : Nat) : List LEvent :=
  List.replicate (N + 1) .tau

/-- `looped --(replicate N tau)--> looped`, for every `N`, by induction chasing the
    self-loop. -/
theorem reach_replicate_tau (N : Nat) : Reach loopStep .looped (List.replicate N .tau) .looped := by
  induction N with
  | zero => exact Reach.nil _
  | succ n ih =>
    rw [List.replicate_succ]
    exact Reach.cons loopStep.selfLoop ih

/-- The fault run is a run from `init`, for every `N`. -/
theorem loop_faultRun (N : Nat) : Run loopStep .init (faultRunEvents N) :=
  ⟨.looped, Reach.cons loopStep.faultStep (reach_replicate_tau N)⟩

/-- The fault-free run is a run from `init`, for every `N`. -/
theorem loop_faultFreeRun (N : Nat) : Run loopStep .init (faultFreeRunEvents N) := by
  refine ⟨.looped, ?_⟩
  show Reach loopStep .init (.tau :: List.replicate N .tau) .looped
  exact Reach.cons loopStep.branchStep (reach_replicate_tau N)

/-- The fault run qualifies as `FaultThenN N`, for every `N`: the fault event is followed
    by exactly `N` further events. -/
theorem loop_faultRun_FaultThenN (N : Nat) :
    FaultThenN isFaultLoop N (faultRunEvents N) :=
  ⟨[], .fault, List.replicate N .tau, rfl, rfl, by simp [List.length_replicate]⟩

/-- The fault-free run never contains a fault event, for every `N`: it is made entirely
    of `tau`s. -/
theorem loop_faultFreeRun_isFaultFree (N : Nat) :
    FaultFree isFaultLoop (faultFreeRunEvents N) := by
  intro e he
  have : e = .tau := List.eq_of_mem_replicate he
  subst this
  rfl

/-- Both runs project to `[]` under the all-unobservable alphabet, for every `N`: neither
    contains an observable event. -/
theorem loop_same_projection (N : Nat) :
    proj observableNone (faultRunEvents N) = proj observableNone (faultFreeRunEvents N) := by
  have hfault : proj observableNone (faultRunEvents N) = [] := by
    unfold faultRunEvents proj
    induction N with
    | zero => rfl
    | succ n _ih => simp [List.replicate_succ, observableNone]
  have hfree : proj observableNone (faultFreeRunEvents N) = [] := by
    unfold faultFreeRunEvents proj
    induction N with
    | zero => rfl
    | succ n _ih => simp [List.replicate_succ, observableNone]
  rw [hfault, hfree]

/-! ### (e) The payoff: not N-diagnosable, for EVERY N -/

theorem loop_not_diagnosable_any_N :
    ∀ N, ¬ NDiagnosable loopStep .init observableNone isFaultLoop N := by
  intro N h
  exact (h _ (loop_faultRun N) (loop_faultRun_FaultThenN N)
      _ (loop_faultFreeRun N) (loop_faultFreeRun_isFaultFree N))
    (loop_same_projection N)

/-! ### (f) Instances: the machinery does not trivially refute everything -/

theorem pos_still_diagnosable : NDiagnosable posStep .s0 observable3 isFault3 1 :=
  posDiagnosable

end AutoproverCorpus.DiagnosabilityUnbounded
