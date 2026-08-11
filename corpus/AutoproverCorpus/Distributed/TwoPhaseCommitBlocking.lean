/-
  AutoproverCorpus.Distributed.TwoPhaseCommitBlocking

  The blocking flaw of two-phase commit: under coordinator crash after prepare, a participant
  can remain undecided forever.

  Attribution: Classical (Gray, 1978; Skeen, 1981).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.TwoPhaseCommitBlocking

/-- A participant's local state. -/
inductive PState where
  | working
  | prepared
  | committed
  | aborted
  deriving DecidableEq, Repr

inductive Decision where
  | commit
  | abort
  deriving DecidableEq, Repr

/-- The participant transition relation, parameterized by the (possibly absent)
    coordinator message. THREE constructors, no more: `vote` needs no message; `onCommit`
    / `onAbort` fire ONLY under the matching message. There is deliberately NO
    constructor for `Step none .prepared _` — a `prepared` participant has no move at
    all without a message, which is the whole content of the blocking result below. -/
inductive Step : Option Decision → PState → PState → Prop where
  | vote : Step none .working .prepared
  | onCommit : Step (some Decision.commit) .prepared .committed
  | onAbort : Step (some Decision.abort) .prepared .aborted

/-- Reachability via PARTICIPANT-ONLY steps — i.e. the steps available under a
    permanently crashed coordinator (no decision message ever delivered, modeled as
    every step in the chain using `Step none`). -/
inductive ReachableNoMsg (init : PState) : PState → Prop where
  | refl : ReachableNoMsg init init
  | step {s s' : PState} (hr : ReachableNoMsg init s) (hst : Step none s s') :
      ReachableNoMsg init s'

/-! ### (a) The blocking theorem -/

/-- **THE BLOCKING THEOREM.** From `.prepared`, every state reachable by
    participant-only steps IS `.prepared` — under a crashed coordinator (no decision
    message ever delivered), a `prepared` participant never decides. By induction on the
    reachability derivation: `refl` is trivial; a further `step` would need
    `Step none .prepared s'`, which has NO constructor (`vote` only applies FROM
    `.working`; `onCommit`/`onAbort` need `some _`, not `none`) — so no such step exists,
    closing that case immediately. -/
theorem blocking {s : PState} (h : ReachableNoMsg .prepared s) : s = .prepared := by
  induction h with
  | refl => rfl
  | step hprev hst ih =>
    rw [ih] at hst
    cases hst

/-- Direct corollary: `committed` is never participant-only reachable from `prepared`. -/
theorem committed_not_reachable_without_message :
    ¬ ReachableNoMsg PState.prepared PState.committed := by
  intro h
  exact absurd (blocking h) (by decide)

/-- Direct corollary: `aborted` is never participant-only reachable from `prepared`. -/
theorem aborted_not_reachable_without_message :
    ¬ ReachableNoMsg PState.prepared PState.aborted := by
  intro h
  exact absurd (blocking h) (by decide)

/-! ### (b) The contrast: with a live coordinator, the participant DOES decide -/

/-- With a live coordinator delivering `commit`, a `prepared` participant moves to
    `committed` — a genuine transition, not something the model structurally forbids in
    general; it is only the message-free (`ReachableNoMsg`) path that is stuck. -/
theorem commits_with_message : Step (some Decision.commit) .prepared .committed :=
  Step.onCommit

/-- Likewise for `abort`. -/
theorem aborts_with_message : Step (some Decision.abort) .prepared .aborted :=
  Step.onAbort

/-- The transition under a live coordinator genuinely LEAVES `prepared` — this is what
    makes (a) a real liveness failure and not a modelling artifact where the participant
    is simply frozen no matter what happens. -/
theorem not_frozen_in_general :
    ∃ s', Step (some Decision.commit) PState.prepared s' ∧ s' ≠ PState.prepared :=
  ⟨PState.committed, Step.onCommit, by decide⟩

/-! ### (c) Instances -/

/-- The blocked state is genuinely reachable in the real protocol, not an unreachable
    corner of the model: a participant votes (`working → prepared`) via an ordinary
    participant-only step. -/
theorem working_reaches_prepared : ReachableNoMsg PState.working PState.prepared :=
  ReachableNoMsg.step ReachableNoMsg.refl Step.vote

/-- `.prepared` participant-only-reaches itself (the degenerate zero-step case), stated
    concretely — the base case the blocking theorem's induction actually starts from. -/
example : ReachableNoMsg PState.prepared PState.prepared := ReachableNoMsg.refl

end AutoproverCorpus.TwoPhaseCommitBlocking
