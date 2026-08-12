/-
  AutoproverCorpus.Distributed.LamportClockMonotone

  Lamport's clock condition, in full generality: for an arbitrary event type, an arbitrary
  base relation generating happens-before (e.g. program order within a process plus
  message send-before-receive across processes, closed under transitivity), and an
  arbitrary scalar clock, IF the clock strictly increases across every base edge THEN it
  strictly increases across the whole happens-before relation. This is the theorem
  `hb_imp_clock_lt` below — not tied to any fixed event history or process count.

  As a non-vacuity witness, the general theorem is instantiated at a concrete fixed
  two-process, six-event history with a hand-assigned Lamport scalar clock, recovering the
  clock condition for that instance (`HB_imp_clock_lt`) for free from `hb_imp_clock_lt`.

  This module proves ONLY that one-directional clock condition (general and instance). The
  CONVERSE — `C e < C e'` implies `e` happens-before `e'` — is FALSE for scalar Lamport
  clocks in general: two concurrent (causally unrelated) events can receive different clock
  values purely from unrelated local activity, with no happens-before edge between them
  either way. An explicit counterexample pair from the instance history is exhibited below
  (`clock_lt_not_converse`). This is exactly the gap that motivated vector clocks, whose
  biconditional clock condition is proved in this corpus's `Distributed.VectorClockCausality`,
  not here.

  Attribution: L. Lamport, "Time, Clocks, and the Ordering of Events in a Distributed System",
  1978.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Order.TransitiveClosure

namespace AutoproverCorpus.LamportClockMonotone

open AutoproverCorpus.TransitiveClosure

/-! ### The general theorem: Lamport's clock condition for any event type, base relation,
    and clock -/

/-- **Lamport's clock condition (general form).** For an arbitrary event type `E`, an
    arbitrary base relation `base : E → E → Prop` (e.g. program order union message
    send-before-receive), and an arbitrary clock `C : E → Nat`: if every `base` edge
    strictly increases the clock, then every happens-before edge — `TC base`, the
    transitive closure of `base` — strictly increases the clock too. Proved by induction on
    the `TC` derivation: the base case is the per-edge hypothesis applied directly; the
    transitive case chains the two strict inequalities (`omega` discharges the `Nat.lt_trans`
    step). Not tied to any fixed history, process count, or clock assignment — this is
    Lamport's clock condition in the generality he stated it. -/
theorem hb_imp_clock_lt {E : Type} {base : E → E → Prop} {C : E → Nat}
    (hstep : ∀ a b, base a b → C a < C b) {a b : E} (h : TC base a b) : C a < C b := by
  induction h with
  | base hr => exact hstep _ _ hr
  | trans _ _ ih1 ih2 => omega

/-! ### Non-vacuity witness: a fixed two-process, six-event history -/

/-- The six events of a fixed two-process history: P0's `a0 -> a1 -> a2`, P1's
    `b0 -> b1 -> b2`, with a message sent at `a1` and received at `b1`. -/
inductive Event where
  | a0 | a1 | a2 | b0 | b1 | b2
  deriving DecidableEq

open Event

/-- The base happens-before-generating edges: the 4 program-order successor edges (2 per
    process) plus the 1 message edge (`a1` sends, `b1` receives). `abbrev` so `decide` can
    unfold it. -/
abbrev stepRel : Event → Event → Bool
  | .a0, .a1 => true
  | .a1, .a2 => true
  | .b0, .b1 => true
  | .b1, .b2 => true
  | .a1, .b1 => true
  | _, _ => false

/-- The base edge relation as a `Prop`. -/
abbrev edge (a b : Event) : Prop := stepRel a b = true

/-- Happens-before: the transitive closure of the base edges (program order plus
    send-before-receive) — an instance of the general `TC base` shape at `base := edge`. -/
abbrev HB (a b : Event) : Prop := TC edge a b

/-- Lamport scalar clock values for this fixed history, worked out by hand following
    Lamport's update rule: an internal or send event increments the process's own counter by
    1; a receive event's counter becomes `max(local counter, message counter) + 1`.
    `P0`: `a0 = 1`, `a1 = 2` (send, tags the message with `2`), `a2 = 3`.
    `P1`: `b0 = 1`, `b1 = max(1, 2) + 1 = 3` (receive), `b2 = 4`. -/
abbrev C : Event → Nat
  | .a0 => 1
  | .a1 => 2
  | .a2 => 3
  | .b0 => 1
  | .b1 => 3
  | .b2 => 4

/-- The five base edges, named for reuse. -/
theorem e_a0a1 : edge .a0 .a1 := by decide
theorem e_a1a2 : edge .a1 .a2 := by decide
theorem e_b0b1 : edge .b0 .b1 := by decide
theorem e_b1b2 : edge .b1 .b2 := by decide
theorem e_a1b1 : edge .a1 .b1 := by decide

/-- Every `edge` fact gives an `HB` fact (base case of `TC`). -/
theorem edge_imp_HB {a b : Event} (h : edge a b) : HB a b := TC.base h

/-- The per-edge hypothesis the general theorem needs for this instance: the hand-assigned
    clock strictly increases across every one of the five base edges, checked by a finite
    case split. -/
theorem step_clock_lt : ∀ a b, edge a b → C a < C b := by
  intro a b h; cases a <;> cases b <;> revert h <;> decide

/-- **Lamport clock condition for this instance**, obtained for free by instantiating the
    general theorem `hb_imp_clock_lt` at this history's `edge`, `HB`, and `C` — the
    non-vacuity witness showing the general theorem is not vacuous. -/
theorem HB_imp_clock_lt {a b : Event} (h : HB a b) : C a < C b :=
  hb_imp_clock_lt step_clock_lt h

/-! ### The converse is false: an explicit concurrency counterexample -/

/-- `b0` and `a2` are NOT related by happens-before in either direction — they are
    concurrent (no chain of edges connects them either way) — yet the scalar clock strictly
    orders them (`C b0 = 1 < C a2 = 3`). This is the standard counterexample showing scalar
    Lamport clocks do not characterize causality: `C e < C e'` does NOT imply `e` happens-before
    `e'`. A concrete, decidable "reachability table" is used only as a finite pivot to rule
    out `HB` in both directions for this one pair; it is not claimed to be the general
    reflexive-transitive-closure algorithm. -/
abbrev reach : Event → Event → Bool
  | .a0, .a1 => true
  | .a0, .a2 => true
  | .a0, .b1 => true
  | .a0, .b2 => true
  | .a1, .a2 => true
  | .a1, .b1 => true
  | .a1, .b2 => true
  | .b0, .b1 => true
  | .b0, .b2 => true
  | .b1, .b2 => true
  | _, _ => false

theorem edge_imp_reach : ∀ a b, edge a b → reach a b = true := by
  intro a b; cases a <;> cases b <;> decide

theorem reach_trans : ∀ a b c, reach a b = true → reach b c = true → reach a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

theorem HB_imp_reach {a b : Event} (h : HB a b) : reach a b = true :=
  tc_least edge_imp_reach reach_trans h

/-- `b0` and `a2` are concurrent: `reach` (an over-approximation of `HB`, since `HB` implies
    `reach`) is false in both directions for this pair, so `HB` is false in both directions
    too. -/
theorem b0_a2_concurrent : ¬ HB .b0 .a2 ∧ ¬ HB .a2 .b0 := by
  constructor
  · intro h; exact absurd (HB_imp_reach h) (by decide)
  · intro h; exact absurd (HB_imp_reach h) (by decide)

/-- The converse-failure witness: `b0` and `a2` are concurrent, yet `C b0 < C a2`. -/
theorem clock_lt_not_converse : (¬ HB .b0 .a2 ∧ ¬ HB .a2 .b0) ∧ C .b0 < C .a2 :=
  ⟨b0_a2_concurrent, by decide⟩

end AutoproverCorpus.LamportClockMonotone
