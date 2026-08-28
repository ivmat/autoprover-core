/-
  AutoproverCorpus.Distributed.VectorClockCausality

  Vector clocks characterize causality: the vector-clock order holds between two events iff the
  first happens-before the second, with a concurrency witness (two incomparable events, neither
  clock dominating).

  Attribution: Classical (Fidge, 1988; Mattern, 1989).

  SCOPE NOTE. Everything below is about ONE fixed history: six events over two processes, with
  five base edges, and a vector clock assigned to each event BY HAND (following the Fidge/Mattern
  update rule, but not computed by a formalized version of it). The strong clock condition is
  established for that history by finite case checking, not for an arbitrary history under an
  arbitrary clock assignment — the general Fidge/Mattern characterization is not proved here.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Order.TransitiveClosure

namespace AutoproverCorpus.VectorClockCausality

open AutoproverCorpus.TransitiveClosure

/-- The six events of the fixed two-process history: P0's `a0 -> a1 -> a2`, P1's
    `b0 -> b1 -> b2`, with a message from `a1` received at `b1`. -/
inductive Event where
  | a0 | a1 | a2 | b0 | b1 | b2
  deriving DecidableEq

open Event

/-- The base causal-edge relation: the 4 program-order successor edges plus the 1
    message edge (a1 sends, b1 receives). `abbrev` so `decide` can unfold it. -/
abbrev stepRel : Event → Event → Bool
  | .a0, .a1 => true
  | .a1, .a2 => true
  | .b0, .b1 => true
  | .b1, .b2 => true
  | .a1, .b1 => true
  | _, _ => false

/-- The base edge relation as a `Prop`. -/
abbrev edge (a b : Event) : Prop := stepRel a b = true

abbrev HB (a b : Event) : Prop := TC edge a b

/-- Vector clock assignment, by hand, following the Fidge/Mattern update rule for this
    fixed history (worked out in the header comment above). Component 0 = P0's counter,
    component 1 = P1's counter. -/
abbrev VC : Event → Nat × Nat
  | .a0 => (1, 0)
  | .a1 => (2, 0)
  | .a2 => (3, 0)
  | .b0 => (0, 1)
  | .b1 => (2, 2)
  | .b2 => (2, 3)

/-- Componentwise `<=` on vector clocks. -/
abbrev vc_le (x y : Nat × Nat) : Prop := x.1 ≤ y.1 ∧ x.2 ≤ y.2

/-- The Strong Clock Condition's ordering: componentwise `<=`, strict somewhere — exactly
    the parenthetical in the spec. -/
abbrev vc_lt (x y : Nat × Nat) : Prop := vc_le x y ∧ (x.1 < y.1 ∨ x.2 < y.2)

/-- `vc_lt` is transitive: componentwise `<=` composes by `Nat` transitivity, and
    "strict somewhere" survives composition (pure linear arithmetic, closed by `omega`). -/
theorem vc_lt_trans {x y z : Nat × Nat} (h1 : vc_lt x y) (h2 : vc_lt y z) : vc_lt x z := by
  obtain ⟨⟨hx1, hx2⟩, hxs⟩ := h1
  obtain ⟨⟨hy1, hy2⟩, hys⟩ := h2
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-- The five base edges, named for reuse in explicit `HB` derivations below. -/
theorem e_a0a1 : edge .a0 .a1 := by decide
theorem e_a1a2 : edge .a1 .a2 := by decide
theorem e_b0b1 : edge .b0 .b1 := by decide
theorem e_b1b2 : edge .b1 .b2 := by decide
theorem e_a1b1 : edge .a1 .b1 := by decide

/-- Every `edge` fact gives an `HB` fact (base case of `TC`). -/
theorem edge_imp_HB {a b : Event} (h : edge a b) : HB a b := TC.base h

/-- Every `HB` fact gives a `vc_lt` fact — the FORWARD direction of the Strong Clock
    Condition (`hb → clock-strict`), by induction on the `TC` derivation: the base case is
    a finite check per concrete edge, the `trans` case composes via `vc_lt_trans`. -/
theorem HB_imp_vc_lt {a b : Event} (h : HB a b) : vc_lt (VC a) (VC b) := by
  induction h with
  | @base a b hr => cases a <;> cases b <;> revert hr <;> decide
  | @trans a b c hab hbc ih1 ih2 => exact vc_lt_trans ih1 ih2

/-- A concrete, decidable "reachability table" for this fixed 6-event history: exactly the
    10 ordered pairs actually connected by a chain of `edge`s. Used only as a finite pivot
    to close the BACKWARD direction; not claimed to be the general reflexive-transitive
    closure algorithm. `abbrev` so `decide` unfolds it. -/
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

/-- Every `edge` fact is in `reach` (containment, checked per concrete pair since `edge` and
    `reach` are both decidable Bool tables). -/
theorem edge_imp_reach : ∀ a b, edge a b → reach a b = true := by
  intro a b; cases a <;> cases b <;> decide

/-- `reach` is transitive over this finite 6-event `Event` type — a brute finite check over
    all 216 triples, each closed instantly by `decide` on concrete `Bool` tables. -/
theorem reach_trans : ∀ a b c, reach a b = true → reach b c = true → reach a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

theorem HB_imp_reach {a b : Event} (h : HB a b) : reach a b = true :=
  tc_least edge_imp_reach reach_trans h

/-- `reach a b = true → HB a b`: the converse containment, proved by exhibiting an explicit
    `TC`-derivation (chain of `edge_imp_HB`/`TC.trans`) for each of the 10 true pairs, and
    deriving `False` from `h` for every other (false) pair. Full case enumeration — no
    cleverness, a plain finite-table style. -/
theorem reach_imp_HB : ∀ a b, reach a b = true → HB a b
  | .a0, .a0, h => absurd h (by decide)
  | .a0, .a1, _ => edge_imp_HB e_a0a1
  | .a0, .a2, _ => TC.trans (edge_imp_HB e_a0a1) (edge_imp_HB e_a1a2)
  | .a0, .b0, h => absurd h (by decide)
  | .a0, .b1, _ => TC.trans (edge_imp_HB e_a0a1) (edge_imp_HB e_a1b1)
  | .a0, .b2, _ =>
      TC.trans (TC.trans (edge_imp_HB e_a0a1) (edge_imp_HB e_a1b1)) (edge_imp_HB e_b1b2)
  | .a1, .a0, h => absurd h (by decide)
  | .a1, .a1, h => absurd h (by decide)
  | .a1, .a2, _ => edge_imp_HB e_a1a2
  | .a1, .b0, h => absurd h (by decide)
  | .a1, .b1, _ => edge_imp_HB e_a1b1
  | .a1, .b2, _ => TC.trans (edge_imp_HB e_a1b1) (edge_imp_HB e_b1b2)
  | .a2, .a0, h => absurd h (by decide)
  | .a2, .a1, h => absurd h (by decide)
  | .a2, .a2, h => absurd h (by decide)
  | .a2, .b0, h => absurd h (by decide)
  | .a2, .b1, h => absurd h (by decide)
  | .a2, .b2, h => absurd h (by decide)
  | .b0, .a0, h => absurd h (by decide)
  | .b0, .a1, h => absurd h (by decide)
  | .b0, .a2, h => absurd h (by decide)
  | .b0, .b0, h => absurd h (by decide)
  | .b0, .b1, _ => edge_imp_HB e_b0b1
  | .b0, .b2, _ => TC.trans (edge_imp_HB e_b0b1) (edge_imp_HB e_b1b2)
  | .b1, .a0, h => absurd h (by decide)
  | .b1, .a1, h => absurd h (by decide)
  | .b1, .a2, h => absurd h (by decide)
  | .b1, .b0, h => absurd h (by decide)
  | .b1, .b1, h => absurd h (by decide)
  | .b1, .b2, _ => edge_imp_HB e_b1b2
  | .b2, .a0, h => absurd h (by decide)
  | .b2, .a1, h => absurd h (by decide)
  | .b2, .a2, h => absurd h (by decide)
  | .b2, .b0, h => absurd h (by decide)
  | .b2, .b1, h => absurd h (by decide)
  | .b2, .b2, h => absurd h (by decide)

/-- `reach a b = true ↔ HB a b`. -/
theorem reach_iff_HB (a b : Event) : reach a b = true ↔ HB a b :=
  ⟨reach_imp_HB a b, HB_imp_reach⟩

/-- `reach a b = true ↔ vc_lt (VC a) (VC b)` — a purely numeric, finite check: with `VC`
    concrete on every event, `vc_lt (VC a) (VC b)` is a decidable `Nat`-comparison fact, and
    it is checked to agree with the `reach` table on all 36 ordered pairs. This is the
    numeric leg that, combined with `reach_iff_HB`, gives the Strong Clock Condition. -/
theorem reach_iff_vc_lt (a b : Event) : reach a b = true ↔ vc_lt (VC a) (VC b) := by
  cases a <;> cases b <;> decide

theorem strong_clock_condition (a b : Event) : HB a b ↔ vc_lt (VC a) (VC b) :=
  (reach_iff_HB a b).symm.trans (reach_iff_vc_lt a b)

theorem concurrency_separating_witness :
    (¬ HB .a2 .b1 ∧ ¬ HB .b1 .a2) ∧ (¬ vc_le (VC .a2) (VC .b1) ∧ ¬ vc_le (VC .b1) (VC .a2)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro h; exact absurd ((strong_clock_condition .a2 .b1).mp h) (by decide)
  · intro h; exact absurd ((strong_clock_condition .b1 .a2).mp h) (by decide)
  · decide
  · decide

end AutoproverCorpus.VectorClockCausality
