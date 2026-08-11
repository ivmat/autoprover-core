/-
  AutoproverCorpus.Distributed.ConsistentCut

  A cut is consistent iff it is closed under happens-before: no message is received inside the
  cut but sent outside it.

  Attribution: Classical (Chandy and Lamport, 1985; Mattern, 1989).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.VectorClockCausality

namespace AutoproverCorpus.ConsistentCut

open AutoproverCorpus.TransitiveClosure
open AutoproverCorpus.VectorClockCausality

/-- A predicate `P` is down-closed under a relation `r`: every `r`-predecessor of a
    `P`-element is itself a `P`-element. `abbrev` so `decide` can
    unfold it in the concrete examples below. -/
abbrev DownClosed {α : Type} (r : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ a b, r a b → P b → P a

/-- **The general bridge lemma.** For any relation `r` and predicate `P` over any type, `P`
    is down-closed under `TC r` iff it is down-closed under `r` itself.
    - `⇒`: immediate, since `r ⊆ TC r` (`TC.base`) — a `TC r`-down-closed `P` is in
      particular down-closed at every `r`-edge.
    - `⇐`: induction on the `TC r` derivation. Base case: exactly the `r`-down-closed
      hypothesis. `trans` case: compose the two inductive hypotheses (down-closedness
      threads through the middle point of the composed chain). -/
theorem tc_downClosed_iff_downClosed {α : Type} (r : α → α → Prop) (P : α → Prop) :
    DownClosed (TC r) P ↔ DownClosed r P := by
  constructor
  · intro h a b hr hb
    exact h a b (TC.base hr) hb
  · intro h a b hab
    induction hab with
    | base hr => intro hb; exact h _ _ hr hb
    | trans hac hcb ih1 ih2 => intro hb; exact ih1 (ih2 hb)

abbrev IsConsistentCut (InCut : Event → Prop) : Prop := DownClosed edge InCut

/-- `InCut` is happens-before-closed iff no event in the cut has an `HB`-predecessor outside
    it — down-closedness under the FULL transitive `HB` relation, not just the generating
    edges. -/
abbrev IsHBClosed (InCut : Event → Prop) : Prop := DownClosed HB InCut

theorem consistentCut_iff_hbClosed (InCut : Event → Prop) :
    IsConsistentCut InCut ↔ IsHBClosed InCut :=
  (tc_downClosed_iff_downClosed edge InCut).symm

theorem consistentCut_no_orphan_message {InCut : Event → Prop} (h : IsConsistentCut InCut)
    (hb1 : InCut .b1) : InCut .a1 :=
  h .a1 .b1 e_a1b1 hb1

section Instances

abbrev orphanCut : Event → Bool
  | .b1 => true
  | _ => false

/-- `orphanCut` as the `Prop`-valued cut predicate `IsConsistentCut` expects. -/
abbrev orphanCutProp (e : Event) : Prop := orphanCut e = true

/-- The orphan cut is genuinely inconsistent: it contains the receive `b1` but not the
    matching send `a1`, so it fails edge-down-closedness — the textbook Chandy–Lamport
    violation, exhibited concretely rather than merely claimed. -/
theorem orphanCut_not_consistent : ¬ IsConsistentCut orphanCutProp := by
  intro h
  have ha1 : orphanCutProp .a1 := h .a1 .b1 e_a1b1 (by decide)
  revert ha1
  decide

abbrev goodCut : Event → Bool
  | .a0 => true
  | .a1 => true
  | .b0 => true
  | _ => false

/-- `goodCut` as the `Prop`-valued cut predicate `IsConsistentCut` expects. -/
abbrev goodCutProp (e : Event) : Prop := goodCut e = true

/-- The good cut is genuinely consistent: a finite check over all `edge b → InCut b → InCut a`
    obligations on the 6-event graph, closed by `decide`. -/
theorem goodCut_consistent : IsConsistentCut goodCutProp := by
  intro a b
  cases a <;> cases b <;> decide

end Instances

end AutoproverCorpus.ConsistentCut
