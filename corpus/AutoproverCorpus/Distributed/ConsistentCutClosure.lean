/-
  AutoproverCorpus.Distributed.ConsistentCutClosure

  Consistent cuts are closed under intersection and union: the intersection and the union of two
  happens-before-closed cuts are themselves happens-before-closed, with the empty and full cuts
  as bottom and top, and separating witnesses for an incomparable pair. Closure only - the
  lattice laws (absorption, distributivity) are not proved here.

  Attribution: Classical (Mattern, 1989); closure-under-meet-and-join face.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.ConsistentCut

namespace AutoproverCorpus.ConsistentCutClosure

open AutoproverCorpus.TransitiveClosure
open AutoproverCorpus.VectorClockCausality
open AutoproverCorpus.ConsistentCut

section General

variable {α : Type} {r : α → α → Prop} {P Q : α → Prop}

/-- **GENERAL LEMMA 1 (meet/`∩`).** For any relation `r` and predicates `P`, `Q` over any type,
    if both are down-closed under `r`, so is their conjunction. -/
theorem downClosed_inter (hP : DownClosed r P) (hQ : DownClosed r Q) :
    DownClosed r (fun x => P x ∧ Q x) := by
  intro a b hr hb
  exact ⟨hP a b hr hb.1, hQ a b hr hb.2⟩

/-- **GENERAL LEMMA 2 (join/`∪`).** For any relation `r` and predicates `P`, `Q` over any type,
    if both are down-closed under `r`, so is their disjunction. -/
theorem downClosed_union (hP : DownClosed r P) (hQ : DownClosed r Q) :
    DownClosed r (fun x => P x ∨ Q x) := by
  intro a b hr hb
  cases hb with
  | inl hb => exact Or.inl (hP a b hr hb)
  | inr hb => exact Or.inr (hQ a b hr hb)

/-- **GENERAL LEMMA 3 (bottom).** The always-false predicate is down-closed under any relation,
    unconditionally. -/
theorem downClosed_bot (r : α → α → Prop) : DownClosed r (fun _ : α => False) := by
  intro a b _ hb
  exact hb

/-- **GENERAL LEMMA 4 (top).** The always-true predicate is down-closed under any relation,
    unconditionally. -/
theorem downClosed_top (r : α → α → Prop) : DownClosed r (fun _ : α => True) := by
  intro a b _ _
  trivial

end General

/-! ### Instantiation at `r := edge` — the sublattice of consistent cuts -/

/-- **MEET.** The intersection of two consistent cuts is a consistent cut. -/
theorem consistentCut_inter {P Q : Event → Prop} (hP : IsConsistentCut P)
    (hQ : IsConsistentCut Q) : IsConsistentCut (fun x => P x ∧ Q x) :=
  downClosed_inter hP hQ

/-- **JOIN.** The union of two consistent cuts is a consistent cut. -/
theorem consistentCut_union {P Q : Event → Prop} (hP : IsConsistentCut P)
    (hQ : IsConsistentCut Q) : IsConsistentCut (fun x => P x ∨ Q x) :=
  downClosed_union hP hQ

/-- **BOTTOM.** The empty cut is consistent. -/
theorem consistentCut_bot : IsConsistentCut (fun _ : Event => False) :=
  downClosed_bot edge

/-- **TOP.** The full cut (every event recorded) is consistent. -/
theorem consistentCut_top : IsConsistentCut (fun _ : Event => True) :=
  downClosed_top edge

/-- **THE SUBLATTICE, BUNDLED.** Exactly the conjunction of the four theorems above — closure
    under `∩`, closure under `∪`, bottom, top — i.e. the consistent cuts on `Event` form a
    sublattice of the powerset lattice under `⊆`, with meet `∩`, join `∪`, bottom `∅`, top the
    full set. Asserts nothing beyond `consistentCut_inter`/`consistentCut_union`/
    `consistentCut_bot`/`consistentCut_top`; named `sublattice`, not `lattice`, since it is a
    sublattice of the ambient powerset lattice, and no absorption/distributivity law is claimed
    as a separate obligation (they come for free from `∩`/`∪` on `Prop`). -/
theorem consistentCuts_sublattice :
    (∀ {P Q : Event → Prop}, IsConsistentCut P → IsConsistentCut Q →
        IsConsistentCut (fun x => P x ∧ Q x)) ∧
    (∀ {P Q : Event → Prop}, IsConsistentCut P → IsConsistentCut Q →
        IsConsistentCut (fun x => P x ∨ Q x)) ∧
    IsConsistentCut (fun _ : Event => False) ∧
    IsConsistentCut (fun _ : Event => True) :=
  ⟨@consistentCut_inter, @consistentCut_union, consistentCut_bot, consistentCut_top⟩

/-! ### The same four facts for `IsHBClosed`, via `consistentCut_iff_hbClosed` -/

theorem hbClosed_inter {P Q : Event → Prop} (hP : IsHBClosed P) (hQ : IsHBClosed Q) :
    IsHBClosed (fun x => P x ∧ Q x) :=
  (consistentCut_iff_hbClosed _).mp
    (consistentCut_inter ((consistentCut_iff_hbClosed P).mpr hP)
      ((consistentCut_iff_hbClosed Q).mpr hQ))

/-- **JOIN, `HB`-closed form.** -/
theorem hbClosed_union {P Q : Event → Prop} (hP : IsHBClosed P) (hQ : IsHBClosed Q) :
    IsHBClosed (fun x => P x ∨ Q x) :=
  (consistentCut_iff_hbClosed _).mp
    (consistentCut_union ((consistentCut_iff_hbClosed P).mpr hP)
      ((consistentCut_iff_hbClosed Q).mpr hQ))

/-- **BOTTOM, `HB`-closed form.** -/
theorem hbClosed_bot : IsHBClosed (fun _ : Event => False) :=
  (consistentCut_iff_hbClosed _).mp consistentCut_bot

/-- **TOP, `HB`-closed form.** -/
theorem hbClosed_top : IsHBClosed (fun _ : Event => True) :=
  (consistentCut_iff_hbClosed _).mp consistentCut_top

section Instances

abbrev cutA : Event → Bool
  | .a0 => true
  | .a1 => true
  | .a2 => true
  | _ => false

/-- `cutA` as the `Prop`-valued cut predicate `IsConsistentCut` expects. -/
abbrev cutAProp (e : Event) : Prop := cutA e = true

/-- `cutA` is consistent: `a0` has no `edge`-predecessor, `a1`'s only predecessor `a0` is in the
    cut, `a2`'s only predecessor `a1` is in the cut — nothing forces any P1 event in. -/
theorem cutA_consistent : IsConsistentCut cutAProp := by
  intro a b
  cases a <;> cases b <;> decide

/-- A second, DISTINCT concrete consistent cut: P0 up to the send (`a0, a1`), and P1 up to the
    matching receive (`b0, b1`). -/
abbrev cutB : Event → Bool
  | .a0 => true
  | .a1 => true
  | .b0 => true
  | .b1 => true
  | _ => false

/-- `cutB` as the `Prop`-valued cut predicate `IsConsistentCut` expects. -/
abbrev cutBProp (e : Event) : Prop := cutB e = true

/-- `cutB` is consistent: `a0`, `b0` have no `edge`-predecessor, `a1`'s predecessor `a0` is in
    the cut, and `b1`'s two predecessors `a1` (the send) and `b0` are both in the cut — the
    matching send is recorded, so this cut has no orphan message either. -/
theorem cutB_consistent : IsConsistentCut cutBProp := by
  intro a b
  cases a <;> cases b <;> decide

/-- `cutA` and `cutB` are genuinely INCOMPARABLE (neither `⊆` the other), each witnessed by a
    concrete separating event: `a2 ∈ cutA` but `a2 ∉ cutB`, and `b1 ∈ cutB` but `b1 ∉ cutA`.
    Both checks closed by `decide` on the concrete finite tables. -/
theorem cutA_cutB_incomparable :
    (cutAProp .a2 ∧ ¬ cutBProp .a2) ∧ (cutBProp .b1 ∧ ¬ cutAProp .b1) :=
  ⟨by decide, by decide⟩

/-- **INTERSECTION IS CONSISTENT AND NON-TRIVIAL.** `cutA ∩ cutB` (which is exactly `{a0, a1}`)
    is a consistent cut by `consistentCut_inter` — genuinely exercising the closure lemma, not
    re-checked by brute `decide` on the union — and it is non-trivial: `a0` witnesses it is
    non-empty, and `a2` (in `cutA` but excluded from the intersection since it is not in `cutB`)
    witnesses it is not the full cut. -/
theorem cutA_inter_cutB_nontrivial :
    IsConsistentCut (fun x => cutAProp x ∧ cutBProp x) ∧
      (cutAProp .a0 ∧ cutBProp .a0) ∧ ¬ (cutAProp .a2 ∧ cutBProp .a2) :=
  ⟨consistentCut_inter cutA_consistent cutB_consistent, by decide, by decide⟩

/-- **UNION IS CONSISTENT AND NON-TRIVIAL.** `cutA ∪ cutB` (which is exactly
    `{a0, a1, a2, b0, b1}`) is a consistent cut by `consistentCut_union` — again genuinely
    exercising the closure lemma — and it is non-trivial: `a0` witnesses it is non-empty, and
    `b2` (in neither `cutA` nor `cutB`) witnesses it is not the full cut. -/
theorem cutA_union_cutB_nontrivial :
    IsConsistentCut (fun x => cutAProp x ∨ cutBProp x) ∧
      (cutAProp .a0 ∨ cutBProp .a0) ∧ ¬ (cutAProp .b2 ∨ cutBProp .b2) :=
  ⟨consistentCut_union cutA_consistent cutB_consistent, by decide, by decide⟩

end Instances

end AutoproverCorpus.ConsistentCutClosure
