/-
  AutoproverCorpus.Probability.BooleUnionBound

  Boole's inequality (union bound) for a finite discrete measure, by list induction, together
  with the two-event inclusion-exclusion equality mass(A union B) + mass(A inter B) = mass A +
  mass B, with strict (overlapping) and tight (disjoint) witnesses. Elementary; no copula or
  dependence structure is involved.

  Attribution: Classical (Boole, 1854).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Probability.FrechetDiscreteMeasure

namespace AutoproverCorpus.BooleUnionBound

open AutoproverCorpus.FrechetDiscreteMeasure

/-! ### `massOf` at the empty event, and nonnegativity -/

/-- Every atom fails the always-false event, so its mass is `0`. Proved by induction using only
    `massOf_cons_neg` (no nonnegativity needed). -/
theorem massOf_empty {Ω : Type} (sample : List (Ω × Rat)) :
    massOf sample (fun _ : Ω => False) = 0 := by
  induction sample with
  | nil => exact massOf_nil _
  | cons p ps ih =>
      rw [massOf_cons_neg p (fun _ => False) (fun h => h), ih]
      grind

theorem massOf_nonneg {Ω : Type} (sample : List (Ω × Rat)) (hnn : ∀ t ∈ sample, 0 ≤ t.2)
    (event : Ω → Prop) : 0 ≤ massOf sample event := by
  have h := massOf_mono sample hnn (fun _ => False) event (fun _ hx => hx.elim)
  rw [massOf_empty sample] at h
  exact h

/-! ### The substantive core: n=2 inclusion–exclusion -/

theorem massOf_incl_excl {Ω : Type} (sample : List (Ω × Rat)) (A B : Ω → Prop) :
    massOf sample (fun x => A x ∨ B x) + massOf sample (fun x => A x ∧ B x) =
    massOf sample A + massOf sample B := by
  induction sample with
  | nil => simp only [massOf_nil]
  | cons p ps ih =>
      by_cases hA : A p.1
      · by_cases hB : B p.1
        · rw [massOf_cons_pos p (fun x => A x ∨ B x) (Or.inl hA),
              massOf_cons_pos p (fun x => A x ∧ B x) ⟨hA, hB⟩,
              massOf_cons_pos p A hA, massOf_cons_pos p B hB]
          grind
        · rw [massOf_cons_pos p (fun x => A x ∨ B x) (Or.inl hA),
              massOf_cons_neg p (fun x => A x ∧ B x) (fun h => hB h.2),
              massOf_cons_pos p A hA, massOf_cons_neg p B hB]
          grind
      · by_cases hB : B p.1
        · rw [massOf_cons_pos p (fun x => A x ∨ B x) (Or.inr hB),
              massOf_cons_neg p (fun x => A x ∧ B x) (fun h => hA h.1),
              massOf_cons_neg p A hA, massOf_cons_pos p B hB]
          grind
        · rw [massOf_cons_neg p (fun x => A x ∨ B x) (fun h => h.elim hA hB),
              massOf_cons_neg p (fun x => A x ∧ B x) (fun h => hA h.1),
              massOf_cons_neg p A hA, massOf_cons_neg p B hB]
          grind

theorem massOf_incl_excl_sub {Ω : Type} (sample : List (Ω × Rat)) (A B : Ω → Prop) :
    massOf sample (fun x => A x ∨ B x) =
    massOf sample A + massOf sample B - massOf sample (fun x => A x ∧ B x) := by
  rw [← massOf_incl_excl sample A B, Rat.add_sub_cancel]

/-! ### Two-event Boole -/

/-- **`boole_two`.** The two-event union bound, from `massOf_incl_excl` plus `massOf_nonneg` on
    the intersection (dropping a nonnegative term from an equality). Unlike `massOf_incl_excl`,
    this needs `hnn` — exactly to justify dropping `massOf(A∩B)`. -/
theorem boole_two {Ω : Type} (sample : List (Ω × Rat)) (hnn : ∀ t ∈ sample, 0 ≤ t.2)
    (A B : Ω → Prop) :
    massOf sample (fun x => A x ∨ B x) ≤ massOf sample A + massOf sample B := by
  have heq := massOf_incl_excl sample A B
  have hge : 0 ≤ massOf sample (fun x => A x ∧ B x) := massOf_nonneg sample hnn _
  grind

/-! ### The general union bound over a finite event family -/

/-- Union of a finite family of events, as a fold: `unionOf [] = fun _ => False`, `unionOf
    (A::As) x = A x ∨ unionOf As x`. -/
def unionOf {Ω : Type} (As : List (Ω → Prop)) : Ω → Prop :=
  fun x => As.foldr (fun A acc => A x ∨ acc) False

/-- Sum of the individual masses of a finite event family. `noncomputable` because it depends on
    `massOf`. -/
noncomputable def sumMass {Ω : Type} (sample : List (Ω × Rat)) (As : List (Ω → Prop)) : Rat :=
  As.foldr (fun A acc => massOf sample A + acc) 0

theorem unionOf_nil {Ω : Type} : unionOf ([] : List (Ω → Prop)) = fun _ : Ω => False := rfl

theorem unionOf_cons {Ω : Type} (A : Ω → Prop) (As : List (Ω → Prop)) :
    unionOf (A :: As) = fun x => A x ∨ unionOf As x := rfl

theorem sumMass_nil {Ω : Type} (sample : List (Ω × Rat)) :
    sumMass sample ([] : List (Ω → Prop)) = 0 := rfl

theorem sumMass_cons {Ω : Type} (sample : List (Ω × Rat)) (A : Ω → Prop) (As : List (Ω → Prop)) :
    sumMass sample (A :: As) = massOf sample A + sumMass sample As := rfl

/-- **`boole_union`, the headline.** Classical Boole's inequality / union bound: `P(⋃ᵢ Aᵢ) ≤
    Σᵢ P(Aᵢ)`, for a finite event family `As`. Proved by induction on `As`: the base case unfolds
    to `massOf_empty` (`0 ≤ 0`); the cons case chains `boole_two A (unionOf As)` with the IH
    lifted through `Rat.add_le_add_left`, closed by `Rat.le_trans`. -/
theorem boole_union {Ω : Type} (sample : List (Ω × Rat)) (hnn : ∀ t ∈ sample, 0 ≤ t.2)
    (As : List (Ω → Prop)) :
    massOf sample (unionOf As) ≤ sumMass sample As := by
  induction As with
  | nil =>
      rw [unionOf_nil, sumMass_nil, massOf_empty]
      exact Rat.le_refl
  | cons A As ih =>
      rw [unionOf_cons, sumMass_cons]
      exact Rat.le_trans (boole_two sample hnn A (unionOf As)) (Rat.add_le_add_left.mpr ih)

theorem incl_excl_A1_A2_concrete :
    massOf sample3 (fun x => A1 x ∨ A2 x) + massOf sample3 (fun x => A1 x ∧ A2 x) =
    massOf sample3 A1 + massOf sample3 A2 :=
  massOf_incl_excl sample3 A1 A2

theorem massOf_sample3_union_A1_A2 : massOf sample3 (fun x => A1 x ∨ A2 x) = 1 := by
  unfold sample3
  rw [massOf_cons_pos (0, mkRat 1 3) (fun x => A1 x ∨ A2 x) (show A1 0 ∨ A2 0 by decide),
      massOf_cons_pos (1, mkRat 1 3) (fun x => A1 x ∨ A2 x) (show A1 1 ∨ A2 1 by decide),
      massOf_cons_pos (2, mkRat 1 3) (fun x => A1 x ∨ A2 x) (show A1 2 ∨ A2 2 by decide),
      massOf_nil]
  simp only [Rat.add_def']
  decide

/-- Example: `A1`, `A2` overlap at `1`, so the union bound has real
    slack: `massOf(A1∪A2) = 1 < 4/3 = massOf A1 + massOf A2` (strict case). -/
theorem boole_strict_example :
    massOf sample3 (fun x => A1 x ∨ A2 x) ≤ massOf sample3 A1 + massOf sample3 A2 ∧
    massOf sample3 (fun x => A1 x ∨ A2 x) < massOf sample3 A1 + massOf sample3 A2 := by
  refine ⟨boole_two sample3 sample3_nonneg A1 A2, ?_⟩
  rw [massOf_sample3_union_A1_A2, massOf_sample3_A1, massOf_sample3_A2]
  simp only [Rat.add_def']
  decide

/-- Event: atom is `2` — disjoint from `A3 = {0}`, used for the tight example below. -/
abbrev A4 (x : Nat) : Prop := x = 2

theorem massOf_sample3_A4 : massOf sample3 A4 = mkRat 1 3 := by
  unfold sample3
  rw [massOf_cons_neg (0, mkRat 1 3) A4 (show ¬ A4 0 by decide),
      massOf_cons_neg (1, mkRat 1 3) A4 (show ¬ A4 1 by decide),
      massOf_cons_pos (2, mkRat 1 3) A4 (show A4 2 by decide), massOf_nil]
  simp only [Rat.add_def']
  decide

theorem massOf_sample3_union_A3_A4 : massOf sample3 (fun x => A3 x ∨ A4 x) = mkRat 2 3 := by
  unfold sample3
  rw [massOf_cons_pos (0, mkRat 1 3) (fun x => A3 x ∨ A4 x) (show A3 0 ∨ A4 0 by decide),
      massOf_cons_neg (1, mkRat 1 3) (fun x => A3 x ∨ A4 x) (show ¬ (A3 1 ∨ A4 1) by decide),
      massOf_cons_pos (2, mkRat 1 3) (fun x => A3 x ∨ A4 x) (show A3 2 ∨ A4 2 by decide),
      massOf_nil]
  simp only [Rat.add_def']
  decide

/-- Example: `A3 = {0}` and `A4 = {2}` are disjoint: Boole's `≤` is exactly
    equality here — `massOf(A3∪A4) = massOf A3 + massOf A4` — pinning that the strictness in
    `boole_strict_example` comes precisely from the `A1`/`A2` overlap, not from the bound itself
    being loose in general. -/
theorem boole_tight_example :
    massOf sample3 (fun x => A3 x ∨ A4 x) = massOf sample3 A3 + massOf sample3 A4 := by
  rw [massOf_sample3_union_A3_A4, massOf_sample3_A3, massOf_sample3_A4]
  simp only [Rat.add_def']
  decide

end AutoproverCorpus.BooleUnionBound
