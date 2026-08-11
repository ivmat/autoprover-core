/-
  AutoproverCorpus.Probability.FrechetUpperBound

  Frechet upper bound at the set level: an intersection of events is contained in each of them,
  so joint probability can never exceed any marginal.

  Attribution: Classical (Frechet, 1935).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.FrechetUpperBound

theorem inter_subset_single {ι Ω : Type} (A : ι → Ω → Prop) :
    ∀ i, ∀ x, (∀ j, A j x) → A i x :=
  fun i _x hx => hx i

theorem ensemble_miss_subset_each {ι Ω : Type} (A : ι → Ω → Prop) (i : ι) :
    ∀ x, (∀ j, A j x) → A i x :=
  fun _x hx => hx i

theorem prob_le_of_monotone {Ω : Type} (P : (Ω → Prop) → Rat)
    (P_mono : ∀ A B : Ω → Prop, (∀ x, A x → B x) → P A ≤ P B)
    {ι : Type} (A : ι → Ω → Prop) :
    ∀ i, P (fun x => ∀ j, A j x) ≤ P (A i) :=
  fun i => P_mono _ _ (ensemble_miss_subset_each A i)

end AutoproverCorpus.FrechetUpperBound
