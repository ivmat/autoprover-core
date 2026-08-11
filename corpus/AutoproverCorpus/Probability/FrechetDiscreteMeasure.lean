/-
  AutoproverCorpus.Probability.FrechetDiscreteMeasure

  Frechet upper bound for a finite discrete measure: the measure of an intersection is at most
  the measure of each factor (monotonicity of a finitely additive mass function). Upper bound
  only.

  Attribution: Classical (Frechet, 1935); finite discrete-measure form.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Probability.FrechetUpperBound

namespace AutoproverCorpus.FrechetDiscreteMeasure

/-! ### The discrete measure: mass of an event over a finite weighted sample -/

open Classical in
noncomputable def massOf {Ω : Type} (sample : List (Ω × Rat)) (event : Ω → Prop) : Rat :=
  sample.foldr (fun p acc => (if event p.1 then p.2 else 0) + acc) 0

/-! ### Unfolding lemmas, stated WITHOUT ever writing a fresh `if` in a theorem's type

  `massOf`'s per-atom `if` carries `Classical.propDecidable` baked in from its own definition
  (see above). Restating `massOf sample event`'s value by writing a NEW `if event a then w else
  0` in some later theorem's STATEMENT would force Lean to elaborate that `if` afresh — and for
  a genuinely decidable `event`/`a` (e.g. `A1 0`), ordinary instance search finds and PREFERS a
  computable `Decidable` instance over `Classical.propDecidable`, giving a term that is NOT
  syntactically the one baked into `massOf`, and the two need not be definitionally equal (a
  `Classical.choice`-built instance does not reduce to a constructor, so the kernel cannot
  confirm they compute the same way). The fix used throughout below: never write `if` in a
  theorem's TYPE; only ever apply `if_pos`/`if_neg` — which are instance-AGNOSTIC (they unify
  against whatever instance already sits in the existing goal, no fresh synthesis) — as REWRITE
  steps against the goal produced by `unfold massOf`. -/

theorem massOf_nil {Ω : Type} (event : Ω → Prop) :
    massOf ([] : List (Ω × Rat)) event = 0 := by
  unfold massOf; rfl

theorem massOf_cons_pos {Ω : Type} {sample : List (Ω × Rat)} (t : Ω × Rat) (event : Ω → Prop)
    (h : event t.1) : massOf (t :: sample) event = t.2 + massOf sample event := by
  unfold massOf
  simp only [List.foldr_cons]
  rw [if_pos h]

theorem massOf_cons_neg {Ω : Type} {sample : List (Ω × Rat)} (t : Ω × Rat) (event : Ω → Prop)
    (h : ¬ event t.1) : massOf (t :: sample) event = 0 + massOf sample event := by
  unfold massOf
  simp only [List.foldr_cons]
  rw [if_neg h]

/-! ### The real work: finite-sum monotonicity over `Rat` with nonnegative weights -/

theorem massOf_mono {Ω : Type} (sample : List (Ω × Rat)) (hnn : ∀ t ∈ sample, 0 ≤ t.2)
    (A B : Ω → Prop) (h : ∀ x, A x → B x) :
    massOf sample A ≤ massOf sample B := by
  induction sample with
  | nil => rw [massOf_nil, massOf_nil]; exact Rat.le_refl
  | cons p ps ih =>
      have ihps : massOf ps A ≤ massOf ps B :=
        ih (fun s hs => hnn s (List.mem_cons_of_mem p hs))
      by_cases hA : A p.1
      · have hB : B p.1 := h p.1 hA
        rw [massOf_cons_pos p A hA, massOf_cons_pos p B hB]
        exact Rat.add_le_add_left.mpr ihps
      · by_cases hB : B p.1
        · rw [massOf_cons_neg p A hA, massOf_cons_pos p B hB]
          have hz : (0 : Rat) + massOf ps A ≤ p.2 + massOf ps A :=
            Rat.add_le_add_right.mpr (hnn p List.mem_cons_self)
          exact Rat.le_trans hz (Rat.add_le_add_left.mpr ihps)
        · rw [massOf_cons_neg p A hA, massOf_cons_neg p B hB]
          exact Rat.add_le_add_left.mpr ihps

theorem frechet_upper_discrete {Ω ι : Type} (sample : List (Ω × Rat))
    (hnn : ∀ t ∈ sample, 0 ≤ t.2) (A : ι → Ω → Prop) (i : ι) :
    massOf sample (fun x => ∀ j, A j x) ≤ massOf sample (A i) :=
  AutoproverCorpus.FrechetUpperBound.prob_le_of_monotone (massOf sample) (massOf_mono sample hnn) A i

/-! ### The explicit "≤ min" form (two-event case) -/

/-- Binary rational minimum. -/
abbrev min2 (a b : Rat) : Rat := if a ≤ b then a else b

theorem le_min2 {x a b : Rat} (ha : x ≤ a) (hb : x ≤ b) : x ≤ min2 a b := by
  unfold min2
  by_cases hab : a ≤ b
  · rw [if_pos hab]; exact ha
  · rw [if_neg hab]; exact hb

theorem discreteMeasure_inter_le_min {Ω : Type} (sample : List (Ω × Rat))
    (hnn : ∀ t ∈ sample, 0 ≤ t.2) (A B : Ω → Prop) :
    massOf sample (fun x => A x ∧ B x) ≤ min2 (massOf sample A) (massOf sample B) :=
  le_min2 (massOf_mono sample hnn (fun x => A x ∧ B x) A (fun _ hx => hx.1))
          (massOf_mono sample hnn (fun x => A x ∧ B x) B (fun _ hx => hx.2))

/-! ### Instance: a concrete 3-atom uniform pmf, weights proved `≥ 0` and summing to `1` -/

/-- Raw total weight of a sample (no event filtering) — used only to certify `sample3` really is
    a probability measure (weights summing to `1`), independent of `massOf`'s classical
    machinery. -/
def totalWeight {Ω : Type} (sample : List (Ω × Rat)) : Rat :=
  sample.foldr (fun t acc => t.2 + acc) 0

/-- Three atoms `0, 1, 2`, each with weight `1/3`. -/
def sample3 : List (Nat × Rat) :=
  [(0, mkRat 1 3), (1, mkRat 1 3), (2, mkRat 1 3)]

/-- The weights are nonnegative — the hypothesis `massOf_mono`/`frechet_upper_discrete` need. -/
theorem sample3_nonneg : ∀ t ∈ sample3, 0 ≤ t.2 := by
  intro t ht
  simp only [sample3, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> decide

theorem sample3_weights_sum_to_one : totalWeight sample3 = 1 := by
  simp only [totalWeight, sample3, List.foldr, Rat.add_def']
  decide

/-- Event: atom is `0` or `1`. `abbrev` (reducible), needed so `decide` can unfold it during
    instance search — plain `def` is not reducible enough. -/
abbrev A1 (x : Nat) : Prop := x = 0 ∨ x = 1

/-- Event: atom is `1` or `2`. -/
abbrev A2 (x : Nat) : Prop := x = 1 ∨ x = 2

/-- Event: atom is `0` (a strict subset of `A1`, used for the TIGHT example). -/
abbrev A3 (x : Nat) : Prop := x = 0

theorem massOf_sample3_A1 : massOf sample3 A1 = mkRat 2 3 := by
  unfold sample3
  rw [massOf_cons_pos (0, mkRat 1 3) A1 (show A1 0 by decide),
      massOf_cons_pos (1, mkRat 1 3) A1 (show A1 1 by decide),
      massOf_cons_neg (2, mkRat 1 3) A1 (show ¬ A1 2 by decide), massOf_nil]
  simp only [Rat.add_def']
  decide

theorem massOf_sample3_A2 : massOf sample3 A2 = mkRat 2 3 := by
  unfold sample3
  rw [massOf_cons_neg (0, mkRat 1 3) A2 (show ¬ A2 0 by decide),
      massOf_cons_pos (1, mkRat 1 3) A2 (show A2 1 by decide),
      massOf_cons_pos (2, mkRat 1 3) A2 (show A2 2 by decide), massOf_nil]
  simp only [Rat.add_def']
  decide

theorem massOf_sample3_A3 : massOf sample3 A3 = mkRat 1 3 := by
  unfold sample3
  rw [massOf_cons_pos (0, mkRat 1 3) A3 (show A3 0 by decide),
      massOf_cons_neg (1, mkRat 1 3) A3 (show ¬ A3 1 by decide),
      massOf_cons_neg (2, mkRat 1 3) A3 (show ¬ A3 2 by decide), massOf_nil]
  simp only [Rat.add_def']
  decide

theorem massOf_sample3_inter_A1_A2 : massOf sample3 (fun x => A1 x ∧ A2 x) = mkRat 1 3 := by
  unfold sample3
  rw [massOf_cons_neg (0, mkRat 1 3) (fun x => A1 x ∧ A2 x) (show ¬ (A1 0 ∧ A2 0) by decide),
      massOf_cons_pos (1, mkRat 1 3) (fun x => A1 x ∧ A2 x) (show A1 1 ∧ A2 1 by decide),
      massOf_cons_neg (2, mkRat 1 3) (fun x => A1 x ∧ A2 x) (show ¬ (A1 2 ∧ A2 2) by decide),
      massOf_nil]
  simp only [Rat.add_def']
  decide

theorem massOf_sample3_inter_A3_A1 : massOf sample3 (fun x => A3 x ∧ A1 x) = mkRat 1 3 := by
  unfold sample3
  rw [massOf_cons_pos (0, mkRat 1 3) (fun x => A3 x ∧ A1 x) (show A3 0 ∧ A1 0 by decide),
      massOf_cons_neg (1, mkRat 1 3) (fun x => A3 x ∧ A1 x) (show ¬ (A3 1 ∧ A1 1) by decide),
      massOf_cons_neg (2, mkRat 1 3) (fun x => A3 x ∧ A1 x) (show ¬ (A3 2 ∧ A1 2) by decide),
      massOf_nil]
  simp only [Rat.add_def']
  decide

/-- Example: `A1 = {0,1}`, `A2 = {1,2}`: the Fréchet upper bound is
    strict — `1/3 < 2/3` — slack, computed over concrete `Rat` literals by `decide`
    (comparison, not `Rat.add`/`mul`/`sub`, so no `@[irreducible]` obstruction). -/
theorem frechet_discrete_strict_example :
    massOf sample3 (fun x => A1 x ∧ A2 x) ≤ min2 (massOf sample3 A1) (massOf sample3 A2) ∧
    massOf sample3 (fun x => A1 x ∧ A2 x) < min2 (massOf sample3 A1) (massOf sample3 A2) := by
  constructor
  · exact discreteMeasure_inter_le_min sample3 sample3_nonneg A1 A2
  · rw [massOf_sample3_inter_A1_A2, massOf_sample3_A1, massOf_sample3_A2]
    unfold min2
    rw [if_pos (show (mkRat 2 3 : Rat) ≤ mkRat 2 3 by decide)]
    decide

/-- Example: `A3 = {0} ⊆ A1 = {0,1}`: the Fréchet upper bound is tight —
    exact equality `1/3 = 1/3` — pinning down that `massOf_mono`'s `≤` is not always strict. -/
theorem frechet_discrete_tight_example :
    massOf sample3 (fun x => A3 x ∧ A1 x) = min2 (massOf sample3 A3) (massOf sample3 A1) := by
  rw [massOf_sample3_inter_A3_A1, massOf_sample3_A3, massOf_sample3_A1]
  unfold min2
  rw [if_pos (show (mkRat 1 3 : Rat) ≤ mkRat 2 3 by decide)]

end AutoproverCorpus.FrechetDiscreteMeasure
