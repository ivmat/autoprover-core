/-
  AutoproverCorpus.Probability.MarkovInequality

  The discrete/counting form of Markov's inequality: for a `Nat`-valued (hence automatically
  nonnegative) function `f` on a finite index list `l` and a threshold `a`, the number of
  indices where `f` reaches or exceeds `a`, scaled by `a`, is bounded by the total sum of `f`
  over `l`. Stated over `Nat` throughout (no `Rat`), by list induction.

  Attribution: Markov's inequality (A. A. Markov).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.MarkovInequality

/-- The count of indices in `l` at or above the threshold `a`. -/
def aboveCount {α : Type} (a : Nat) (f : α → Nat) (l : List α) : Nat :=
  (l.filter (fun i => decide (a ≤ f i))).length

theorem aboveCount_nil {α : Type} (a : Nat) (f : α → Nat) :
    aboveCount a f ([] : List α) = 0 := rfl

/-- **Markov's inequality (discrete/counting form).** `a` times the number of indices where
    `f` reaches or exceeds `a` is bounded by the total sum of `f` over the list — the count of
    "large" values cannot exceed what the total mass can support. Proved by induction on `l`:
    when the head clears the threshold, both the count and the sum absorb one `a`-vs-`f x`
    comparison (`h : a ≤ f x`) on top of the inductive hypothesis; when it does not, the count
    is unchanged while the sum only grows (`f x` is a `Nat`, hence `≥ 0`). -/
theorem markov_inequality {α : Type} (a : Nat) (f : α → Nat) (l : List α) :
    a * aboveCount a f l ≤ (l.map f).sum := by
  induction l with
  | nil => simp [aboveCount]
  | cons x xs ih =>
    unfold aboveCount at ih ⊢
    by_cases h : a ≤ f x
    · rw [List.filter_cons_of_pos (by simpa using h), List.length_cons, Nat.mul_succ,
          List.map_cons, List.sum_cons]
      omega
    · rw [List.filter_cons_of_neg (by simpa using h), List.map_cons, List.sum_cons]
      omega

/-! ### Non-vacuity witness -/

/-- A concrete index list. -/
def sampleList : List Nat := [1, 2, 3, 4, 5]

/-- Three of the five entries (`3, 4, 5`) reach or exceed the threshold `3`. -/
example : aboveCount 3 id sampleList = 3 := by decide

/-- The total sum of `sampleList` is `15`. -/
example : (sampleList.map id).sum = 15 := by decide

/-- The concrete instance of Markov's inequality on `sampleList` at threshold `3`:
    `3 * 3 = 9 ≤ 15`, with genuine slack (the bound is not tight here). -/
example : 3 * aboveCount 3 id sampleList ≤ (sampleList.map id).sum :=
  markov_inequality 3 id sampleList

end AutoproverCorpus.MarkovInequality
