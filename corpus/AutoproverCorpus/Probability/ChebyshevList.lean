/-
  AutoproverCorpus.Probability.ChebyshevList

  A list-level restatement of Chebyshev's sum inequality, derived as a corollary of the finite
  form.

  Attribution: Classical (Chebyshev); corollary form.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Probability.ChebyshevSum

namespace AutoproverCorpus.ChebyshevList

open AutoproverCorpus.ChebyshevSum

/-- **Bridge sum lemma.** Summing `l.getD · 0` over the first `n` indices (via `S`)
    equals the sum of `l.take n`. -/
theorem S_take (l : List Int) : ∀ n, S n (fun i => l.getD i 0) = (l.take n).sum
  | 0 => by simp
  | k + 1 => by
      have ih := S_take l k
      simp only [S_succ, ih]
      rw [List.take_add_one, List.sum_append]
      congr 1
      rw [List.getD_eq_getElem?_getD]
      cases l[k]? with
      | none => simp
      | some x => simp

/-- **Specialization to `n := l.length`.** The full `getD`-indexed sum over a list
    equals the list's own sum. -/
theorem listSum_eq_S (l : List Int) : S l.length (fun i => l.getD i 0) = l.sum := by
  have h := S_take l l.length
  rwa [List.take_length] at h

/-- The "sum of pointwise products" of `a` and `b`, index-bridged via `getD` (default
    `0`), summed over `a`'s own length. -/
def dotSum (a b : List Int) : Int :=
  S a.length (fun i => a.getD i 0 * b.getD i 0)

def SimilarlyOrderedList (a b : List Int) : Prop :=
  ∀ i j, i < a.length → j < a.length →
    0 ≤ (a.getD i 0 - a.getD j 0) * (b.getD i 0 - b.getD j 0)

theorem chebyshev_sum_ineq_list (a b : List Int) (hlen : a.length = b.length)
    (hord : SimilarlyOrderedList a b) :
    (a.length : Int) * dotSum a b ≥ a.sum * b.sum := by
  have hineq := chebyshev_sum_ineq a.length (fun i => a.getD i 0) (fun i => b.getD i 0) hord
  have hbsum : S a.length (fun i => b.getD i 0) = b.sum := by
    rw [hlen]; exact listSum_eq_S b
  have hasum : S a.length (fun i => a.getD i 0) = a.sum := listSum_eq_S a
  rw [hasum, hbsum] at hineq
  exact hineq

/-! ### Instances -/

theorem chebyshev_sum_ineq_list_example :
    SimilarlyOrderedList ([1, 2, 3] : List Int) ([1, 2, 3] : List Int) ∧
    (3 : Int) * dotSum ([1, 2, 3] : List Int) ([1, 2, 3] : List Int) ≥
      ([1, 2, 3] : List Int).sum * ([1, 2, 3] : List Int).sum := by
  constructor
  · intro i j hi hj
    have hlen3 : ([1, 2, 3] : List Int).length = 3 := rfl
    rw [hlen3] at hi hj
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi3 with rfl | rfl | rfl <;> rcases hj3 with rfl | rfl | rfl <;> decide
  · decide

end AutoproverCorpus.ChebyshevList
