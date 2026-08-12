/-
  AutoproverCorpus.Probability.CauchySchwarzFinite

  The finite Cauchy-Schwarz inequality over integer lists: for equal-length integer sequences
  `a` and `b`, `(sum aᵢbᵢ)^2 ≤ (sum aᵢ^2) * (sum bᵢ^2)`. Proved via the Lagrange identity
  `2 * ((sum aᵢ^2) * (sum bᵢ^2) - (sum aᵢbᵢ)^2) = sum_i sum_j (aᵢbⱼ - aⱼbᵢ)^2`: the right-hand
  side is a sum of squares, hence nonnegative, which forces the inequality. Working entirely
  over `Int` (rather than a field of scalars) avoids `Rat`'s irreducible-literal traps.

  Attribution: Cauchy (1821); the sum-of-squares proof via the Lagrange identity is classical
  (Lagrange, 1773, for the 3-term case; the general finite identity is standard).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.CauchySchwarzFinite

/-- Sum of `f 0, f 1, ..., f (n-1)`. -/
def S (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => S k f + f k

@[simp] theorem S_zero (f : Nat → Int) : S 0 f = 0 := rfl

@[simp] theorem S_succ (n : Nat) (f : Nat → Int) : S (n + 1) f = S n f + f n := rfl

theorem S_add (n : Nat) (f g : Nat → Int) :
    S n (fun i => f i + g i) = S n f + S n g := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_sub (n : Nat) (f g : Nat → Int) :
    S n (fun i => f i - g i) = S n f - S n g := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    S n (fun i => c * f i) = c * S n f := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_mul_right (n : Nat) (c : Int) (f : Nat → Int) :
    S n (fun i => f i * c) = S n f * c := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_nonneg (n : Nat) (f : Nat → Int) : (∀ i, i < n → 0 ≤ f i) → 0 ≤ S n f := by
  induction n with
  | zero => intro _; simp
  | succ k ih =>
      intro h
      have hk : 0 ≤ S k f := ih (fun i hi => h i (by omega))
      have hfk : 0 ≤ f k := h k (by omega)
      simp only [S_succ]
      omega

theorem S_congr (n : Nat) {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    S n f = S n g := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ]
      rw [ih (fun i hi => h i (by omega)), h k (by omega)]

/-! ### A square is nonnegative over `Int` -/

/-- `0 ≤ x * x` for `x : Int`, proved by a sign split (core Lean's `Int` has no `sq_nonneg`
    without `mathlib`). -/
theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  have h : 0 ≤ x ∨ x < 0 := by omega
  rcases h with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-! ### The Lagrange identity, in double-sum form -/

/-- The double-sum defining the Lagrange identity's right-hand side. -/
def L (n : Nat) (a b : Nat → Int) : Int :=
  S n (fun i => S n (fun j => (a i * b j - a j * b i) * (a i * b j - a j * b i)))

/-- Inner-sum expansion, for fixed `i`: expand `(aᵢbⱼ - aⱼbᵢ)^2` and split the sum over `j`. -/
theorem inner_expand (n : Nat) (a b : Nat → Int) (i : Nat) :
    S n (fun j => (a i * b j - a j * b i) * (a i * b j - a j * b i))
      = (a i * a i) * S n (fun j => b j * b j)
        - 2 * (a i * b i) * S n (fun j => a j * b j)
        + (b i * b i) * S n (fun j => a j * a j) := by
  have hpt : ∀ j, j < n →
      (a i * b j - a j * b i) * (a i * b j - a j * b i)
        = (a i * a i) * (b j * b j) - 2 * (a i * b i) * (a j * b j)
            + (b i * b i) * (a j * a j) := by
    intro j _; grind
  rw [S_congr n hpt]
  rw [S_add, S_sub]
  rw [S_mul_left n (a i * a i) (fun j => b j * b j)]
  rw [S_mul_left n (2 * (a i * b i)) (fun j => a j * b j)]
  rw [S_mul_left n (b i * b i) (fun j => a j * a j)]

/-- The double-sum identity: `L n a b = 2 * ((sum aᵢ^2) * (sum bᵢ^2) - (sum aᵢbᵢ)^2)`. -/
theorem lagrange_identity (n : Nat) (a b : Nat → Int) :
    L n a b
      = 2 * (S n (fun i => a i * a i) * S n (fun i => b i * b i)
              - S n (fun i => a i * b i) * S n (fun i => a i * b i)) := by
  unfold L
  have hpt : ∀ i, i < n →
      S n (fun j => (a i * b j - a j * b i) * (a i * b j - a j * b i))
        = (a i * a i) * S n (fun j => b j * b j)
          - 2 * (a i * b i) * S n (fun j => a j * b j)
          + (b i * b i) * S n (fun j => a j * a j) :=
    fun i _ => inner_expand n a b i
  rw [S_congr n hpt]
  rw [S_add, S_sub]
  rw [S_mul_right n (S n (fun j => b j * b j)) (fun i => a i * a i)]
  rw [S_mul_right n (S n (fun j => a j * b j)) (fun i => 2 * (a i * b i))]
  rw [S_mul_right n (S n (fun j => a j * a j)) (fun i => b i * b i)]
  have h2ab : S n (fun i => 2 * (a i * b i)) = 2 * S n (fun i => a i * b i) :=
    S_mul_left n 2 (fun i => a i * b i)
  rw [h2ab]
  have hsymm : S n (fun i => b i * b i) * S n (fun i => a i * a i)
      = S n (fun i => a i * a i) * S n (fun i => b i * b i) := by grind
  grind

/-- `L n a b` is a sum of squares, hence nonnegative. -/
theorem L_nonneg (n : Nat) (a b : Nat → Int) : 0 ≤ L n a b := by
  apply S_nonneg
  intro i _
  apply S_nonneg
  intro j _
  exact int_mul_self_nonneg _

/-! ### Cauchy-Schwarz, in `S`-indexed form -/

/-- **Cauchy-Schwarz inequality (finite, `Int`, `S`-indexed form).** -/
theorem cauchy_schwarz_S (n : Nat) (a b : Nat → Int) :
    S n (fun i => a i * b i) * S n (fun i => a i * b i)
      ≤ S n (fun i => a i * a i) * S n (fun i => b i * b i) := by
  have hid := lagrange_identity n a b
  have hnn := L_nonneg n a b
  have : 0 ≤ 2 * (S n (fun i => a i * a i) * S n (fun i => b i * b i)
              - S n (fun i => a i * b i) * S n (fun i => a i * b i)) := by
    rw [← hid]; exact hnn
  omega

/-! ### Bridging to `List Int` of equal length -/

/-- **Bridge sum lemma.** Summing `l.getD · 0` over the first `n` indices (via `S`) equals the
    sum of `l.take n`. -/
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

/-- **Specialization to `n := l.length`.** The full `getD`-indexed sum over a list equals the
    list's own sum. -/
theorem listSum_eq_S (l : List Int) : S l.length (fun i => l.getD i 0) = l.sum := by
  have h := S_take l l.length
  rwa [List.take_length] at h

/-- The dot product of two integer lists, index-bridged via `getD` (default `0`), summed over
    `a`'s own length. -/
def dot (a b : List Int) : Int :=
  S a.length (fun i => a.getD i 0 * b.getD i 0)

/-- The sum of squares of a list's entries. -/
def sumSq (a : List Int) : Int :=
  S a.length (fun i => a.getD i 0 * a.getD i 0)

/-- **Finite Cauchy-Schwarz inequality, list form.** For integer lists `a` and `b` of equal
    length, `(dot a b)^2 ≤ (sumSq a) * (sumSq b)`. -/
theorem cauchy_schwarz_finite (a b : List Int) (hlen : a.length = b.length) :
    dot a b * dot a b ≤ sumSq a * sumSq b := by
  have hineq := cauchy_schwarz_S a.length (fun i => a.getD i 0) (fun i => b.getD i 0)
  unfold dot sumSq
  rw [← hlen]
  exact hineq

/-! ### Instances -/

/-- A concrete non-vacuity witness: `a = (1, 2, 3)`, `b = (4, 5, 6)`, distinct (not parallel)
    sequences, checked strictly below the bound (`(1*4+2*5+3*6)^2 = 32^2 = 1024 <
    (1+4+9)*(16+25+36) = 14*77 = 1078`), confirming the inequality is not merely an equality
    forced by a degenerate case. -/
theorem cauchy_schwarz_finite_example :
    dot ([1, 2, 3] : List Int) ([4, 5, 6] : List Int)
        * dot ([1, 2, 3] : List Int) ([4, 5, 6] : List Int)
      ≤ sumSq ([1, 2, 3] : List Int) * sumSq ([4, 5, 6] : List Int) :=
  cauchy_schwarz_finite ([1, 2, 3] : List Int) ([4, 5, 6] : List Int) (by decide)

/-- The bound is strict here (not merely non-strict), confirming genuine, non-degenerate
    content. -/
example :
    dot ([1, 2, 3] : List Int) ([4, 5, 6] : List Int)
        * dot ([1, 2, 3] : List Int) ([4, 5, 6] : List Int)
      < sumSq ([1, 2, 3] : List Int) * sumSq ([4, 5, 6] : List Int) := by decide

/-- The equality case: a list against a (nonzero integer) scalar multiple of itself attains
    equality in Cauchy-Schwarz, checked concretely for `a = (1, 2, 3)`, `b = (2, 4, 6)`. -/
example :
    dot ([1, 2, 3] : List Int) ([2, 4, 6] : List Int)
        * dot ([1, 2, 3] : List Int) ([2, 4, 6] : List Int)
      = sumSq ([1, 2, 3] : List Int) * sumSq ([2, 4, 6] : List Int) := by decide

end AutoproverCorpus.CauchySchwarzFinite
