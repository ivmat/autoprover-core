/-
  AutoproverCorpus.Probability.ChebyshevSum

  Chebyshev's sum inequality in finite form over integer lists: similarly ordered sequences make
  the average of products at least the product of averages.

  Attribution: Classical (Chebyshev).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.ChebyshevSum

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

theorem S_const (n : Nat) (c : Int) : S n (fun _ => c) = (n : Int) * c := by
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

/-- The double-sum defining Chebyshev's "covariance" term. -/
def D (n : Nat) (a b : Nat → Int) : Int :=
  S n (fun i => S n (fun j => (a i - a j) * (b i - b j)))

/-- Inner-sum expansion, for fixed `i`. -/
theorem inner_expand (n : Nat) (a b : Nat → Int) (i : Nat) :
    S n (fun j => (a i - a j) * (b i - b j))
      = (n : Int) * (a i * b i) - a i * S n b - S n a * b i + S n (fun j => a j * b j) := by
  have hpt : ∀ j, j < n →
      (a i - a j) * (b i - b j)
        = (a i * b i) - a i * b j - a j * b i + a j * b j := by
    intro j _; grind
  rw [S_congr n hpt]
  rw [S_add, S_sub, S_sub]
  rw [S_const n (a i * b i), S_mul_left n (a i) b, S_mul_right n (b i) a]

theorem D_eq (n : Nat) (a b : Nat → Int) :
    D n a b = (n : Int) * S n (fun i => a i * b i) - S n a * S n b
              - (S n a * S n b) + (n : Int) * S n (fun j => a j * b j) := by
  unfold D
  have hpt : ∀ i, i < n → S n (fun j => (a i - a j) * (b i - b j))
      = (n : Int) * (a i * b i) - a i * S n b - S n a * b i + S n (fun j => a j * b j) :=
    fun i _ => inner_expand n a b i
  rw [S_congr n hpt]
  rw [S_add, S_sub, S_sub]
  rw [S_const n (S n (fun j => a j * b j))]
  rw [S_mul_left n (n:Int) (fun i => a i * b i)]
  rw [S_mul_right n (S n b) a]
  rw [S_mul_left n (S n a) b]

/-- The double-sum identity: `2 * (n * Σaᵢbᵢ − (Σaᵢ)(Σbᵢ)) = Σᵢⱼ (aᵢ−aⱼ)(bᵢ−bⱼ)`. -/
theorem chebyshev_identity (n : Nat) (a b : Nat → Int) :
    2 * ((n : Int) * S n (fun i => a i * b i) - S n a * S n b) = D n a b := by
  rw [D_eq n a b]
  grind

/-- Similarly ordered: for all indices `i j < n`, `a` and `b` move in the same
    direction (nonnegative "local covariance"). -/
def SimilarlyOrdered (n : Nat) (a b : Nat → Int) : Prop :=
  ∀ i j, i < n → j < n → 0 ≤ (a i - a j) * (b i - b j)

theorem D_nonneg (n : Nat) (a b : Nat → Int) (h : SimilarlyOrdered n a b) :
    0 ≤ D n a b := by
  apply S_nonneg
  intro i _
  apply S_nonneg
  intro j hj
  exact h i j (by omega) hj

/-- Chebyshev's sum inequality (finite, `Int`): similarly ordered sequences satisfy
    `n * Σ aᵢbᵢ ≥ (Σaᵢ)(Σbᵢ)`. -/
theorem chebyshev_sum_ineq (n : Nat) (a b : Nat → Int) (h : SimilarlyOrdered n a b) :
    (n : Int) * S n (fun i => a i * b i) ≥ S n a * S n b := by
  have hid := chebyshev_identity n a b
  have hnn := D_nonneg n a b h
  have : 0 ≤ 2 * ((n:Int) * S n (fun i => a i * b i) - S n a * S n b) := by
    rw [hid]; exact hnn
  omega

/-- Instance: a similarly-ordered length-3 instance, `a = b = (1,2,3)`
    (both strictly increasing, hence similarly ordered). Checked over `Int` by `decide`,
    not `native_decide`. -/
theorem chebyshev_sum_ineq_example :
    SimilarlyOrdered 3 (fun i => (i : Int) + 1) (fun i => (i : Int) + 1) ∧
    (3 : Int) * S 3 (fun i => ((i : Int) + 1) * ((i : Int) + 1)) ≥
      S 3 (fun i => (i : Int) + 1) * S 3 (fun i => (i : Int) + 1) := by
  constructor
  · intro i j hi hj
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi3 with rfl | rfl | rfl <;> rcases hj3 with rfl | rfl | rfl <;> decide
  · decide

end AutoproverCorpus.ChebyshevSum
