/-
  AutoproverCorpus.Probability.KroghVedelsby

  The Krogh-Vedelsby ambiguity decomposition as a finite rational sum identity (no limits):
  ensemble error equals average member error minus average ambiguity.

  Attribution: Classical (Krogh and Vedelsby, 1995).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.KroghVedelsby

/-- Sum of `f 0, f 1, ..., f (n-1)`, over `Rat`. -/
def S (n : Nat) (f : Nat → Rat) : Rat :=
  match n with
  | 0 => 0
  | k + 1 => S k f + f k

@[simp] theorem S_zero (f : Nat → Rat) : S 0 f = 0 := rfl

@[simp] theorem S_succ (n : Nat) (f : Nat → Rat) : S (n + 1) f = S n f + f n := rfl

theorem S_add (n : Nat) (f g : Nat → Rat) :
    S n (fun i => f i + g i) = S n f + S n g := by
  induction n with
  | zero => simp only [S_zero]; rw [Rat.add_zero]
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_sub (n : Nat) (f g : Nat → Rat) :
    S n (fun i => f i - g i) = S n f - S n g := by
  induction n with
  | zero => simp only [S_zero]; rw [Rat.sub_self]
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_mul_left (n : Nat) (c : Rat) (f : Nat → Rat) :
    S n (fun i => c * f i) = c * S n f := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_const (n : Nat) (c : Rat) : S n (fun _ => c) = (n : Rat) * c := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ, ih]
      grind

theorem S_congr (n : Nat) {f g : Nat → Rat} (h : ∀ i, i < n → f i = g i) :
    S n f = S n g := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [S_succ]
      rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem S_nonneg (n : Nat) (f : Nat → Rat) (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ S n f := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : 0 ≤ S k f := ih (fun i hi => h i (by omega))
      have hfk : 0 ≤ f k := h k (by omega)
      simp only [S_succ]
      grind

/-! ### A square is nonnegative (core Lean's `Rat` has no `LinearOrder`/`sq_nonneg`) -/

/-- `x^2 = x * x`, bridging `HPow` notation to plain multiplication (`Rat.pow_succ` /
    `Rat.pow_one`), needed before any sign case-split on a square. -/
theorem rat_sq_eq_mul_self (x : Rat) : x ^ 2 = x * x := by
  rw [show (2 : Nat) = 1 + 1 from rfl, Rat.pow_succ, Rat.pow_one]

/-- `0 ≤ x^2` for any `x : Rat`. This is nonlinear sign analysis (core `grind`'s
    `Rat` ring normalizer is explicitly documented not to cover this),
    so it is hand-proved: case-split on the sign of `x` via `Rat.nonneg_total`, and in the
    negative branch bridge `(-x)*(-x) = x*x` before closing with `Rat.mul_nonneg`. -/
theorem rat_sq_nonneg (x : Rat) : 0 ≤ x ^ 2 := by
  rw [rat_sq_eq_mul_self]
  rcases Rat.nonneg_total x with hx | hx
  · exact Rat.mul_nonneg hx hx
  · have heq : (-x) * (-x) = x * x := by
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [← heq]
    exact Rat.mul_nonneg hx hx

/-! ### The ensemble mean and the decomposition -/

/-- The ensemble (weighted-mean) prediction: `Σ w i * f i`. -/
def fbar (n : Nat) (w f : Nat → Rat) : Rat := S n (fun i => w i * f i)

theorem krogh_vedelsby_identity (n : Nat) (w f : Nat → Rat) (t : Rat) (hw : S n w = 1) :
    (fbar n w f - t) ^ 2
      = S n (fun i => w i * (f i - t) ^ 2) - S n (fun i => w i * (f i - fbar n w f) ^ 2) := by
  have hpt : ∀ i, i < n →
      w i * (f i - t) ^ 2
        = (w i * (f i - fbar n w f) ^ 2
              + 2 * (fbar n w f - t) * (w i * (f i - fbar n w f)))
          + (fbar n w f - t) ^ 2 * w i := by
    intro i _
    grind
  have hzero : S n (fun i => w i * (f i - fbar n w f)) = 0 := by
    have hexp : S n (fun i => w i * (f i - fbar n w f))
        = S n (fun i => w i * f i) - S n (fun i => w i * fbar n w f) := by
      have hcongr : ∀ i, i < n →
          w i * (f i - fbar n w f) = w i * f i - w i * fbar n w f := by
        intro i _; grind
      rw [S_congr n hcongr]
      exact S_sub n (fun i => w i * f i) (fun i => w i * fbar n w f)
    rw [hexp]
    have hwm : S n (fun i => w i * fbar n w f) = fbar n w f * S n w := by
      have hcomm : ∀ i, i < n → w i * fbar n w f = fbar n w f * w i := by
        intro i _; grind
      rw [S_congr n hcomm]
      exact S_mul_left n (fbar n w f) w
    rw [hwm, hw]
    have hSf : S n (fun i => w i * f i) = fbar n w f := rfl
    rw [hSf]
    grind
  have hmid :
      S n (fun i => 2 * (fbar n w f - t) * (w i * (f i - fbar n w f))) = 0 := by
    rw [S_mul_left n (2 * (fbar n w f - t)) (fun i => w i * (f i - fbar n w f))]
    rw [hzero]
    grind
  have hlast : S n (fun i => (fbar n w f - t) ^ 2 * w i) = (fbar n w f - t) ^ 2 := by
    rw [S_mul_left n ((fbar n w f - t) ^ 2) w, hw]
    grind
  have hsplit1 : S n (fun i => w i * (f i - t) ^ 2)
      = S n (fun i =>
            (w i * (f i - fbar n w f) ^ 2
                + 2 * (fbar n w f - t) * (w i * (f i - fbar n w f)))
              + (fbar n w f - t) ^ 2 * w i) :=
    S_congr n hpt
  have key : S n (fun i => w i * (f i - t) ^ 2)
      = S n (fun i => w i * (f i - fbar n w f) ^ 2) + (fbar n w f - t) ^ 2 := by
    rw [hsplit1, S_add, S_add, hmid, hlast]
    grind
  rw [key]
  grind

/-- **Readable corollary**: under genuinely CONVEX weights (`w i ≥ 0` on top of `S n w = 1`),
    the subtracted ambiguity term is manifestly nonnegative, so the ensemble is never worse
    than the weighted-average member: `(fbar - t)^2 ≤ Σ w i*(f i - t)^2`. General `n`. -/
theorem krogh_vedelsby_le (n : Nat) (w f : Nat → Rat) (t : Rat)
    (hw : S n w = 1) (hnn : ∀ i, i < n → 0 ≤ w i) :
    (fbar n w f - t) ^ 2 ≤ S n (fun i => w i * (f i - t) ^ 2) := by
  have hid := krogh_vedelsby_identity n w f t hw
  have hamb_nonneg : 0 ≤ S n (fun i => w i * (f i - fbar n w f) ^ 2) := by
    apply S_nonneg
    intro i hi
    exact Rat.mul_nonneg (hnn i hi) (rat_sq_nonneg _)
  rw [hid]
  grind

/-! ### Counterexample separating the hypotheses, with strictly positive ambiguity -/

/-- Concrete `n = 2` weights: `w 0 = w 1 = 1/2`, `0` elsewhere. -/
def w2 : Nat → Rat
  | 0 => mkRat 1 2
  | 1 => mkRat 1 2
  | _ => 0

/-- Concrete `n = 2` member predictions: `f 0 = 0`, `f 1 = 2`. -/
def f2 : Nat → Rat
  | 0 => 0
  | 1 => 2
  | _ => 0

theorem w2_sum_one : S 2 w2 = 1 := by
  simp only [S_succ, S_zero, w2]
  simp only [Rat.add_def']
  decide

theorem fbar2_eq_one : fbar 2 w2 f2 = 1 := by
  unfold fbar
  simp only [S_succ, S_zero, w2, f2]
  simp only [Rat.add_def', Rat.mul_def']
  decide

/-- The convex-weight hypotheses hold for `w2`. -/
theorem w2_nonneg : ∀ i, i < 2 → 0 ≤ w2 i := by
  intro i hi
  have hi2 : i = 0 ∨ i = 1 := by omega
  rcases hi2 with rfl | rfl <;> simp only [w2] <;> decide

/-- Counterexample separating the hypotheses: at
    `w = w2`, `f = f2`, `t = 1`, the ensemble mean is `fbar = 1` (so the ensemble error is
    `0`), the ambiguity is `1 > 0`, and the weighted-average member error is `1`. The
    ensemble is strictly better than the weighted-average member — this is the qualitative
    content ("diversity helps") the name "ambiguity decomposition" is for. -/
theorem krogh_vedelsby_strict_example :
    S 2 (fun i => w2 i * (f2 i - fbar 2 w2 f2) ^ 2) > 0 ∧
    (fbar 2 w2 f2 - (1 : Rat)) ^ 2 < S 2 (fun i => w2 i * (f2 i - (1 : Rat)) ^ 2) := by
  have hfbar : fbar 2 w2 f2 = 1 := fbar2_eq_one
  constructor
  · rw [hfbar]
    simp only [S_succ, S_zero, w2, f2]
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.sub_def', Rat.mul_def', Rat.add_def']
    decide
  · rw [hfbar]
    simp only [S_succ, S_zero, w2, f2]
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.sub_def', Rat.mul_def', Rat.add_def']
    decide

end AutoproverCorpus.KroghVedelsby
