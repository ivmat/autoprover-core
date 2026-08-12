/-
  AutoproverCorpus.Reliability.KOutOfN

  The k-out-of-n structure function (the system is up iff at least k of its n components are
  up) is monotone: raising any component from down to up never turns an up system down. The
  series (n-out-of-n, all components must be up) and parallel (1-out-of-n, some component
  suffices) systems are the two extreme special cases, recovered as corollaries.

  Attribution: Classical reliability theory (Birnbaum, 1969; Barlow and Proschan, 1975).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Reliability.PivotalDecomposition

namespace AutoproverCorpus.KOutOfN

open AutoproverCorpus.PivotalDecomposition

/-! ### The structure function -/

/-- The number of up (`true`) components of a state vector, over `Fin n`. -/
def upCount {n : Nat} (x : Fin n → Bool) : Nat :=
  (List.finRange n).countP (fun i => x i)

/-- The k-out-of-n structure function: the system is up iff at least `k` of the `n`
    components are up. -/
def kOutOfN {n : Nat} (k : Nat) (x : Fin n → Bool) : Bool :=
  decide (k ≤ upCount x)

/-! ### Monotonicity -/

/-- `upCount` is monotone under the pointwise "down → up" order on state vectors: raising any
    subset of components from down to up cannot decrease the count of up components. Proved by
    `List.countP_mono_left` on the `finRange n` list underlying `upCount`. -/
theorem upCount_mono {n : Nat} {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
    upCount x ≤ upCount y :=
  List.countP_mono_left (fun i _ hi => h i hi)

/-- **Monotonicity of the k-out-of-n system.** Raising any component from down to up (or,
    more generally, any pointwise "down → up" change of state) never turns an up system down —
    the classical coherence property of a k-out-of-n system, for every fixed threshold `k`. -/
theorem kOutOfN_monotone {n : Nat} (k : Nat) : Monotone (kOutOfN (n := n) k) := by
  intro x y hxy hx
  unfold kOutOfN at hx ⊢
  have hle : upCount x ≤ upCount y := upCount_mono hxy
  exact decide_eq_true (Nat.le_trans (of_decide_eq_true hx) hle)

/-! ### Series and parallel as the two extreme special cases -/

/-- **n-out-of-n = series.** The n-out-of-n system is up iff EVERY component is up: the
    classical series system, needing all `n` components. -/
theorem kOutOfN_n_iff_series {n : Nat} (x : Fin n → Bool) :
    kOutOfN n x = true ↔ ∀ i, x i = true := by
  unfold kOutOfN upCount
  rw [decide_eq_true_iff]
  have hlen : (List.finRange n).length = n := List.length_finRange
  have hle : (List.finRange n).countP (fun i => x i) ≤ (List.finRange n).length :=
    List.countP_le_length
  constructor
  · intro h
    have heqlen : (List.finRange n).countP (fun i => x i) = (List.finRange n).length := by omega
    intro i
    exact (List.countP_eq_length.mp heqlen) i (List.mem_finRange i)
  · intro h
    have heqlen : (List.finRange n).countP (fun i => x i) = (List.finRange n).length :=
      List.countP_eq_length.mpr (fun a _ => h a)
    omega

/-- **1-out-of-n = parallel.** The 1-out-of-n system is up iff SOME component is up: the
    classical parallel system, needing only one working component. -/
theorem kOutOfN_one_iff_parallel {n : Nat} (x : Fin n → Bool) :
    kOutOfN 1 x = true ↔ ∃ i, x i = true := by
  unfold kOutOfN upCount
  rw [decide_eq_true_iff]
  have hiff : (1 ≤ (List.finRange n).countP (fun i => x i)) ↔
      (0 < (List.finRange n).countP (fun i => x i)) := by omega
  rw [hiff, List.countP_pos_iff]
  constructor
  · rintro ⟨i, _, hi⟩; exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, List.mem_finRange i, hi⟩

/-! ### Instances: a concrete 3-component 2-out-of-3 system -/

/-- A concrete 3-component vector: components `0` and `1` up, component `2` down. -/
def vTTF : Fin 3 → Bool := fun i => i.val ≠ 2

/-- With 2 of 3 components up, the 2-out-of-3 system is up. -/
example : kOutOfN 2 vTTF = true := by decide

/-- With only 2 of 3 components up, the 3-out-of-3 (series) system is down. -/
example : kOutOfN 3 vTTF = false := by decide

/-- With 2 of 3 components up, the 1-out-of-3 (parallel) system is up. -/
example : kOutOfN 1 vTTF = true := by decide

/-- Monotonicity, concretely: raising the one down component (`2`) of `vTTF` to up keeps the
    2-out-of-3 system up — an instance of `kOutOfN_monotone`, not just its abstract shape. -/
example :
    kOutOfN 2 vTTF = true →
      kOutOfN 2 (fun i => if i = (2 : Fin 3) then true else vTTF i) = true := by decide

/-- The all-down vector fails every positive threshold, including the parallel (1-out-of-n)
    case — the threshold is not vacuous. -/
example : kOutOfN 1 (fun _ : Fin 3 => false) = false := by decide

end AutoproverCorpus.KOutOfN
