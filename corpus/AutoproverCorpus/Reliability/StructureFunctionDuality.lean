/-
  AutoproverCorpus.Reliability.StructureFunctionDuality

  The dual structure function and the cut/path duality of reliability theory. The dual of a
  structure function `phi` is `phiᴰ(x) = ¬ phi(x̄)`: the system that is up exactly when the
  original system, with every component's state flipped, is down. Four results:

  (1) `dual_dual`      — dualizing twice returns the original system.
  (2) `dual_coherent`  — the dual of a coherent (monotone, non-degenerate) system is coherent.
  (3) `dual_series_eq_parallel` / `dual_parallel_eq_series` — the dual of a series system is the
      parallel system, and conversely: the classical pair, recovered rather than assumed.
  (4) `minimalCut_iff_dual_minimalPath` — **the cut/path duality**: the minimal CUT vectors of
      `phi` are exactly the minimal PATH vectors of `phiᴰ`, under component-wise complement.
      This is the theorem that lets a cut-set analysis be run as a path-set analysis on the dual
      system, and it is proved here for an arbitrary structure function over `n` components, not
      just for a worked instance.

  Minimality is stated component-wise, in the standard form for monotone systems: a path vector
  is minimal when removing ANY up component brings the system down; a cut vector is minimal when
  repairing ANY down component brings the system up.

  TERMINOLOGY: "coherent" is the `Coherent` predicate imported from `PivotalDecomposition` —
  monotone and non-degenerate, what much of the modern literature calls "semicoherent" (see the
  note at the root of that module). Nothing below uses a relevance hypothesis.

  Attribution: Classical reliability theory (Barlow and Proschan, 1975; the dual structure
  function and the minimal-cut/minimal-path correspondence).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Reliability.CoherentSystemBounds

namespace AutoproverCorpus.StructureFunctionDuality

-- Selective open: `PivotalDecomposition` also defines `seriesPhi`/`parallelPhi` (at a fixed
-- arity), so only the three names actually used are brought in from it, and the general
-- series/parallel systems come from `CoherentSystemBounds`.
open AutoproverCorpus.PivotalDecomposition (Monotone Coherent update)
open AutoproverCorpus.CoherentSystemBounds

/-! ### The complement of a state, and the dual system -/

/-- Component-wise complement of a state vector: every up component goes down and vice versa. -/
def compl {n : Nat} (x : Fin n → Bool) : Fin n → Bool := fun i => !(x i)

/-- The dual structure function: `phiᴰ(x) = ¬ phi(x̄)`. -/
def dual {n : Nat} (phi : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => !(phi (compl x))

theorem compl_compl {n : Nat} (x : Fin n → Bool) : compl (compl x) = x := by
  funext i; simp [compl]

/-- Complementing turns the all-down state into the all-up state. -/
theorem compl_allFalse {n : Nat} : compl (fun _ : Fin n => false) = (fun _ => true) := by
  funext i; rfl

theorem compl_allTrue {n : Nat} : compl (fun _ : Fin n => true) = (fun _ => false) := by
  funext i; rfl

/-- Complement turns overriding a component down into overriding it up, and vice versa. -/
theorem compl_update {n : Nat} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    compl (update x i b) = update (compl x) i (!b) := by
  funext j
  unfold compl update
  by_cases h : j = i <;> simp [h]

/-- **(1) Duality is an involution.** -/
theorem dual_dual {n : Nat} (phi : (Fin n → Bool) → Bool) : dual (dual phi) = phi := by
  funext x
  simp [dual, compl_compl]

/-! ### (2) The dual of a coherent system is coherent -/

/-- Complement reverses the component-wise order. -/
theorem compl_antitone {n : Nat} {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
    ∀ i, compl y i = true → compl x i = true := by
  intro i hi
  unfold compl at hi ⊢
  cases hx : x i with
  | false => rfl
  | true => rw [h i hx] at hi; exact absurd hi (by simp)

/-- The dual of a monotone system is monotone: raising a component in the dual lowers it in the
    original, and the original's monotonicity carries the conclusion back. -/
theorem dual_monotone {n : Nat} {phi : (Fin n → Bool) → Bool} (hmono : Monotone phi) :
    Monotone (dual phi) := by
  intro x y hxy hx
  unfold dual at hx ⊢
  have hnot : phi (compl x) = false := by
    cases h : phi (compl x) with
    | false => rfl
    | true => rw [h] at hx; exact absurd hx (by simp)
  have hy : phi (compl y) = false := by
    cases h : phi (compl y) with
    | false => rfl
    | true =>
      have := hmono (compl y) (compl x) (compl_antitone hxy) h
      rw [this] at hnot
      exact absurd hnot (by simp)
  rw [hy]; rfl

/-- **(2) The dual of a coherent system is coherent.** The two non-degeneracy conditions swap
    roles: `phiᴰ` is down when all components are down because `phi` is up when all are up, and
    vice versa. -/
theorem dual_coherent {n : Nat} {phi : (Fin n → Bool) → Bool} (hc : Coherent phi) :
    Coherent (dual phi) where
  mono := dual_monotone hc.mono
  allFalse := by simp [dual, compl_allFalse, hc.allTrue]
  allTrue := by simp [dual, compl_allTrue, hc.allFalse]

/-! ### (3) Series and parallel are each other's duals -/

/-- **The dual of the series system is the parallel system.** The series system is up iff every
    component is up; complementing, its dual is up iff some component is up. -/
theorem dual_series_eq_parallel {n : Nat} : dual (seriesPhi (n := n)) = parallelPhi := by
  funext x
  cases hpar : parallelPhi x with
  | true =>
    obtain ⟨i, hi⟩ := (parallelPhi_iff x).mp hpar
    have hser : seriesPhi (compl x) = false := by
      cases hs : seriesPhi (compl x) with
      | false => rfl
      | true =>
        have := (seriesPhi_iff (compl x)).mp hs i
        unfold compl at this
        rw [hi] at this
        exact absurd this (by simp)
    simp [dual, hser]
  | false =>
    have hall : ∀ i, compl x i = true := by
      intro i
      unfold compl
      cases hx : x i with
      | false => rfl
      | true =>
        have : parallelPhi x = true := (parallelPhi_iff x).mpr ⟨i, hx⟩
        rw [hpar] at this
        exact absurd this (by simp)
    have hser : seriesPhi (compl x) = true := (seriesPhi_iff (compl x)).mpr hall
    simp [dual, hser]

/-- **The dual of the parallel system is the series system**, by involutivity. -/
theorem dual_parallel_eq_series {n : Nat} : dual (parallelPhi (n := n)) = seriesPhi := by
  have h := congrArg dual (dual_series_eq_parallel (n := n))
  rw [dual_dual] at h
  exact h.symm

/-! ### (4) Cut/path duality -/

/-- A path vector: a component state at which the system is up. -/
def IsPath {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop := phi x = true

/-- A cut vector: a component state at which the system is down. -/
def IsCut {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop := phi x = false

/-- A MINIMAL path vector: the system is up, and taking down any single up component brings it
    down — no proper sub-collection of the working components keeps the system up. -/
def MinimalPath {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop :=
  phi x = true ∧ ∀ i, x i = true → phi (update x i false) = false

/-- A MINIMAL cut vector: the system is down, and repairing any single down component brings it
    up — no proper sub-collection of the failed components suffices to fail the system. -/
def MinimalCut {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop :=
  phi x = false ∧ ∀ i, x i = false → phi (update x i true) = true

/-- The unminimized half of the duality: a state cuts `phi` exactly when its complement is a
    path of `phiᴰ`. -/
theorem cut_iff_dual_path {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    IsCut phi x ↔ IsPath (dual phi) (compl x) := by
  unfold IsCut IsPath dual
  rw [compl_compl]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    cases hx : phi x with
    | false => rfl
    | true => rw [hx] at h; exact absurd h (by simp)

/-- **The cut/path duality (main theorem).** The minimal cut vectors of a system are exactly
    the minimal path vectors of its dual, under component-wise complement. Each clause matches:
    "the system is down" becomes "the dual is up"; "repairing a failed component brings the
    system up" becomes "removing a working component brings the dual down" — because
    complementing an override of `i` to `true` is an override of `i` to `false`. -/
theorem minimalCut_iff_dual_minimalPath {n : Nat} (phi : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : MinimalCut phi x ↔ MinimalPath (dual phi) (compl x) := by
  unfold MinimalCut MinimalPath dual
  rw [compl_compl]
  constructor
  · intro ⟨h0, h1⟩
    refine ⟨by rw [h0]; rfl, ?_⟩
    intro i hi
    have hxi : x i = false := by
      unfold compl at hi
      cases hx : x i with
      | false => rfl
      | true => rw [hx] at hi; exact absurd hi (by simp)
    rw [compl_update, compl_compl]
    simp only [Bool.not_false]
    rw [h1 i hxi]
    rfl
  · intro ⟨h0, h1⟩
    have hx0 : phi x = false := by
      cases hx : phi x with
      | false => rfl
      | true => rw [hx] at h0; exact absurd h0 (by simp)
    refine ⟨hx0, ?_⟩
    intro i hi
    have hci : compl x i = true := by unfold compl; rw [hi]; rfl
    have h := h1 i hci
    rw [compl_update, compl_compl] at h
    simp only [Bool.not_false] at h
    cases hu : phi (update x i true) with
    | true => rfl
    | false => rw [hu] at h; exact absurd h (by simp)

/-! ### Instance: the 2-out-of-3 majority system is self-dual -/

/-- The 2-out-of-3 majority system (reused from `CoherentSystemBounds`) is its own dual: a
    majority of three components is up exactly when a majority is not down. This is the smallest
    case of the classical fact that a k-out-of-n system's dual is the (n−k+1)-out-of-n system,
    which is self-dual exactly when `n = 2k − 1`; only this instance is verified here, the
    general k-out-of-n identity is not claimed. -/
theorem majority3_self_dual : dual majority3 = majority3 := by
  funext x
  unfold dual compl majority3
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> simp [h0, h1, h2]

/-- Non-vacuity for the duality: a genuine minimal cut of the majority system — components `0`
    and `1` down, `2` up, is a cut (no pair is up), and repairing either failed component makes
    a pair — matched by the corresponding minimal path of the dual under complement. -/
example : MinimalCut majority3 (fun i => i.val = 2) := by
  unfold MinimalCut
  decide

/-- Series and parallel are genuinely different systems, so result (3) is not the identity in
    disguise: at a state with one component up out of three, the parallel system is up and the
    series system is down. -/
example : parallelPhi (n := 3) (fun i => i.val = 0) = true ∧
    seriesPhi (n := 3) (fun i => i.val = 0) = false := by decide

end AutoproverCorpus.StructureFunctionDuality
