/-
  AutoproverCorpus.Reliability.BirnbaumCriticality

  Birnbaum component criticality: a component is critical for a state vector iff flipping it
  flips the system, and the critical components of a state vector can be counted
  (`criticalCount`). Counting is all that is defined here: no importance ORDER over components
  is defined and no ranking theorem is proved.

  Attribution: Classical (Birnbaum, 1969).

  TERMINOLOGY note (relevance vs. the `Coherent` predicate): the criticality notion here is
  exactly the "relevance" condition that distinguishes the two standard classes of structure
  function. A component is RELEVANT iff it is critical/pivotal in at least one state, i.e.
  `∃ x, IsCritical phi x i`. The `Coherent` predicate imported from `PivotalDecomposition`
  requires only monotonicity + non-degeneracy (what much of the modern literature calls
  "semicoherent"); the STRONGER classical (Barlow–Proschan) "coherent" additionally requires
  every component to be relevant in this sense. The results in this module assume only
  monotonicity, so they hold for both classes.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Reliability.PivotalDecomposition

namespace AutoproverCorpus.BirnbaumCriticality

open AutoproverCorpus.PivotalDecomposition

/-! ### Criticality -/

/-- Component `i` is critical for structure function `phi` at state `x`: flipping `i`
    flips the system's value. -/
def IsCritical {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) (i : Fin n) : Prop :=
  phi (update x i true) ≠ phi (update x i false)

/-- The Boolean test underlying `IsCritical`, used to make `criticalCount` computable
    without threading a bespoke `Decidable (IsCritical ..)` instance. -/
def isCriticalB {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  phi (update x i true) != phi (update x i false)

/-- `isCriticalB` computes exactly `IsCritical` (the `!=`/`≠` correspondence, unfolded). -/
theorem isCriticalB_iff {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) (i : Fin n) :
    isCriticalB phi x i = true ↔ IsCritical phi x i := by
  unfold isCriticalB IsCritical
  simp [bne_iff_ne]

/-! ### (a) Criticality is exactly pivotality, for monotone `phi` -/

/-- **Crux step.** Monotonicity forbids the "reverse" pivot direction: it cannot be that
    turning `i` OFF makes the system up while turning `i` ON makes it down. -/
theorem not_reverse_critical {n : Nat} {phi : (Fin n → Bool) → Bool} (hmono : Monotone phi)
    (x : Fin n → Bool) (i : Fin n) :
    ¬ (phi (update x i true) = false ∧ phi (update x i false) = true) := by
  rintro ⟨hfalse, htrue⟩
  have hle : ∀ j, update x i false j = true → update x i true j = true := by
    intro j hj
    unfold update at hj ⊢
    by_cases hji : j = i
    · simp [hji]
    · simp [hji] at hj ⊢; exact hj
  have := hmono (update x i false) (update x i true) hle htrue
  rw [hfalse] at this
  exact Bool.false_ne_true this

/-- **(a) Criticality is exactly pivotality.** For monotone `phi`, `IsCritical phi x i`
    (the `≠` form) collapses to the ordered form: turning `i` ON makes the system `true` AND
    turning `i` OFF makes it `false` — the reverse direction is impossible by monotonicity
    (`not_reverse_critical`). -/
theorem isCritical_iff_pivotal {n : Nat} {phi : (Fin n → Bool) → Bool} (hmono : Monotone phi)
    (x : Fin n → Bool) (i : Fin n) :
    IsCritical phi x i ↔
      (phi (update x i true) = true ∧ phi (update x i false) = false) := by
  unfold IsCritical
  constructor
  · intro hne
    cases hon : phi (update x i true) <;> cases hoff : phi (update x i false) <;>
      simp_all
    · exact absurd ⟨hon, hoff⟩ (not_reverse_critical hmono x i)
  · intro ⟨hon, hoff⟩
    rw [hon, hoff]
    decide

/-! ### (b) A critical component determines the system's value -/

theorem critical_determines_system {n : Nat} {phi : (Fin n → Bool) → Bool} (hmono : Monotone phi)
    (x : Fin n → Bool) (i : Fin n) (hcrit : IsCritical phi x i) :
    phi x = x i := by
  obtain ⟨hon, hoff⟩ := (isCritical_iff_pivotal hmono x i).mp hcrit
  rw [pivotal_decomposition phi x i, hon, hoff]
  cases hxi : x i <;> simp

/-! ### (c) Counting critical components -/

/-- The number of critical components of `phi` at state `x`, over `Fin n` — computable by
    construction via `List.countP` on the Boolean test, no typeclass search needed. -/
def criticalCount {n : Nat} (phi : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Nat :=
  (List.finRange n).countP (isCriticalB phi x)

/-! ### Series/parallel sanity facts -/

/-- In the 2-component series (AND) system, component `0` is critical at `x` exactly when
    component `1` is up. -/
theorem seriesPhi_critical_iff (x : Fin 2 → Bool) :
    IsCritical seriesPhi x 0 ↔ x 1 = true := by
  unfold IsCritical seriesPhi update
  constructor
  · intro hne
    cases hx1 : x 1 <;> simp_all
  · intro hx1
    simp [hx1]

/-- In the 2-component series (AND) system, component `1` is critical at `x` exactly when
    component `0` is up. -/
theorem seriesPhi_critical_iff' (x : Fin 2 → Bool) :
    IsCritical seriesPhi x 1 ↔ x 0 = true := by
  unfold IsCritical seriesPhi update
  constructor
  · intro hne
    cases hx0 : x 0 <;> simp_all
  · intro hx0
    simp [hx0]

/-- In the 2-component parallel (OR) system, component `0` is critical at `x` exactly when
    component `1` is DOWN. -/
theorem parallelPhi_critical_iff (x : Fin 2 → Bool) :
    IsCritical parallelPhi x 0 ↔ x 1 = false := by
  unfold IsCritical parallelPhi update
  constructor
  · intro hne
    cases hx1 : x 1 <;> simp_all
  · intro hx1
    simp [hx1]

/-- In the 2-component parallel (OR) system, component `1` is critical at `x` exactly when
    component `0` is DOWN. -/
theorem parallelPhi_critical_iff' (x : Fin 2 → Bool) :
    IsCritical parallelPhi x 1 ↔ x 0 = false := by
  unfold IsCritical parallelPhi update
  constructor
  · intro hne
    cases hx0 : x 0 <;> simp_all
  · intro hx0
    simp [hx0]

/-! ### (d) Instances -/

/-- Concrete vector: component `0` up, component `1` down. -/
def vTF : Fin 2 → Bool := fun i => if i = 0 then true else false

/-- Concrete vector: both components up. -/
def vTT : Fin 2 → Bool := fun _ => true

/-- At `vTF` (`0` up, `1` down): component `0` is NOT critical (needs `1` up, per
    `seriesPhi_critical_iff`, and `1` is down here); component `1` IS critical (needs `0`
    up, per `seriesPhi_critical_iff'`, and `0` is up here) — so exactly one component is
    critical, `criticalCount = 1`. -/
example : criticalCount seriesPhi vTF = 1 := by decide

/-- At `vTT` (both up), the series system has BOTH components critical (each one's own
    partner is up) — `criticalCount = 2`. -/
example : criticalCount seriesPhi vTT = 2 := by decide

/-- At `vTF` (`0` up, `1` down), the parallel system has exactly ONE critical component
    (component `0`, since `parallelPhi_critical_iff` needs the OTHER component down, true
    for component `0`'s partner (`1`); component `1` needs its partner (`0`) down, which is
    false). -/
example : criticalCount parallelPhi vTF = 1 := by decide

/-- At the all-down vector, the parallel system has BOTH components critical (each one's
    partner is down). -/
example : criticalCount parallelPhi (fun (_ : Fin 2) => false) = 2 := by decide

/-- `critical_determines_system`, concretely: component `0` is critical for `seriesPhi` at
    `vTT` (both up), and indeed `seriesPhi vTT = vTT 0`. -/
example : seriesPhi vTT = vTT 0 := by decide

end AutoproverCorpus.BirnbaumCriticality
