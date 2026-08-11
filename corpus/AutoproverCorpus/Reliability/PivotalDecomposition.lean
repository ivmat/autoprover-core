/-
  AutoproverCorpus.Reliability.PivotalDecomposition

  Pivotal decomposition of monotone Boolean structure functions, with the series and parallel
  bounds.

  Attribution: Classical (Birnbaum; Barlow and Proschan).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.PivotalDecomposition

def Monotone {n : Nat} (phi : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → phi x = true → phi y = true

def update {n : Nat} (x : Fin n → Bool) (i : Fin n) (b : Bool) : Fin n → Bool :=
  fun j => if j = i then b else x j

/-- Overriding coordinate `i` with its own current value is a no-op. -/
theorem update_self {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    update x i (x i) = x := by
  funext j
  unfold update
  by_cases h : j = i <;> simp [h]

/-- (1) Pivotal (Shannon) decomposition, Boolean form: pivoting `phi` on coordinate `i`
    splits it into the "`i` is up" branch (`update x i true`) and the "`i` is down" branch
    (`update x i false`), selected by the actual value `x i`. Proved by cases on `x i`,
    using that overriding `i` with its own value returns `x` unchanged. -/
theorem pivotal_decomposition {n : Nat} (phi : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (i : Fin n) :
    phi x = ((x i && phi (update x i true)) || (!x i && phi (update x i false))) := by
  rcases hxi : x i with _ | _
  · have h : update x i false = x := by rw [← hxi]; exact update_self x i
    rw [h]; simp
  · have h : update x i true = x := by rw [← hxi]; exact update_self x i
    rw [h]; simp

/-- (2a) Floor direction: if the all-false vector already makes `phi` true (a degenerate
    hypothesis for a genuine "always-up" `phi`), monotonicity forces `phi x = true` for
    every `x`, since `fun _ => false` is pointwise `≤` any `x` vacuously
    (`false = true → _` is vacuously true at every coordinate). -/
theorem floor_bound {n : Nat} (phi : (Fin n → Bool) → Bool) (hmono : Monotone phi)
    (x : Fin n → Bool) (h0 : phi (fun _ => false) = true) : phi x = true :=
  hmono (fun _ => false) x (fun _ hi => absurd hi (by simp)) h0

/-- (2b) Ceiling direction: `phi x = true` forces `phi (fun _ => true) = true`, since `x`
    is pointwise `≤` the all-true vector trivially (`_ → true` always holds). Together with
    `floor_bound`, this is the implication-form of the classical bound
    `phi(all-false) ≤ phi x ≤ phi(all-true)`. -/
theorem ceil_bound {n : Nat} (phi : (Fin n → Bool) → Bool) (hmono : Monotone phi)
    (x : Fin n → Bool) (hx : phi x = true) : phi (fun _ => true) = true :=
  hmono x (fun _ => true) (fun _ _ => rfl) hx

/-- (3) Series-floor equality: for a monotone `phi`, any all-true vector `x` (i.e. every
    component up) makes `phi` agree exactly with the canonical all-true vector — not just
    `≤` (via `ceil_bound`) but `=`, using the reverse pointwise inequality `(fun _ => true)
    ≤ x` (which holds since `x` IS all-true) together with `ceil_bound`. -/
theorem all_true_eq {n : Nat} (phi : (Fin n → Bool) → Bool) (hmono : Monotone phi)
    (x : Fin n → Bool) (hx : ∀ i, x i = true) : phi x = phi (fun _ => true) := by
  have h1 := ceil_bound phi hmono x
  have h2 := hmono (fun _ => true) x (fun i _ => hx i)
  cases hxx : phi x <;> cases hyy : phi (fun (_ : Fin n) => true) <;> simp_all

/-- A coherent system: monotone, plus the two nontriviality normalizations — all-down stays
    down and all-up stays up. (Barlow–Proschan's usual strengthening of "monotone
    structure function" to a genuine, non-degenerate reliability system.) -/
structure Coherent {n : Nat} (phi : (Fin n → Bool) → Bool) : Prop where
  mono      : Monotone phi
  allFalse  : phi (fun _ => false) = false
  allTrue   : phi (fun _ => true) = true

/-- (4a) The all-true corollary for coherent systems: every component up makes the system
    up (`all_true_eq` specialized via `allTrue`). -/
theorem coherent_all_true {n : Nat} {phi : (Fin n → Bool) → Bool} (hc : Coherent phi)
    (x : Fin n → Bool) (hx : ∀ i, x i = true) : phi x = true := by
  rw [all_true_eq phi hc.mono x hx, hc.allTrue]

/-- (4b) The classical "min_i x_i ≤ phi(x)" content, stated existentially: for a coherent
    system, `phi x = true` forces SOME component to be up — the system cannot be up while
    every component is down, since that would make `phi x = phi (fun _ => false) = false`
    by the `allFalse` normalization, contradicting `phi x = true`. -/
theorem coherent_true_imp_exists {n : Nat} {phi : (Fin n → Bool) → Bool} (hc : Coherent phi)
    (x : Fin n → Bool) (hx : phi x = true) : ∃ i, x i = true := by
  by_cases hcon : ∃ i, x i = true
  · exact hcon
  · exfalso
    have hall : ∀ i, x i = false := by
      intro i
      cases h : x i with
      | false => rfl
      | true => exact absurd ⟨i, h⟩ hcon
    have hxeq : x = (fun _ => false) := funext hall
    rw [hxeq, hc.allFalse] at hx
    exact Bool.false_ne_true hx

-- (5) Instances: the 2-component series (`AND`) and parallel (`OR`) systems.

/-- The 2-component series system: up iff BOTH components are up. -/
def seriesPhi (x : Fin 2 → Bool) : Bool := x 0 && x 1

/-- The 2-component parallel system: up iff EITHER component is up. -/
def parallelPhi (x : Fin 2 → Bool) : Bool := x 0 || x 1

theorem seriesPhi_monotone : Monotone seriesPhi := by
  intro x y h hx
  unfold seriesPhi at *
  rcases Bool.and_eq_true_iff.mp hx with ⟨hx0, hx1⟩
  simp [h 0 hx0, h 1 hx1]

theorem parallelPhi_monotone : Monotone parallelPhi := by
  intro x y h hx
  unfold parallelPhi at *
  rcases Bool.or_eq_true_iff.mp hx with hx0 | hx1
  · simp [h 0 hx0]
  · simp [h 1 hx1]

theorem seriesPhi_coherent : Coherent seriesPhi :=
  { mono := seriesPhi_monotone
    allFalse := by decide
    allTrue := by decide }

theorem parallelPhi_coherent : Coherent parallelPhi :=
  { mono := parallelPhi_monotone
    allFalse := by decide
    allTrue := by decide }

/-- A concrete 2-vector, component 0 up and component 1 down, for the decomposition
    instances below. -/
def vTF : Fin 2 → Bool := fun i => if i = 0 then true else false

/-- Concrete instance of (1) for the series system, pivoting on coordinate 0, checked by
    `decide` on `vTF` (`vTF 0 = true, vTF 1 = false`, so `seriesPhi vTF = false`). -/
theorem seriesPhi_pivotal_vTF :
    seriesPhi vTF =
      ((vTF 0 && seriesPhi (update vTF 0 true)) || (!vTF 0 && seriesPhi (update vTF 0 false))) := by
  decide

/-- Concrete instance of (1) for the parallel system, pivoting on coordinate 1, checked by
    `decide` on `vTF` (`vTF 0 = true, vTF 1 = false`, so `parallelPhi vTF = true`). -/
theorem parallelPhi_pivotal_vTF :
    parallelPhi vTF =
      ((vTF 1 && parallelPhi (update vTF 1 true)) || (!vTF 1 && parallelPhi (update vTF 1 false))) := by
  decide

end AutoproverCorpus.PivotalDecomposition
