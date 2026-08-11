/-
  AutoproverCorpus.Probability.AssociationClosure

  Closure properties of associated random variables over an abstract expectation functional:
  subsets of associated families are associated, and monotone images of associated families are
  associated.

  Attribution: Classical (Esary, Proschan and Walkup, 1967).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.AssociationClosure

variable {Ω ι ι' : Type}

/-- Pointwise (coordinatewise) order on value-vectors indexed by `ι`. -/
def PtLE (x y : ι → Rat) : Prop := ∀ i, x i ≤ y i

/-- A real-valued function of a value-vector is *nondecreasing* if it respects the
    coordinatewise order (EPW's "nondecreasing function", Def 1.1, p.1466). -/
def Nondecreasing (f : (ι → Rat) → Rat) : Prop :=
  ∀ x y, PtLE x y → f x ≤ f y

/-- Definition 1.1 (p.1466): `X : ι → Ω → Rat` is associated w.r.t. abstract
    expectation `E` iff `Cov[f(X), g(X)] ≥ 0` for every pair of nondecreasing
    test functions `f, g`. -/
def Associated (E : (Ω → Rat) → Rat) (X : ι → Ω → Rat) : Prop :=
  ∀ f g : (ι → Rat) → Rat, Nondecreasing f → Nondecreasing g →
    E (fun ω => f (fun i => X i ω) * g (fun i => X i ω)) ≥
      E (fun ω => f (fun i => X i ω)) * E (fun ω => g (fun i => X i ω))

/-- Composition-of-nondecreasing bookkeeping underlying P1: precomposing a
    nondecreasing function of a subfamily with a reindexing map `e` gives a
    nondecreasing function of the whole family. -/
theorem nondecreasing_reindex (e : ι' → ι) {f' : (ι' → Rat) → Rat}
    (hf' : Nondecreasing f') :
    Nondecreasing (fun x : ι → Rat => f' (fun i' => x (e i'))) := by
  intro x y hxy
  exact hf' (fun i' => x (e i')) (fun i' => y (e i')) (fun i' => hxy (e i'))

/-- P1 closure fact, general reindexing form: if `X` is associated, so is `X`
    reindexed along ANY `e : ι' → ι` (the algebraic proof does not need `e`
    injective — see `associated_subset` for the genuine-subfamily statement). -/
theorem associated_reindex (E : (Ω → Rat) → Rat) (X : ι → Ω → Rat) (e : ι' → ι)
    (hX : Associated E X) :
    Associated E (fun i' ω => X (e i') ω) := by
  intro f' g' hf' hg'
  have hf : Nondecreasing (fun x : ι → Rat => f' (fun i' => x (e i'))) :=
    nondecreasing_reindex e hf'
  have hg : Nondecreasing (fun x : ι → Rat => g' (fun i' => x (e i'))) :=
    nondecreasing_reindex e hg'
  exact hX (fun x => f' (fun i' => x (e i'))) (fun x => g' (fun i' => x (e i')))
    hf hg

/-- P1 (EPW p.1466): "Any subset of associated random variables are associated."
    `e : ι' → ι` injective realizes the subfamily (distinct indices ↦ distinct
    coordinates, matching "subset"); the algebraic content is
    `associated_reindex`, which does not itself use injectivity. -/
theorem associated_subset (E : (Ω → Rat) → Rat) (X : ι → Ω → Rat) (e : ι' → ι)
    (_hinj : Function.Injective e) (hX : Associated E X) :
    Associated E (fun i' ω => X (e i') ω) :=
  associated_reindex E X e hX

/-- Composition-of-nondecreasing bookkeeping underlying P4: a nondecreasing
    function of a family of coordinatewise-nondecreasing functions is itself
    nondecreasing in the underlying coordinates. -/
theorem nondecreasing_comp_family {F : ι' → (ι → Rat) → Rat}
    (hF : ∀ j, Nondecreasing (F j)) {f' : (ι' → Rat) → Rat} (hf' : Nondecreasing f') :
    Nondecreasing (fun x : ι → Rat => f' (fun j => F j x)) := by
  intro x y hxy
  exact hf' (fun j => F j x) (fun j => F j y) (fun j => hF j x y hxy)

/-- P4 (EPW pp.1466-67): "Nondecreasing functions of associated random variables
    are associated." Formalized as: given `X` associated and a family
    `F : ι' → (ι → Rat) → Rat` of coordinatewise-nondecreasing functions, the
    composed family `fun j ω => F j (fun i => X i ω)` is associated. -/
theorem associated_compose (E : (Ω → Rat) → Rat) (X : ι → Ω → Rat)
    (F : ι' → (ι → Rat) → Rat) (hF : ∀ j, Nondecreasing (F j))
    (hX : Associated E X) :
    Associated E (fun j ω => F j (fun i => X i ω)) := by
  intro f' g' hf' hg'
  have hf : Nondecreasing (fun x : ι → Rat => f' (fun j => F j x)) :=
    nondecreasing_comp_family hF hf'
  have hg : Nondecreasing (fun x : ι → Rat => g' (fun j => F j x)) :=
    nondecreasing_comp_family hF hg'
  exact hX (fun x => f' (fun j => F j x)) (fun x => g' (fun j => F j x)) hf hg

end AutoproverCorpus.AssociationClosure
