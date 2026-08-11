/-
  AutoproverCorpus.Order.KnasterTarski

  The Knaster-Tarski least fixed point over sets-as-predicates: a monotone operator on subsets
  has a least fixed point, which is also the least pre-fixed point.

  Attribution: Classical (Knaster, 1928; Tarski, 1955).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.KnasterTarski

def Set (α : Type) := α → Prop

namespace Set

instance {α : Type} : HasSubset (Set α) where
  Subset s t := ∀ x, s x → t x

theorem subset_def {α : Type} {s t : Set α} : s ⊆ t ↔ ∀ x, s x → t x := Iff.rfl

/-- Set equality from pointwise `↔` — `funext` + `propext` (both core; see header). -/
theorem ext {α : Type} {s t : Set α} (h : ∀ x, s x ↔ t x) : s = t :=
  funext (fun x => propext (h x))

theorem subset_refl {α : Type} (s : Set α) : s ⊆ s := fun _ h => h

theorem subset_trans {α : Type} {s t u : Set α} (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u :=
  fun x hx => h2 x (h1 x hx)

end Set

def sInter {α : Type} (𝒮 : Set (Set α)) : Set α := fun x => ∀ s, 𝒮 s → s x

/-- `f` is monotone: `s ⊆ t → f s ⊆ f t`. -/
def Monotone {α : Type} (f : Set α → Set α) : Prop := ∀ s t : Set α, s ⊆ t → f s ⊆ f t

/-- The least fixpoint of `f` — the intersection of all its pre-fixpoints. -/
def lfp {α : Type} (f : Set α → Set α) : Set α := fun x => ∀ s : Set α, f s ⊆ s → s x

theorem lfp_eq_sInter {α : Type} (f : Set α → Set α) :
    lfp f = sInter (fun s => f s ⊆ s) := rfl

/-! ### (d) Leastness — proved first; purely definitional -/

/-- **(d) LEAST.** Any pre-fixpoint `s` of `f` contains `lfp f`. Needs no monotonicity —
    a direct unfolding of `lfp`'s definition as an intersection. -/
theorem lfp_least {α : Type} {f : Set α → Set α} {s : Set α} (hfs : f s ⊆ s) :
    lfp f ⊆ s := fun _ hx => hx s hfs

/-! ### (a) Pre-fixpoint -/

/-- **(a)** `lfp f` is itself a pre-fixpoint: `f (lfp f) ⊆ lfp f`. -/
theorem lfp_prefixpoint {α : Type} {f : Set α → Set α} (hf : Monotone f) :
    f (lfp f) ⊆ lfp f := by
  intro x hx s hfs
  have hle : lfp f ⊆ s := lfp_least hfs
  have hmono : f (lfp f) ⊆ f s := hf (lfp f) s hle
  exact hfs x (hmono x hx)

/-! ### (b) Post-fixpoint -/

/-- **(b)** `lfp f` is also a post-fixpoint: `lfp f ⊆ f (lfp f)`. Route: apply `f` to (a)
    itself — this shows `f (lfp f)` is ITSELF a pre-fixpoint of `f` — then apply leastness
    (d) to that pre-fixpoint. -/
theorem lfp_postfixpoint {α : Type} {f : Set α → Set α} (hf : Monotone f) :
    lfp f ⊆ f (lfp f) := by
  have hpre : f (lfp f) ⊆ lfp f := lfp_prefixpoint hf
  have hffle : f (f (lfp f)) ⊆ f (lfp f) := hf (f (lfp f)) (lfp f) hpre
  exact lfp_least hffle

/-! ### (c) The fixpoint equation -/

/-- **(c)** Hence `f (lfp f) = lfp f`: a genuine fixpoint, not merely a pre- or post-fixpoint.
    Mutual inclusion via `Set.ext` (funext/propext were not awkward here, so the equation
    form is used directly rather than the mutual-inclusion fallback). -/
theorem lfp_fixpoint {α : Type} {f : Set α → Set α} (hf : Monotone f) :
    f (lfp f) = lfp f :=
  Set.ext (fun x => ⟨fun hx => lfp_prefixpoint hf x hx, fun hx => lfp_postfixpoint hf x hx⟩)

/-! ### (e) The induction principle -/

theorem lfp_induction {α : Type} {f : Set α → Set α} {P : Set α} (hP : f P ⊆ P) :
    lfp f ⊆ P := lfp_least hP

/-! ### (f) The dual: greatest fixpoint + coinduction -/

/-- The greatest fixpoint of `f` — the union of all its post-fixpoints. -/
def gfp {α : Type} (f : Set α → Set α) : Set α := fun x => ∃ s : Set α, s ⊆ f s ∧ s x

/-- **Coinduction principle** (dual of (d)): any post-fixpoint `s` of `f` is contained in
    `gfp f`. Equally definitional, dual route. -/
theorem gfp_coinduction {α : Type} {f : Set α → Set α} {s : Set α} (hs : s ⊆ f s) :
    s ⊆ gfp f := fun _ hx => ⟨s, hs, hx⟩

/-- **Dual of (a).** `gfp f` is itself a post-fixpoint: `gfp f ⊆ f (gfp f)`. -/
theorem gfp_postfixpoint {α : Type} {f : Set α → Set α} (hf : Monotone f) :
    gfp f ⊆ f (gfp f) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hsg : s ⊆ gfp f := gfp_coinduction hs
  have hmono : f s ⊆ f (gfp f) := hf s (gfp f) hsg
  exact hmono x (hs x hsx)

/-- **Dual of (b).** `gfp f` is also a pre-fixpoint: `f (gfp f) ⊆ gfp f`. -/
theorem gfp_prefixpoint {α : Type} {f : Set α → Set α} (hf : Monotone f) :
    f (gfp f) ⊆ gfp f := by
  have hpost : gfp f ⊆ f (gfp f) := gfp_postfixpoint hf
  have hffle : f (gfp f) ⊆ f (f (gfp f)) := hf (gfp f) (f (gfp f)) hpost
  exact gfp_coinduction hffle

/-- **Dual of (c).** `gfp f = f (gfp f)`. -/
theorem gfp_fixpoint {α : Type} {f : Set α → Set α} (hf : Monotone f) :
    gfp f = f (gfp f) :=
  Set.ext (fun x => ⟨fun hx => gfp_postfixpoint hf x hx, fun hx => gfp_prefixpoint hf x hx⟩)

/-! ### (g) Instances: a reachability operator, a concrete 3-node chain -/

/-- A 3-node chain: `0 → 1 → 2`. -/
inductive ChainEdge : Fin 3 → Fin 3 → Prop
  | e01 : ChainEdge 0 1
  | e12 : ChainEdge 1 2

/-- The seed set `{0}`. -/
def seed : Set (Fin 3) := fun x => x = 0

/-- The one-step reachability operator: `x` is in the next approximation iff it is a seed
    element, or reachable in one `r`-step from something already in `s`. -/
def reachOp (r : Fin 3 → Fin 3 → Prop) (sd : Set (Fin 3)) (s : Set (Fin 3)) : Set (Fin 3) :=
  fun x => sd x ∨ ∃ y, s y ∧ r y x

/-- `reachOp r sd` is monotone in `s`, for any `r`, `sd`. -/
theorem reachOp_monotone (r : Fin 3 → Fin 3 → Prop) (sd : Set (Fin 3)) :
    Monotone (reachOp r sd) := by
  intro s t hst x hx
  rcases hx with h0 | ⟨y, hy, hyx⟩
  · exact Or.inl h0
  · exact Or.inr ⟨y, hst y hy, hyx⟩

/-- The lfp of the chain's reachability operator contains the seed `0`. -/
example : lfp (reachOp ChainEdge seed) 0 := by
  apply lfp_prefixpoint (reachOp_monotone ChainEdge seed)
  exact Or.inl rfl

/-- ... contains `1` — one hop from the seed. -/
example : lfp (reachOp ChainEdge seed) 1 := by
  apply lfp_prefixpoint (reachOp_monotone ChainEdge seed)
  refine Or.inr ⟨0, ?_, ChainEdge.e01⟩
  apply lfp_prefixpoint (reachOp_monotone ChainEdge seed)
  exact Or.inl rfl

example : lfp (reachOp ChainEdge seed) 2 := by
  apply lfp_prefixpoint (reachOp_monotone ChainEdge seed)
  refine Or.inr ⟨1, ?_, ChainEdge.e12⟩
  apply lfp_prefixpoint (reachOp_monotone ChainEdge seed)
  refine Or.inr ⟨0, ?_, ChainEdge.e01⟩
  apply lfp_prefixpoint (reachOp_monotone ChainEdge seed)
  exact Or.inl rfl

end AutoproverCorpus.KnasterTarski
