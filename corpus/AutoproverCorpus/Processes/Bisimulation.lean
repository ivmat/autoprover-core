/-
  AutoproverCorpus.Processes.Bisimulation

  Bisimilarity is an equivalence relation: the identity is a bisimulation, and converses and
  compositions of bisimulations are bisimulations.

  Attribution: Classical (Park, 1981; Milner).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.Bisimulation

variable {S : Type} {Act : Type}

-- A labelled transition system: `step x a y` means state `x` can perform action `a` and
-- land in state `y`.
variable (step : S → Act → S → Prop)

/-- `R` is a (strong) bisimulation on `step`: for every related pair, every step from
    either side is matched by a step from the other side landing in related states. -/
def IsBisimulation (R : S → S → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ a x', step x a x' → ∃ y', step y a y' ∧ R x' y') ∧
    (∀ a y', step y a y' → ∃ x', step x a x' ∧ R x' y')

/-- Two states are bisimilar if some bisimulation relates them. -/
def Bisim (x y : S) : Prop := ∃ R, IsBisimulation step R ∧ R x y

variable {step}

/-! ### (a) Reflexivity: the identity relation is a bisimulation -/

theorem eq_isBisimulation : IsBisimulation step (Eq (α := S)) := by
  intro x y hxy
  subst hxy
  exact ⟨fun a x' hx' => ⟨x', hx', rfl⟩, fun a y' hy' => ⟨y', hy', rfl⟩⟩

theorem bisim_refl (x : S) : Bisim step x x :=
  ⟨Eq, eq_isBisimulation, rfl⟩

/-! ### (b) Symmetry: `flip` of a bisimulation is a bisimulation -/

theorem flip_isBisimulation {R : S → S → Prop} (hR : IsBisimulation step R) :
    IsBisimulation step (flip R) := by
  intro x y hxy
  have h := hR y x hxy
  exact ⟨h.2, h.1⟩

theorem bisim_symm {x y : S} (h : Bisim step x y) : Bisim step y x := by
  obtain ⟨R, hR, hxy⟩ := h
  exact ⟨flip R, flip_isBisimulation hR, hxy⟩

/-! ### (c) Transitivity: relational composition of two bisimulations is a bisimulation -/

/-- Relational composition: `x` and `z` are related through some intermediate `y`. -/
def RelComp (R1 R2 : S → S → Prop) (x z : S) : Prop := ∃ y, R1 x y ∧ R2 y z

theorem relComp_isBisimulation {R1 R2 : S → S → Prop}
    (hR1 : IsBisimulation step R1) (hR2 : IsBisimulation step R2) :
    IsBisimulation step (RelComp R1 R2) := by
  intro x z hxz
  obtain ⟨y, hxy, hyz⟩ := hxz
  refine ⟨?_, ?_⟩
  · intro a x' hx'
    obtain ⟨y', hy', hxy'⟩ := (hR1 x y hxy).1 a x' hx'
    obtain ⟨z', hz', hyz'⟩ := (hR2 y z hyz).1 a y' hy'
    exact ⟨z', hz', y', hxy', hyz'⟩
  · intro a z' hz'
    obtain ⟨y', hy', hyz'⟩ := (hR2 y z hyz).2 a z' hz'
    obtain ⟨x', hx', hxy'⟩ := (hR1 x y hxy).2 a y' hy'
    exact ⟨x', hx', y', hxy', hyz'⟩

theorem bisim_trans {x y z : S} (hxy : Bisim step x y) (hyz : Bisim step y z) :
    Bisim step x z := by
  obtain ⟨R1, hR1, hxy'⟩ := hxy
  obtain ⟨R2, hR2, hyz'⟩ := hyz
  exact ⟨RelComp R1 R2, relComp_isBisimulation hR1 hR2, y, hxy', hyz'⟩

/-! ### (d) Packaged as an `Equivalence` -/

theorem bisim_equivalence : Equivalence (Bisim step) :=
  ⟨bisim_refl, bisim_symm, bisim_trans⟩

/-! ### (e) Instances: concrete bisimilar and non-bisimilar systems -/

section Instances

/-- A single action label (all systems below use only one action). -/
abbrev BAct := Unit

/-! #### A bisimilar-but-distinct pair: one-state self-loop vs two-state cycle -/

/-- States for the bisimilar example: `p` is a one-state self-loop; `q1, q2` form a
    two-state cycle on the same single action. -/
inductive BEx where
  | p | q1 | q2
deriving DecidableEq

/-- Concrete step relation: `p` self-loops; `q1 → q2 → q1` cycles. -/
abbrev bStep : BEx → BAct → BEx → Prop
  | .p, (), .p => True
  | .q1, (), .q2 => True
  | .q2, (), .q1 => True
  | _, _, _ => False

/-- The relation witnessing `p ~ q1` and `p ~ q2`: `p`'s constant self-loop always
    matches whichever cycle state it is compared against, since each cycle state has
    exactly one outgoing step landing in the OTHER cycle state. -/
abbrev bR : BEx → BEx → Prop
  | .p, .q1 => True
  | .p, .q2 => True
  | _, _ => False

theorem bR_isBisimulation : IsBisimulation bStep bR := by
  intro x y hxy
  have hcase : (x = .p ∧ y = .q1) ∨ (x = .p ∧ y = .q2) := by
    cases x <;> cases y <;> simp_all [bR]
  rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy
  · refine ⟨?_, ?_⟩
    · intro a x' hx'
      cases a
      have hx'p : x' = .p := by cases x' <;> simp_all [bStep]
      subst hx'p
      exact ⟨.q2, by decide, by decide⟩
    · intro a y' hy'
      cases a
      have hy'q2 : y' = .q2 := by cases y' <;> simp_all [bStep]
      subst hy'q2
      exact ⟨.p, by decide, by decide⟩
  · refine ⟨?_, ?_⟩
    · intro a x' hx'
      cases a
      have hx'p : x' = .p := by cases x' <;> simp_all [bStep]
      subst hx'p
      exact ⟨.q1, by decide, by decide⟩
    · intro a y' hy'
      cases a
      have hy'q1 : y' = .q1 := by cases y' <;> simp_all [bStep]
      subst hy'q1
      exact ⟨.p, by decide, by decide⟩

/-- `p` and `q1` are distinct states. -/
example : BEx.p ≠ BEx.q1 := by decide

/-- `p` and `q1` are nonetheless bisimilar. -/
example : Bisim bStep BEx.p BEx.q1 :=
  ⟨bR, bR_isBisimulation, by decide⟩

/-! #### A concrete NON-bisimilar pair: can-do-the-action vs deadlocked -/

/-- States for the non-bisimilar example: `canDo` can perform the (only) action and
    self-loops; `cannotDo` is deadlocked and can perform no action at all. -/
inductive CEx where
  | canDo | cannotDo
deriving DecidableEq

/-- Concrete step relation: only `canDo` has any outgoing step. -/
abbrev cStep : CEx → BAct → CEx → Prop
  | .canDo, (), .canDo => True
  | _, _, _ => False

/-- A state able to perform an action and a deadlocked state are NOT bisimilar: any
    bisimulation relating them would have to match `canDo`'s step with SOME step from
    `cannotDo`, but `cannotDo` has none. -/
theorem canDo_not_bisim_cannotDo : ¬ Bisim cStep CEx.canDo CEx.cannotDo := by
  intro h
  obtain ⟨R, hR, hrel⟩ := h
  have hstep : cStep CEx.canDo () CEx.canDo := by decide
  obtain ⟨y', hy', _⟩ := (hR CEx.canDo CEx.cannotDo hrel).1 () CEx.canDo hstep
  cases y' <;> exact absurd hy' (by decide)

end Instances

end AutoproverCorpus.Bisimulation
