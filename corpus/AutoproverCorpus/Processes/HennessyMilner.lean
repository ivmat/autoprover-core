/-
  AutoproverCorpus.Processes.HennessyMilner

  Hennessy-Milner logic (HML) on a labelled transition system: the formulas are built from
  `true`, conjunction, negation, and the modal diamond `<a>` ("some `a`-successor satisfies...").
  This module proves the EASY direction of the Hennessy-Milner theorem: bisimilar states satisfy
  exactly the same HML formulas (`bisimilar s t -> forall phi, s |= phi <-> t |= phi`), by
  induction on the structure of `phi`, reusing the bisimulation notion from
  `Processes.Bisimulation`.

  The CONVERSE direction — HML-equivalence (same formulas satisfied) implies bisimilarity — is
  the deeper half of the classical Hennessy-Milner theorem and additionally requires the
  transition system to be IMAGE-FINITE (every state has only finitely many `a`-successors, for
  every action `a`). That converse is NOT proved in this module.

  Attribution: M. Hennessy and R. Milner, "Algebraic Laws for Nondeterminism and Concurrency",
  1985 (the logical characterization of bisimulation traces to their earlier 1980 work).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Processes.Bisimulation

namespace AutoproverCorpus.HennessyMilner

open AutoproverCorpus.Bisimulation

variable {S : Type} {Act : Type}

/-- Hennessy-Milner logic formulas over action alphabet `Act`: `tt` (always true), finite
    conjunction, negation, and the modal diamond `<a> phi` ("some `a`-successor satisfies
    `phi`"). -/
inductive HML (Act : Type) where
  | tt : HML Act
  | and : HML Act → HML Act → HML Act
  | neg : HML Act → HML Act
  | dia : Act → HML Act → HML Act

variable (step : S → Act → S → Prop)

/-- Satisfaction of an HML formula at a state, defined by recursion on formula structure. -/
def Sat : S → HML Act → Prop
  | _, HML.tt => True
  | s, HML.and φ ψ => Sat s φ ∧ Sat s ψ
  | s, HML.neg φ => ¬ Sat s φ
  | s, HML.dia a φ => ∃ s', step s a s' ∧ Sat s' φ

variable {step}

/-- **Hennessy-Milner invariance under bisimulation (easy direction).** If `s` and `t` are
    bisimilar, they satisfy exactly the same HML formulas — proved by induction on the
    formula `phi`. The universal quantification over the RELATED PAIR `s t` is carried inside
    each induction case (not fixed before the induction), so the diamond case can apply the
    inductive hypothesis to the fresh successor pair produced by the bisimulation's matching
    condition. -/
theorem hml_invariant_under_bisim (φ : HML Act) :
    ∀ s t : S, Bisim step s t → (Sat step s φ ↔ Sat step t φ) := by
  induction φ with
  | tt => intro s t _; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro s t hst
      constructor
      · rintro ⟨hφ, hψ⟩
        exact ⟨(ihφ s t hst).mp hφ, (ihψ s t hst).mp hψ⟩
      · rintro ⟨hφ, hψ⟩
        exact ⟨(ihφ s t hst).mpr hφ, (ihψ s t hst).mpr hψ⟩
  | neg φ ihφ =>
      intro s t hst
      constructor
      · intro hnφ hφt
        exact hnφ ((ihφ s t hst).mpr hφt)
      · intro hnφ hφs
        exact hnφ ((ihφ s t hst).mp hφs)
  | dia a φ ihφ =>
      intro s t hst
      obtain ⟨R, hR, hRst⟩ := hst
      constructor
      · rintro ⟨s', hstep, hφs'⟩
        obtain ⟨t', hstep', hRs't'⟩ := (hR s t hRst).1 a s' hstep
        exact ⟨t', hstep', (ihφ s' t' ⟨R, hR, hRs't'⟩).mp hφs'⟩
      · rintro ⟨t', hstep, hφt'⟩
        obtain ⟨s', hstep', hRs't'⟩ := (hR s t hRst).2 a t' hstep
        exact ⟨s', hstep', (ihφ s' t' ⟨R, hR, hRs't'⟩).mpr hφt'⟩

/-- Corollary, packaged with `Bisim` applied first (the usual statement order). -/
theorem bisim_imp_hml_equiv {s t : S} (h : Bisim step s t) (φ : HML Act) :
    Sat step s φ ↔ Sat step t φ :=
  hml_invariant_under_bisim φ s t h

/-! ### Instances -/

section Instances

/-- A single action label (all systems below use only one action). -/
abbrev HAct := Unit

/-! #### Non-vacuity: bisimilar-but-distinct states satisfy the same HML formula -/

/-- States for the bisimilar example: `p` is a one-state self-loop; `q1, q2` form a
    two-state cycle on the same single action (same shape as `Processes.Bisimulation`'s
    instance, redefined locally so this module is self-contained beyond the reused
    `Bisim`/`IsBisimulation` machinery). -/
inductive BEx where
  | p | q1 | q2
deriving DecidableEq

/-- Concrete step relation: `p` self-loops; `q1 -> q2 -> q1` cycles. -/
abbrev bStep : BEx → HAct → BEx → Prop
  | .p, (), .p => True
  | .q1, (), .q2 => True
  | .q2, (), .q1 => True
  | _, _, _ => False

/-- The relation witnessing `p ~ q1`. -/
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

/-- `p` and `q1` are bisimilar. -/
theorem p_bisim_q1 : Bisim bStep BEx.p BEx.q1 :=
  ⟨bR, bR_isBisimulation, by decide⟩

/-- A formula that `p` satisfies: "some step leads to a state from which some step leads
    to a state satisfying `tt`" (`<()> <()> tt`, i.e. at least a 2-step run exists). Both
    `p` and `q1` satisfy it, per the theorem below — genuine non-vacuous content, not
    `tt` itself. -/
def twoStepFormula : HML HAct := HML.dia () (HML.dia () HML.tt)

example : Sat bStep BEx.p twoStepFormula := ⟨.p, by decide, .p, by decide, trivial⟩

/-- Applying `bisim_imp_hml_equiv` to `p ~ q1` and `twoStepFormula`: `p` satisfies it, hence
    (via the theorem, not by re-deriving it directly on `q1`) `q1` does too. -/
example : Sat bStep BEx.q1 twoStepFormula :=
  (bisim_imp_hml_equiv p_bisim_q1 twoStepFormula).mp ⟨.p, by decide, .p, by decide, trivial⟩

/-! #### A concrete separating formula for a NON-bisimilar pair -/

/-- States for the non-bisimilar example: `canDo` can perform the (only) action and
    self-loops; `cannotDo` is deadlocked and can perform no action at all. -/
inductive CEx where
  | canDo | cannotDo
deriving DecidableEq

/-- Concrete step relation: only `canDo` has any outgoing step. -/
abbrev cStep : CEx → HAct → CEx → Prop
  | .canDo, (), .canDo => True
  | _, _, _ => False

/-- The formula "some `()`-step is possible" (`<()> tt`). -/
def canStepFormula : HML HAct := HML.dia () HML.tt

/-- `canDo` satisfies `<()> tt`. -/
example : Sat cStep CEx.canDo canStepFormula := ⟨.canDo, by decide, trivial⟩

/-- `cannotDo` does NOT satisfy `<()> tt` — it has no outgoing step at all. This is a
    concrete HML formula separating a non-bisimilar pair, complementing (without proving the
    converse theorem) the invariance direction proved above: bisimilar states cannot be
    separated this way, and here two states that a formula DOES separate are indeed not
    bisimilar. -/
example : ¬ Sat cStep CEx.cannotDo canStepFormula := by
  rintro ⟨s', hs', _⟩
  cases s' <;> exact absurd hs' (by decide)

end Instances

end AutoproverCorpus.HennessyMilner
