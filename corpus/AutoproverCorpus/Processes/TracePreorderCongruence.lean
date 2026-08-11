/-
  AutoproverCorpus.Processes.TracePreorderCongruence

  Congruence of the trace-inclusion preorder for a finite non-recursive process calculus: the
  preorder is preserved by prefix, choice and parallel contexts. `par` here is pure
  interleaving (no synchronisation), and inclusion is over finite performable traces; this is
  a trace-inclusion preorder, weaker than standard may-testing equivalence (which quantifies
  over all observer/test processes, not just trace containment).

  Attribution: Trace-inclusion congruence for a De Nicola-Hennessy-style process calculus
  (De Nicola and Hennessy, 1984); scoped here to pure-interleaving trace inclusion.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Processes.TestingPreorder

namespace AutoproverCorpus.TracePreorderCongruence

/-! ### The process calculus -/

/-- A finite, non-recursive process calculus: no fixpoint/recursion operator, so every
    `Proc` term is a finite tree and every derivation below is structural. -/
inductive Proc (Act : Type) where
  | nil : Proc Act
  | pre (a : Act) (p : Proc Act) : Proc Act
  | choice (p q : Proc Act) : Proc Act
  | par (p q : Proc Act) : Proc Act
deriving DecidableEq

/-- The LTS. `par` is pure interleaving — `parL`/`parR` only, no synchronisation
    constructor (see header). -/
inductive Step {Act : Type} : Proc Act → Act → Proc Act → Prop where
  | pre (a : Act) (p : Proc Act) : Step (Proc.pre a p) a p
  | choiceL {p q p' : Proc Act} {a : Act} (h : Step p a p') : Step (Proc.choice p q) a p'
  | choiceR {p q q' : Proc Act} {a : Act} (h : Step q a q') : Step (Proc.choice p q) a q'
  | parL {p q p' : Proc Act} {a : Act} (h : Step p a p') :
      Step (Proc.par p q) a (Proc.par p' q)
  | parR {p q q' : Proc Act} {a : Act} (h : Step q a q') :
      Step (Proc.par p q) a (Proc.par p q')

/-- `t` is a finite trace performable from `p`: a prefix of some run, not necessarily
    maximal. -/
inductive Performs {Act : Type} : Proc Act → List Act → Prop where
  | nil (p : Proc Act) : Performs p []
  | cons {p p' : Proc Act} {a : Act} {t : List Act} (h1 : Step p a p') (h2 : Performs p' t) :
      Performs p (a :: t)

def TraceLe {Act : Type} (P Q : Proc Act) : Prop :=
  AutoproverCorpus.TestingPreorder.MayLe (passes := fun (P : Proc Act) (t : List Act) => Performs P t) P Q

theorem traceInclusion_refl {Act : Type} (P : Proc Act) : TraceLe P P :=
  AutoproverCorpus.TestingPreorder.mayLe_refl P

theorem traceInclusion_trans {Act : Type} {P Q R : Proc Act} (hPQ : TraceLe P Q) (hQR : TraceLe Q R) :
    TraceLe P R :=
  AutoproverCorpus.TestingPreorder.mayLe_trans hPQ hQR

/-- Unfolding lemma: `TraceLe` is exactly "every trace `P` performs, `Q` also performs". -/
theorem traceInclusion_iff {Act : Type} {P Q : Proc Act} :
    TraceLe P Q ↔ ∀ t, Performs P t → Performs Q t :=
  Iff.rfl

/-! ### (b) Congruence -/

/-! #### Prefix -/

theorem traceInclusion_pre {Act : Type} (a : Act) {P Q : Proc Act} (h : TraceLe P Q) :
    TraceLe (Proc.pre a P) (Proc.pre a Q) := by
  intro t ht
  cases ht with
  | nil => exact Performs.nil _
  | cons h1 h2 =>
    cases h1
    exact Performs.cons (Step.pre a Q) (h _ h2)

/-! #### Choice -/

/-- `choice P R` performs exactly the union of what `P` and `R` perform. -/
theorem performs_choice_iff {Act : Type} (P R : Proc Act) (t : List Act) :
    Performs (Proc.choice P R) t ↔ Performs P t ∨ Performs R t := by
  constructor
  · intro h
    cases h with
    | nil => exact Or.inl (Performs.nil _)
    | cons h1 h2 =>
      cases h1 with
      | choiceL hP => exact Or.inl (Performs.cons hP h2)
      | choiceR hR => exact Or.inr (Performs.cons hR h2)
  · rintro (h | h)
    · cases h with
      | nil => exact Performs.nil _
      | cons h1 h2 => exact Performs.cons (Step.choiceL h1) h2
    · cases h with
      | nil => exact Performs.nil _
      | cons h1 h2 => exact Performs.cons (Step.choiceR h1) h2

theorem traceInclusion_choice_congr_left {Act : Type} {P Q R : Proc Act} (h : TraceLe P Q) :
    TraceLe (Proc.choice P R) (Proc.choice Q R) := by
  intro t ht
  rcases (performs_choice_iff P R t).mp ht with hP | hR
  · exact (performs_choice_iff Q R t).mpr (Or.inl (h t hP))
  · exact (performs_choice_iff Q R t).mpr (Or.inr hR)

theorem traceInclusion_choice_congr_right {Act : Type} {P Q R : Proc Act} (h : TraceLe P Q) :
    TraceLe (Proc.choice R P) (Proc.choice R Q) := by
  intro t ht
  rcases (performs_choice_iff R P t).mp ht with hR | hP
  · exact (performs_choice_iff R Q t).mpr (Or.inl hR)
  · exact (performs_choice_iff R Q t).mpr (Or.inr (h t hP))

/-! #### Parallel — the substantive case: interleaving decomposition -/

/-- `Interleave x y z` — `z` is a shuffle (interleaving) of `x` and `y`: at every point,
    the next element of `z` is taken either from the front of `x` or the front of `y`. -/
inductive Interleave {Act : Type} : List Act → List Act → List Act → Prop where
  | nilL (l : List Act) : Interleave [] l l
  | nilR (l : List Act) : Interleave l [] l
  | consL {a : Act} {x y z : List Act} (h : Interleave x y z) : Interleave (a :: x) y (a :: z)
  | consR {a : Act} {x y z : List Act} (h : Interleave x y z) : Interleave x (a :: y) (a :: z)

/-- **The interleaving decomposition lemma.** A trace of `par P R` is performable iff it
    is an interleaving of some trace `P` performs and some trace `R` performs. Proved by
    induction on the trace (quantified over all `P R` at each step, since an interleaving
    step changes which sub-process is "active"). -/
theorem performs_par_iff {Act : Type} :
    ∀ (t : List Act) (P R : Proc Act),
      Performs (Proc.par P R) t ↔ ∃ t1 t2, Interleave t1 t2 t ∧ Performs P t1 ∧ Performs R t2 := by
  intro t
  induction t with
  | nil =>
    intro P R
    constructor
    · intro _
      exact ⟨[], [], Interleave.nilL [], Performs.nil P, Performs.nil R⟩
    · intro _
      exact Performs.nil _
  | cons a rest ih =>
    intro P R
    constructor
    · intro h
      cases h with
      | cons h1 h2 =>
        cases h1 with
        | parL hP =>
          obtain ⟨t1, t2, hint, hPt1, hRt2⟩ := (ih _ R).mp h2
          exact ⟨a :: t1, t2, Interleave.consL hint, Performs.cons hP hPt1, hRt2⟩
        | parR hR =>
          obtain ⟨t1, t2, hint, hPt1, hRt2⟩ := (ih P _).mp h2
          exact ⟨t1, a :: t2, Interleave.consR hint, hPt1, Performs.cons hR hRt2⟩
    · rintro ⟨t1, t2, hint, hPt1, hRt2⟩
      cases hint with
      | nilL =>
        cases hRt2 with
        | cons hR1 hR2 =>
          exact Performs.cons (Step.parR hR1)
            ((ih P _).mpr ⟨[], rest, Interleave.nilL rest, Performs.nil P, hR2⟩)
      | nilR =>
        cases hPt1 with
        | cons hP1 hP2 =>
          exact Performs.cons (Step.parL hP1)
            ((ih _ R).mpr ⟨rest, [], Interleave.nilR rest, hP2, Performs.nil R⟩)
      | consL hxy =>
        cases hPt1 with
        | cons hP1 hP2 =>
          exact Performs.cons (Step.parL hP1) ((ih _ R).mpr ⟨_, _, hxy, hP2, hRt2⟩)
      | consR hxy =>
        cases hRt2 with
        | cons hR1 hR2 =>
          exact Performs.cons (Step.parR hR1) ((ih P _).mpr ⟨_, _, hxy, hPt1, hR2⟩)

theorem traceInclusion_par_congr_left {Act : Type} {P Q R : Proc Act} (h : TraceLe P Q) :
    TraceLe (Proc.par P R) (Proc.par Q R) := by
  intro t ht
  obtain ⟨t1, t2, hint, hPt1, hRt2⟩ := (performs_par_iff t P R).mp ht
  exact (performs_par_iff t Q R).mpr ⟨t1, t2, hint, h t1 hPt1, hRt2⟩

theorem traceInclusion_par_congr_right {Act : Type} {P Q R : Proc Act} (h : TraceLe P Q) :
    TraceLe (Proc.par R P) (Proc.par R Q) := by
  intro t ht
  obtain ⟨t1, t2, hint, hRt1, hPt2⟩ := (performs_par_iff t R P).mp ht
  exact (performs_par_iff t R Q).mpr ⟨t1, t2, hint, hRt1, h t2 hPt2⟩

/-! ### (c) Instances -/

section Instances

/-- Two concrete actions. -/
inductive Act2 where
  | a | b
deriving DecidableEq

/-- The "does nothing" process. -/
def P0 : Proc Act2 := Proc.nil

/-- Strictly richer: can perform `a` (and, trivially, the empty trace). -/
def Q0 : Proc Act2 := Proc.pre Act2.a Proc.nil

/-- `P0` and `Q0` are distinct processes. -/
example : P0 ≠ Q0 := by decide

/-- **The strict pair.** `Q0` performs every trace `P0` performs (only the empty one). -/
theorem traceInclusion_P0_Q0 : TraceLe P0 Q0 := by
  intro t ht
  cases ht with
  | nil => exact Performs.nil _
  | cons h1 _h2 => cases h1

/-- The pair is strict / the preorder is not trivial: `P0` does not trace-include
    `Q0` — `Q0` performs `[a]`, which `P0` (deadlocked) cannot. -/
theorem not_traceInclusion_Q0_P0 : ¬ TraceLe Q0 P0 := by
  intro h
  have ht : Performs Q0 [Act2.a] := Performs.cons (Step.pre Act2.a Proc.nil) (Performs.nil Proc.nil)
  have hcontra := h [Act2.a] ht
  cases hcontra with
  | cons h1 _h2 => cases h1

/-! #### The congruence conclusion, exhibited concretely at `P0 ≤ Q0` -/

/-- `pre` congruence, concretely. -/
example : TraceLe (Proc.pre Act2.b P0) (Proc.pre Act2.b Q0) :=
  traceInclusion_pre Act2.b traceInclusion_P0_Q0

/-- `choice` congruence, concretely, both argument positions. -/
example : TraceLe (Proc.choice P0 Proc.nil) (Proc.choice Q0 Proc.nil) :=
  traceInclusion_choice_congr_left traceInclusion_P0_Q0

example : TraceLe (Proc.choice Proc.nil P0) (Proc.choice Proc.nil Q0) :=
  traceInclusion_choice_congr_right traceInclusion_P0_Q0

/-- `par` congruence, concretely, both argument positions — the substantive operator,
    riding on the interleaving decomposition lemma. -/
example : TraceLe (Proc.par P0 (Proc.pre Act2.b Proc.nil)) (Proc.par Q0 (Proc.pre Act2.b Proc.nil)) :=
  traceInclusion_par_congr_left traceInclusion_P0_Q0

example : TraceLe (Proc.par (Proc.pre Act2.b Proc.nil) P0) (Proc.par (Proc.pre Act2.b Proc.nil) Q0) :=
  traceInclusion_par_congr_right traceInclusion_P0_Q0

end Instances

end AutoproverCorpus.TracePreorderCongruence
