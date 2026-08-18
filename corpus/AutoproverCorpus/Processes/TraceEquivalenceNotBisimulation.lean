/-
  AutoproverCorpus.Processes.TraceEquivalenceNotBisimulation

  Trace equivalence is strictly coarser than bisimilarity: Milner's standard counterexample,
  `a.(b + c)` versus `a.b + a.c`. The two processes have exactly the same finite traces —
  characterized here explicitly as `{[], [a], [a,b], [a,c]}` for BOTH, so the equality of the
  trace sets is proved rather than asserted — yet no bisimulation relates them, because the
  branching choice is made at a different moment: `a.b + a.c` commits to `b` or to `c` while
  performing `a`, whereas `a.(b + c)` keeps both options open afterwards.

  This is the converse of the implication proved in this corpus's `SimulationTraceInclusion`
  (a simulation forces trace inclusion, hence bisimilarity forces trace equivalence). The
  converse fails, and this module is the witness: trace equivalence does NOT imply bisimilarity.
  It is the reason `HennessyMilner` needs the modal logic to characterize bisimilarity — trace
  sets are too weak — and the reason refinement stated only over traces cannot express
  branching-time properties such as "the implementation never deadlocks a client that offers
  only `c`".

  The two processes live in ONE labelled transition system with a shared terminal state, so the
  comparison is between two states of the same LTS and needs no notion of process composition.

  Attribution: Classical (R. Milner; the standard example separating trace equivalence from
  bisimilarity — "A Calculus of Communicating Systems", 1980, and "Communication and
  Concurrency", 1989; the bisimulation notion itself is Park, 1981, and Hennessy and Milner,
  1980).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Processes.Bisimulation

namespace AutoproverCorpus.TraceEquivalenceNotBisimulation

open AutoproverCorpus.Bisimulation

/-! ### One LTS holding both processes -/

/-- Three visible actions. -/
inductive Act where
  | a | b | c
  deriving DecidableEq, Repr

/-- States: `p0 = a.(b + c)` with continuation `p1 = b + c`; `q0 = a.b + a.c` with
    continuations `qb = b` and `qc = c`; and one shared terminal state `stop`. -/
inductive St where
  | p0 | p1 | q0 | qb | qc | stop
  deriving DecidableEq, Repr

/-- The transition table. `abbrev` so `decide` unfolds it. -/
abbrev stepB : St → Act → St → Bool
  | .p0, .a, .p1 => true
  | .p1, .b, .stop => true
  | .p1, .c, .stop => true
  | .q0, .a, .qb => true
  | .q0, .a, .qc => true
  | .qb, .b, .stop => true
  | .qc, .c, .stop => true
  | _, _, _ => false

/-- The transition relation, as the `Prop`-valued step relation the `Bisimulation` module's
    definitions expect. -/
abbrev step (x : St) (α : Act) (y : St) : Prop := stepB x α y = true

/-! ### Finite traces -/

/-- `Tr x w`: the word `w` is a finite trace of state `x`. -/
inductive Tr : St → List Act → Prop where
  | nil {x : St} : Tr x []
  | cons {x : St} {α : Act} {y : St} {w : List Act} : step x α y → Tr y w → Tr x (α :: w)

/-! #### Successor tables, each a finite `decide`-checked fact -/

theorem stop_sink : ∀ α y, ¬ step St.stop α y := by
  intro α y; cases α <;> cases y <;> decide

theorem p0_dest : ∀ α y, step St.p0 α y → α = Act.a ∧ y = St.p1 := by
  intro α y h; cases α <;> cases y <;> revert h <;> decide

theorem p1_dest : ∀ α y, step St.p1 α y → (α = Act.b ∨ α = Act.c) ∧ y = St.stop := by
  intro α y h; cases α <;> cases y <;> revert h <;> decide

theorem q0_dest : ∀ α y, step St.q0 α y → α = Act.a ∧ (y = St.qb ∨ y = St.qc) := by
  intro α y h; cases α <;> cases y <;> revert h <;> decide

theorem qb_dest : ∀ α y, step St.qb α y → α = Act.b ∧ y = St.stop := by
  intro α y h; cases α <;> cases y <;> revert h <;> decide

theorem qc_dest : ∀ α y, step St.qc α y → α = Act.c ∧ y = St.stop := by
  intro α y h; cases α <;> cases y <;> revert h <;> decide

/-- The terminal state has only the empty trace. -/
theorem tr_stop : ∀ w, Tr St.stop w → w = [] := by
  intro w h
  cases h with
  | nil => rfl
  | cons hs _ => exact absurd hs (stop_sink _ _)

/-! ### The two trace sets, computed exactly -/

/-- **The traces of `a.(b + c)`** are exactly `[]`, `[a]`, `[a,b]`, `[a,c]`. Forward by
    inversion on the derivation (each state's successors are pinned down by the `decide`-checked
    tables above); backward by exhibiting the four derivations. -/
theorem tr_p0_iff (w : List Act) :
    Tr St.p0 w ↔ (w = [] ∨ w = [Act.a] ∨ w = [Act.a, Act.b] ∨ w = [Act.a, Act.c]) := by
  constructor
  · intro h
    cases h with
    | nil => exact Or.inl rfl
    | cons hs ht =>
      obtain ⟨hα, hy⟩ := p0_dest _ _ hs
      subst hα; subst hy
      cases ht with
      | nil => exact Or.inr (Or.inl rfl)
      | cons hs' ht' =>
        obtain ⟨hβ, hz⟩ := p1_dest _ _ hs'
        subst hz
        have hw : _ = [] := tr_stop _ ht'
        subst hw
        rcases hβ with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact Tr.nil
    · exact Tr.cons (show step St.p0 Act.a St.p1 by decide) Tr.nil
    · exact Tr.cons (show step St.p0 Act.a St.p1 by decide)
        (Tr.cons (show step St.p1 Act.b St.stop by decide) Tr.nil)
    · exact Tr.cons (show step St.p0 Act.a St.p1 by decide)
        (Tr.cons (show step St.p1 Act.c St.stop by decide) Tr.nil)

/-- **The traces of `a.b + a.c`** are the same four words. The difference between the two
    processes is invisible here: it lies in WHICH state the `a`-step lands in. -/
theorem tr_q0_iff (w : List Act) :
    Tr St.q0 w ↔ (w = [] ∨ w = [Act.a] ∨ w = [Act.a, Act.b] ∨ w = [Act.a, Act.c]) := by
  constructor
  · intro h
    cases h with
    | nil => exact Or.inl rfl
    | cons hs ht =>
      obtain ⟨hα, hy⟩ := q0_dest _ _ hs
      subst hα
      rcases hy with rfl | rfl
      · cases ht with
        | nil => exact Or.inr (Or.inl rfl)
        | cons hs' ht' =>
          obtain ⟨hβ, hz⟩ := qb_dest _ _ hs'
          subst hβ; subst hz
          have hw : _ = [] := tr_stop _ ht'
          subst hw
          exact Or.inr (Or.inr (Or.inl rfl))
      · cases ht with
        | nil => exact Or.inr (Or.inl rfl)
        | cons hs' ht' =>
          obtain ⟨hβ, hz⟩ := qc_dest _ _ hs'
          subst hβ; subst hz
          have hw : _ = [] := tr_stop _ ht'
          subst hw
          exact Or.inr (Or.inr (Or.inr rfl))
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact Tr.nil
    · exact Tr.cons (show step St.q0 Act.a St.qb by decide) Tr.nil
    · exact Tr.cons (show step St.q0 Act.a St.qb by decide)
        (Tr.cons (show step St.qb Act.b St.stop by decide) Tr.nil)
    · exact Tr.cons (show step St.q0 Act.a St.qc by decide)
        (Tr.cons (show step St.qc Act.c St.stop by decide) Tr.nil)

/-- **The two processes are trace equivalent**: word for word, they have the same traces. -/
theorem trace_equivalent (w : List Act) : Tr St.p0 w ↔ Tr St.q0 w := by
  rw [tr_p0_iff w, tr_q0_iff w]

/-! ### …but they are not bisimilar -/

/-- **No bisimulation relates them.** Any bisimulation must match `p0 -a-> p1` by an `a`-step
    from `q0`, landing in `qb` or in `qc`. In the first case `p1`'s `c`-step is unmatchable
    (`qb` offers only `b`); in the second, `p1`'s `b`-step is unmatchable. The choice `q0` makes
    while performing `a` is exactly what `p0` postpones — and what traces cannot see. -/
theorem p0_not_bisim_q0 : ¬ Bisim step St.p0 St.q0 := by
  rintro ⟨R, hR, hrel⟩
  obtain ⟨y, hy, hRy⟩ := (hR _ _ hrel).1 Act.a St.p1 (by decide)
  have hcase : y = St.qb ∨ y = St.qc := (q0_dest _ _ hy).2
  rcases hcase with rfl | rfl
  · obtain ⟨z, hz, _⟩ := (hR _ _ hRy).1 Act.c St.stop (by decide)
    exact absurd (qb_dest _ _ hz).1 (by decide)
  · obtain ⟨z, hz, _⟩ := (hR _ _ hRy).1 Act.b St.stop (by decide)
    exact absurd (qc_dest _ _ hz).1 (by decide)

/-- **The separation, packaged.** Two states of one LTS with identical trace sets that are not
    bisimilar: trace equivalence does not imply bisimilarity, so the implication proved in
    `SimulationTraceInclusion` (and its bisimulation corollary) is strictly one-directional. -/
theorem trace_equivalence_does_not_imply_bisimilarity :
    (∀ w, Tr St.p0 w ↔ Tr St.q0 w) ∧ ¬ Bisim step St.p0 St.q0 :=
  ⟨trace_equivalent, p0_not_bisim_q0⟩

/-! ### Non-vacuity: the trace sets are genuinely nonempty, and branching genuinely differs -/

/-- `[a, c]` really is a trace of both processes — the shared trace set is not empty, and the
    equivalence above is not the trivial one between two dead states. -/
example : Tr St.p0 [Act.a, Act.c] ∧ Tr St.q0 [Act.a, Act.c] :=
  ⟨(tr_p0_iff _).mpr (Or.inr (Or.inr (Or.inr rfl))),
   (tr_q0_iff _).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- The branching difference, concretely: after its `a`-step `p0` can still do either `b` or
    `c`, while each of `q0`'s two `a`-successors can do exactly one of them. -/
example :
    (step St.p1 Act.b St.stop ∧ step St.p1 Act.c St.stop) ∧
      (∀ y, ¬ step St.qb Act.c y) ∧ (∀ y, ¬ step St.qc Act.b y) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro y; cases y <;> decide
  · intro y; cases y <;> decide

end AutoproverCorpus.TraceEquivalenceNotBisimulation
