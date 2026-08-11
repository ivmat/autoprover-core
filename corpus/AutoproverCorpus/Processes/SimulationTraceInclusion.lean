/-
  AutoproverCorpus.Processes.SimulationTraceInclusion

  Simulation implies finite-trace inclusion: a simulating implementation exhibits no finite
  trace absent from its abstract model.

  Attribution: Classical (Milner).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.SimulationTraceInclusion

/-- `R` is a simulation from `stepA` to `stepB`: every related pair's `stepA`-step is
    matched by a `stepB`-step landing in related states. One-sided — no requirement in
    the other direction, unlike a bisimulation. -/
def IsSimulation {SA SB Act : Type} (stepA : SA → Act → SA → Prop)
    (stepB : SB → Act → SB → Prop) (R : SA → SB → Prop) : Prop :=
  ∀ s t, R s t → ∀ a s', stepA s a s' → ∃ t', stepB t a t' ∧ R s' t'

/-- `tr` is a finite action sequence executable from `s` under `step`. -/
inductive TraceOf {S Act : Type} (step : S → Act → S → Prop) : S → List Act → Prop where
  | nil (s : S) : TraceOf step s []
  | cons {s s' : S} {a : Act} {tr : List Act} (h1 : step s a s') (h2 : TraceOf step s' tr) :
      TraceOf step s (a :: tr)

/-! ### (a) The main theorem -/

/-- **Simulation implies finite-trace inclusion.** If `R` is a simulation from `stepA`
    to `stepB` and `R` relates `s` to `t`, every trace executable from `s` under
    `stepA` is also executable from `t` under `stepB` — a simulating implementation
    exhibits no behavior absent from its abstract model. Proved by induction on the
    `TraceOf` derivation. -/
theorem simulation_trace_inclusion {SA SB Act : Type} {stepA : SA → Act → SA → Prop}
    {stepB : SB → Act → SB → Prop} {R : SA → SB → Prop} (hsim : IsSimulation stepA stepB R)
    {s : SA} {tr : List Act} (htr : TraceOf stepA s tr) :
    ∀ {t : SB}, R s t → TraceOf stepB t tr := by
  induction htr with
  | nil =>
    intro t _hR
    exact TraceOf.nil t
  | cons h1 _h2 ih =>
    intro t hR
    obtain ⟨t', ht', hR'⟩ := hsim _ t hR _ _ h1
    exact TraceOf.cons ht' (ih hR')

/-! ### (b) The corollary in (self-contained) set language -/

/-- The trace set of `s` under `step`, as a bare predicate on `List Act` (core Lean has
    no `Set` type available here). -/
def TraceSet {S Act : Type} (step : S → Act → S → Prop) (s : S) : List Act → Prop :=
  fun tr => TraceOf step s tr

/-- Predicate-subset, standing in for `Set`'s `⊆`. -/
def SubsetPred {α : Type} (P Q : α → Prop) : Prop := ∀ x, P x → Q x

/-- **Trace-set inclusion.** The trace set of a simulating state `s` is included in the
    trace set of the state `t` it is related to. -/
theorem traceSet_subset {SA SB Act : Type} {stepA : SA → Act → SA → Prop}
    {stepB : SB → Act → SB → Prop} {R : SA → SB → Prop} (hsim : IsSimulation stepA stepB R)
    {s : SA} {t : SB} (hR : R s t) : SubsetPred (TraceSet stepA s) (TraceSet stepB t) :=
  fun _tr h => simulation_trace_inclusion hsim h hR

/-! ### (c) Simulation is a preorder (reflexive + transitive) -/

def Sim {S Act : Type} (step : S → Act → S → Prop) (s t : S) : Prop :=
  ∃ R, IsSimulation step step R ∧ R s t

theorem eq_isSimulation {S Act : Type} (step : S → Act → S → Prop) :
    IsSimulation step step (Eq (α := S)) := by
  intro s t hst a s' hstep
  subst hst
  exact ⟨s', hstep, rfl⟩

/-- **Reflexivity.** The identity relation is always a simulation of a system with
    itself. -/
theorem sim_refl {S Act : Type} (step : S → Act → S → Prop) (s : S) : Sim step s s :=
  ⟨Eq, eq_isSimulation step, rfl⟩

/-- Relational composition through an intermediate state. -/
def RelComp {SA SB SC : Type} (R1 : SA → SB → Prop) (R2 : SB → SC → Prop) (s : SA)
    (u : SC) : Prop := ∃ t, R1 s t ∧ R2 t u

/-- The composition of two simulations (over a shared action type, chained through a
    middle LTS type) is again a simulation. General 3-type form, specialized below to
    give transitivity of `Sim` on a single LTS type. -/
theorem isSimulation_comp {SA SB SC Act : Type} {stepA : SA → Act → SA → Prop}
    {stepB : SB → Act → SB → Prop} {stepC : SC → Act → SC → Prop} {R1 : SA → SB → Prop}
    {R2 : SB → SC → Prop} (h1 : IsSimulation stepA stepB R1) (h2 : IsSimulation stepB stepC R2) :
    IsSimulation stepA stepC (RelComp R1 R2) := by
  intro s u hsu a s' hstep
  obtain ⟨t, hst, htu⟩ := hsu
  obtain ⟨t', ht', hst'⟩ := h1 s t hst a s' hstep
  obtain ⟨u', hu', htu'⟩ := h2 t u htu a t' ht'
  exact ⟨u', hu', t', hst', htu'⟩

/-- **Transitivity.** `Sim` composes: if `s` simulates `t` and `t` simulates `u`, then
    `s` simulates `u`, via `RelComp` of the witnessing relations. Together with
    `sim_refl`, `Sim` is a preorder (not proved/claimed an equivalence — simulation is
    one-sided; see the negative instance below for the asymmetry). -/
theorem sim_trans {S Act : Type} {step : S → Act → S → Prop} {s t u : S}
    (hst : Sim step s t) (htu : Sim step t u) : Sim step s u := by
  obtain ⟨R1, h1, hR1⟩ := hst
  obtain ⟨R2, h2, hR2⟩ := htu
  exact ⟨RelComp R1 R2, isSimulation_comp h1 h2, t, hR1, hR2⟩

/-! ### (d) Instances (positive and negative) -/

section Instances

/-- Two actions, shared by every concrete system below. -/
inductive Act2 where
  | a | b
deriving DecidableEq

/-! #### Positive instance: an implementation simulated by a strictly richer spec -/

/-- The implementation: one action `a` from `i0` to `i1`, then deadlocked. -/
inductive Impl where
  | i0 | i1
deriving DecidableEq

/-- The abstract spec: from `s0`, either `a` (to `s1`) or `b` (to `s2`) — strictly more
    behavior than `Impl` exhibits. -/
inductive Spec where
  | s0 | s1 | s2
deriving DecidableEq

inductive implStep : Impl → Act2 → Impl → Prop where
  | step : implStep .i0 .a .i1

inductive specStep : Spec → Act2 → Spec → Prop where
  | toS1 : specStep .s0 .a .s1
  | toS2 : specStep .s0 .b .s2

/-- The relating relation: `i0 ~ s0`, `i1 ~ s1` (the spec's `b`-branch is simply never
    reached from `Impl`, which is fine — simulation does not require the abstract side
    to be matched, only the implementation side). -/
inductive implSpecR : Impl → Spec → Prop where
  | rel0 : implSpecR .i0 .s0
  | rel1 : implSpecR .i1 .s1

theorem implSpecR_isSimulation : IsSimulation implStep specStep implSpecR := by
  intro s t hst act s' hstep
  cases hst with
  | rel0 =>
    cases hstep with
    | step => exact ⟨.s1, specStep.toS1, implSpecR.rel1⟩
  | rel1 => cases hstep

/-- The spec can perform `b` — a trace absent from the implementation. -/
theorem spec_extra_trace : TraceOf specStep .s0 [Act2.b] :=
  TraceOf.cons specStep.toS2 (TraceOf.nil Spec.s2)

/-- The implementation cannot perform `b` at all: its only step is `a`. -/
theorem impl_lacks_extra_trace : ¬ TraceOf implStep .i0 [Act2.b] := by
  intro h
  cases h with
  | cons h1 _h2 => cases h1

/-- Everything `Impl` can do, `Spec` can also do (the main theorem, instantiated). -/
theorem impl_trace_subset_spec : SubsetPred (TraceSet implStep .i0) (TraceSet specStep .s0) :=
  traceSet_subset implSpecR_isSimulation implSpecR.rel0

/-! #### Negative instance: no simulation, and a trace mismatch to match -/

/-- The left system: a single self-looping state, able to perform `a` forever. -/
inductive Left where
  | l0
deriving DecidableEq

/-- The right system: a single, permanently deadlocked state — no outgoing steps at
    all. -/
inductive Right where
  | r0
deriving DecidableEq

inductive leftStep : Left → Act2 → Left → Prop where
  | loop : leftStep .l0 .a .l0

/-- No constructors: `rightStep` relates nothing — `r0` is deadlocked. -/
inductive rightStep : Right → Act2 → Right → Prop where

/-- The left system can perform `a`. -/
theorem left_has_trace : TraceOf leftStep .l0 [Act2.a] :=
  TraceOf.cons leftStep.loop (TraceOf.nil Left.l0)

/-- The right system cannot: it is deadlocked. -/
theorem right_lacks_trace : ¬ TraceOf rightStep .r0 [Act2.a] := by
  intro h
  cases h with
  | cons h1 _h2 => cases h1

/-- **No simulation relates `l0` to `r0`.** Any candidate relation would have to match
    `l0`'s `a`-step with some `rightStep`-step from `r0`, and there is none. This is
    exactly the situation the main theorem rules out for simulating pairs —
    here, correspondingly, `left_has_trace`/`right_lacks_trace` show the trace
    inclusion the theorem would have given does fail. -/
theorem no_simulation_left_right : ¬ ∃ R, IsSimulation leftStep rightStep R ∧ R .l0 .r0 := by
  rintro ⟨R, hsim, hR⟩
  obtain ⟨t', ht', _hR'⟩ := hsim .l0 .r0 hR .a .l0 leftStep.loop
  cases ht'

end Instances

end AutoproverCorpus.SimulationTraceInclusion
