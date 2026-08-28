/-
  AutoproverCorpus.Security.Noninterference

  Goguen-Meseguer noninterference for a deterministic machine: the purge lemma and the unwinding
  theorem, by list induction over command sequences.

  Attribution: Classical (Goguen and Meseguer, 1982).

  SCOPE NOTE. `Level` here is the two-domain core, `Low`/`High`: every statement below is about
  a single Low observer purging High inputs. The general multi-domain case — an arbitrary set of
  security domains with an interference relation between them — is the natural generalization,
  and it is out of scope in THIS module; it is proved separately in
  `AutoproverCorpus.Security.MultiDomainNoninterference`.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.Noninterference

/-- Security levels: the classical two-domain core (`Low`/`High`). The general
    multi-domain case (many domains + an interference relation) is the natural
    generalization and is out of scope here — see the header's SCOPE NOTE. -/
inductive Level
  | Low
  | High
  deriving DecidableEq, Repr

/-- The transition function `step : S → I → S` extended over a whole input trace, via
    left fold — the deterministic machine's run on a full input list. -/
def run {I S : Type u} (step : S → I → S) (s : S) (is : List I) : S :=
  is.foldl step s

@[simp] theorem run_nil {I S : Type u} (step : S → I → S) (s : S) :
    run step s ([] : List I) = s := rfl

@[simp] theorem run_cons {I S : Type u} (step : S → I → S) (s : S) (i : I) (is : List I) :
    run step s (i :: is) = run step (step s i) is := rfl

/-- Executable (`Bool`-valued) test for "input `i` is Low", used to drive `purge` via
    `List.filter`. -/
def isLow {I : Type u} (lvl : I → Level) (i : I) : Bool :=
  match lvl i with
  | Level.Low => true
  | Level.High => false

theorem isLow_eq_true_iff {I : Type u} (lvl : I → Level) (i : I) :
    isLow lvl i = true ↔ lvl i = Level.Low := by
  unfold isLow
  cases lvl i <;> simp

/-- `purge lvl is` — drop every High input from `is`, keeping the Low inputs in their
    original order. -/
def purge {I : Type u} (lvl : I → Level) (is : List I) : List I :=
  is.filter (isLow lvl)

/-- (2) `purge` is idempotent: filtering twice is the same as filtering once. -/
theorem purge_idempotent {I : Type u} (lvl : I → Level) (is : List I) :
    purge lvl (purge lvl is) = purge lvl is := by
  unfold purge
  rw [List.filter_filter]
  congr 1
  funext i
  cases isLow lvl i <;> rfl

/-- (3) Soundness of `purge`: every input it keeps is genuinely Low. -/
theorem purge_sound {I : Type u} (lvl : I → Level) (is : List I) :
    ∀ i ∈ purge lvl is, lvl i = Level.Low := by
  intro i hi
  unfold purge at hi
  rw [List.mem_filter] at hi
  exact (isLow_eq_true_iff lvl i).mp hi.2

def Noninterference {I S O : Type u} (step : S → I → S) (out : S → O) (lvl : I → Level) :
    Prop :=
  ∀ (s0 : S) (is : List I), out (run step s0 is) = out (run step s0 (purge lvl is))

/-- (OC) Output consistency: `eqv`-equivalent states are indistinguishable to Low. -/
def OutputConsistent {S O : Type u} (out : S → O) (eqv : S → S → Prop) : Prop :=
  ∀ s t, eqv s t → out s = out t

/-- (SC) Step consistency: a Low input preserves `eqv`-equivalence of two runs. -/
def StepConsistent {I S : Type u} (step : S → I → S) (lvl : I → Level) (eqv : S → S → Prop) :
    Prop :=
  ∀ (s t : S) (i : I), eqv s t → lvl i = Level.Low → eqv (step s i) (step t i)

/-- (LR) Locally respects: a High input does not move a state out of its own
    `eqv`-equivalence class. -/
def LocallyRespects {I S : Type u} (step : S → I → S) (lvl : I → Level) (eqv : S → S → Prop) :
    Prop :=
  ∀ (s : S) (i : I), lvl i = Level.High → eqv s (step s i)

/-- Core route for (1): the stronger, list-length-induction-friendly invariant —
    `eqv`-related starting states stay `eqv`-related after running one trace against the
    other's purge. Low-input step (`SC` case): both sides take the same (unpurged) step,
    `SC` carries the relation forward, `ih` finishes. High-input step (`LR` case): the
    unpurged side takes an extra step that `LR` shows stays in-class (`eqv s (step s
    i)`), so `eqv.symm` + `eqv.trans` against the incoming `eqv s t` lets `ih` finish
    against the OTHER side's un-stepped, purge-dropped state. -/
theorem unwinding_step {I S : Type u} (step : S → I → S) (lvl : I → Level)
    (eqv : S → S → Prop) (heqv : Equivalence eqv) (hSC : StepConsistent step lvl eqv)
    (hLR : LocallyRespects step lvl eqv) :
    ∀ (is : List I) (s t : S), eqv s t → eqv (run step s is) (run step t (purge lvl is)) := by
  intro is
  induction is with
  | nil => intro s t h; simpa [purge] using h
  | cons i is' ih =>
    intro s t h
    cases hl : lvl i with
    | Low =>
      have hpurge : purge lvl (i :: is') = i :: purge lvl is' := by
        unfold purge; simp [isLow, hl]
      rw [run_cons, hpurge, run_cons]
      exact ih (step s i) (step t i) (hSC s t i h hl)
    | High =>
      have hpurge : purge lvl (i :: is') = purge lvl is' := by
        unfold purge; simp [isLow, hl]
      rw [run_cons, hpurge]
      have h1 : eqv (step s i) s := heqv.symm (hLR s i hl)
      have h2 : eqv (step s i) t := heqv.trans h1 h
      exact ih (step s i) t h2

/-- (1) **Unwinding theorem.** OC + SC + LR for an equivalence relation `eqv` on states
    implies noninterference: Low's observation is invariant to purging the High inputs. -/
theorem unwinding_theorem {I S O : Type u} (step : S → I → S) (out : S → O) (lvl : I → Level)
    (eqv : S → S → Prop) (heqv : Equivalence eqv) (hOC : OutputConsistent out eqv)
    (hSC : StepConsistent step lvl eqv) (hLR : LocallyRespects step lvl eqv) :
    Noninterference step out lvl := by
  intro s0 is
  exact hOC _ _ (unwinding_step step lvl eqv heqv hSC hLR is s0 s0 (heqv.refl s0))

/-! ### (4) Instances: a shared tiny machine, positive and negative instances -/

/-- The tiny machine's input type: a Low increment and a High increment. -/
inductive Cmd
  | lowInc
  | highInc
  deriving DecidableEq, Repr

/-- The level partition matching each command's name. -/
def cmdLvl : Cmd → Level
  | Cmd.lowInc => Level.Low
  | Cmd.highInc => Level.High

/-- The shared state: `(low counter, high counter)`. Low only ever observes the first
    component. -/
abbrev St : Type := Nat × Nat

/-- What Low sees of the state: the low counter. -/
def obs (s : St) : Nat := s.1

/-- Low-equivalence on states: agreement on the low-visible counter. -/
def lowEq (s t : St) : Prop := s.1 = t.1

theorem lowEq_equivalence : Equivalence lowEq :=
  { refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2 }

/-- Honest machine: each command bumps only the counter matching its own level. -/
def honestStep (s : St) (i : Cmd) : St :=
  match i with
  | Cmd.lowInc => (s.1 + 1, s.2)
  | Cmd.highInc => (s.1, s.2 + 1)

theorem honest_OC : OutputConsistent obs lowEq := fun _ _ h => h

theorem honest_SC : StepConsistent honestStep cmdLvl lowEq := by
  intro s t i h hl
  cases i with
  | lowInc => simp [honestStep, lowEq] at h ⊢; omega
  | highInc => simp [cmdLvl] at hl

theorem honest_LR : LocallyRespects honestStep cmdLvl lowEq := by
  intro s i hl
  cases i with
  | lowInc => simp [cmdLvl] at hl
  | highInc => simp [honestStep, lowEq]

/-- The honest machine satisfies noninterference, DIRECTLY via the unwinding theorem
    (no bespoke induction needed — OC/SC/LR above suffice). -/
theorem honest_noninterference : Noninterference honestStep obs cmdLvl :=
  unwinding_theorem honestStep obs cmdLvl lowEq lowEq_equivalence honest_OC honest_SC honest_LR

/-- Leaky machine: a High input ALSO bumps the low counter — a genuine information
    leak from High to Low. -/
def leakyStep (s : St) (i : Cmd) : St :=
  match i with
  | Cmd.lowInc => (s.1 + 1, s.2)
  | Cmd.highInc => (s.1 + 1, s.2 + 1)

/-- Concrete counterexample trace: a single High input from `(0, 0)`. Running it moves
    Low's observation from `0` to `1`; purging it (dropping the High input) leaves Low's
    observation at `0`. -/
theorem leaky_witness_diverges :
    obs (run leakyStep (0, 0) [Cmd.highInc]) ≠
      obs (run leakyStep (0, 0) (purge cmdLvl [Cmd.highInc])) := by decide

/-- Negative witness: the leaky machine genuinely VIOLATES noninterference — witnessing
    that the unwinding theorem's OC/SC/LR hypotheses are not vacuous (a machine that
    fails them can, and here does, fail the conclusion too). -/
theorem leaky_not_noninterferent : ¬ Noninterference leakyStep obs cmdLvl := by
  intro h
  exact leaky_witness_diverges (h (0, 0) [Cmd.highInc])

end AutoproverCorpus.Noninterference
