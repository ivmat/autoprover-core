/-
  AutoproverCorpus.Concurrency.PetersonMutex

  Peterson's algorithm for two processes guarantees mutual exclusion: the two processes are
  never simultaneously in the critical section. Each process runs the six-location entry/exit
  protocol
    idle -> setFlag -> setTurn -> wait -> cs -> reset -> idle
  (own flag derived from location; `turn` shared; wait -> cs only fires once the other's flag
  is down or `turn` no longer favors the other). The joint state (both locations plus `turn`) is
  a finite type; mutual exclusion is proved by exhibiting an INDUCTIVE invariant — true at the
  initial state and preserved by every enabled transition, both checked by `decide` over the
  finite state/transition space — that on its own implies the two processes are never both at
  `cs`. This avoids enumerating reachable states: the invariant argument covers every reachable
  state in one finite, transition-local check.

  Attribution: G. L. Peterson, 1981.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.PetersonMutex

/-! ### The state space -/

/-- One process's program location. `flagOf` below derives that process's `flag` from its
    location, rather than tracking `flag` as separate mutable state: `flag` is true from the
    moment the `setFlag -> setTurn` step executes (i.e. once the location leaves `setFlag`)
    until the `reset -> idle` step executes. -/
inductive PC
  | idle | setFlag | setTurn | wait | cs | reset
  deriving DecidableEq, BEq, Repr

/-- The derived flag: `false` before the flag write (`idle`, `setFlag`), `true` from
    immediately after it (`setTurn`, `wait`, `cs`) through immediately before the reset write
    completes (`reset`). -/
def flagOf : PC → Bool
  | .idle => false
  | .setFlag => false
  | .setTurn => true
  | .wait => true
  | .cs => true
  | .reset => true

/-- The joint state: each process's location, plus the shared `turn` bit. `turn = true` means
    process 0 has (in its `setTurn` step) most recently yielded to process 1 — process 0 then
    waits while `flag 1 && turn`; `turn = false` is the symmetric marker written by process 1. -/
structure State where
  pc0 : PC
  pc1 : PC
  turn : Bool
  deriving DecidableEq, BEq, Repr

/-! ### The transition relation -/

/-- Process 0's own enabled moves, holding process 1's location fixed. The `wait -> cs` move is
    enabled exactly when process 0's spin condition (`flag 1 && turn`) currently fails. -/
def step0B (s s' : State) : Bool :=
  s.pc1 == s'.pc1 &&
  ((s.pc0 == PC.idle    && s'.pc0 == PC.setFlag && s'.turn == s.turn) ||
   (s.pc0 == PC.setFlag && s'.pc0 == PC.setTurn && s'.turn == s.turn) ||
   (s.pc0 == PC.setTurn && s'.pc0 == PC.wait    && s'.turn == true) ||
   (s.pc0 == PC.wait    && s'.pc0 == PC.cs      && s'.turn == s.turn &&
      !(flagOf s.pc1 && s.turn == true)) ||
   (s.pc0 == PC.cs      && s'.pc0 == PC.reset   && s'.turn == s.turn) ||
   (s.pc0 == PC.reset   && s'.pc0 == PC.idle    && s'.turn == s.turn))

/-- Process 1's own enabled moves — the mirror image of `step0B`, with `turn`'s polarity
    flipped (process 1 writes `turn := false` to yield, and spins while `flag 0 && !turn`). -/
def step1B (s s' : State) : Bool :=
  s.pc0 == s'.pc0 &&
  ((s.pc1 == PC.idle    && s'.pc1 == PC.setFlag && s'.turn == s.turn) ||
   (s.pc1 == PC.setFlag && s'.pc1 == PC.setTurn && s'.turn == s.turn) ||
   (s.pc1 == PC.setTurn && s'.pc1 == PC.wait    && s'.turn == false) ||
   (s.pc1 == PC.wait    && s'.pc1 == PC.cs      && s'.turn == s.turn &&
      !(flagOf s.pc0 && s.turn == false)) ||
   (s.pc1 == PC.cs      && s'.pc1 == PC.reset   && s'.turn == s.turn) ||
   (s.pc1 == PC.reset   && s'.pc1 == PC.idle    && s'.turn == s.turn))

/-- The joint step relation: either process moves, one at a time (standard interleaving
    semantics). `abbrev`, so `decide` can see through it. -/
abbrev stepB (s s' : State) : Bool := step0B s s' || step1B s s'

/-- `abbrev` (not `def`), so `decide` can see through it on concrete instances. -/
abbrev Step (s s' : State) : Prop := stepB s s' = true

def initState : State := { pc0 := .idle, pc1 := .idle, turn := false }

/-- Reachability: `initState`, closed under `Step`. -/
inductive Reachable : State → Prop
  | init : Reachable initState
  | step {s s' : State} (hr : Reachable s) (hst : Step s s') : Reachable s'

/-! ### The inductive invariant -/

/-- The invariant, as a decidable `Bool` test:
    (1) never both at `cs`;
    (2) if process 0 is at `cs` and process 1 is at `wait`, `turn` still blocks process 1
        (`turn = false`, matching process 1's own spin condition `flag 0 && !turn`);
    (3) the mirror condition protecting process 1's occupancy of `cs`.
    `abbrev`, so `decide` can see through it on concrete instances. -/
abbrev InvB (s : State) : Bool :=
  !(s.pc0 == PC.cs && s.pc1 == PC.cs) &&
  (!(s.pc0 == PC.cs) || !(s.pc1 == PC.wait) || s.turn == false) &&
  (!(s.pc1 == PC.cs) || !(s.pc0 == PC.wait) || s.turn == true)

abbrev Inv (s : State) : Prop := InvB s = true

/-- The invariant holds at the initial state (vacuously — neither process has even started
    trying to enter). -/
theorem inv_init : Inv initState := by decide

/-- **The inductive step.** Every enabled transition preserves the invariant. Checked by
    `decide` over the whole finite state/transition space (`72 × 72` pairs, reached by casing
    on every field of both states) — no reachability enumeration is needed: this one finite
    check, together with `inv_init`, covers every reachable state by the standard induction
    below. (`State` is not `Fin n`, so `decide` cannot see a blanket `∀ s s' : State, …` as
    decidable on its own; casing down to concrete constructors first gives `decide` a
    genuinely closed, decidable goal in each of the resulting branches.) -/
theorem inv_preserved : ∀ s s', Step s s' → Inv s → Inv s' := by
  intro s s'
  obtain ⟨pc0, pc1, turn⟩ := s
  obtain ⟨pc0', pc1', turn'⟩ := s'
  cases pc0 <;> cases pc1 <;> cases turn <;> cases pc0' <;> cases pc1' <;> cases turn' <;> decide

/-- **The invariant holds at every reachable state.** By induction on the `Reachable`
    derivation, using `inv_init` for the base case and `inv_preserved` for the step case. -/
theorem reachable_inv {s : State} (h : Reachable s) : Inv s := by
  induction h with
  | init => exact inv_init
  | step _ hst ih => exact inv_preserved _ _ hst ih

/-- The invariant's first conjunct is exactly mutual exclusion. -/
theorem mutual_exclusion_of_inv {s : State} (h : Inv s) :
    ¬ (s.pc0 = .cs ∧ s.pc1 = .cs) := by
  rintro ⟨h0, h1⟩
  unfold Inv InvB at h
  rw [h0, h1] at h
  cases hturn : s.turn <;> rw [hturn] at h <;> exact absurd h (by decide)

/-- **Peterson's mutual exclusion theorem.** The two processes are never simultaneously in the
    critical section, at any state reachable from the initial state. -/
theorem peterson_mutual_exclusion {s : State} (h : Reachable s) :
    ¬ (s.pc0 = .cs ∧ s.pc1 = .cs) :=
  mutual_exclusion_of_inv (reachable_inv h)

/-! ### Non-vacuity: the critical section is genuinely reachable (by either process alone) -/

/-- Process 0 running its entry protocol alone, from `initState`, through the three
    intermediate states, to a concrete state with `pc0 = cs`. -/
def p0Step1 : State := { pc0 := .setFlag, pc1 := .idle, turn := false }

def p0Step2 : State := { pc0 := .setTurn, pc1 := .idle, turn := false }

def p0Step3 : State := { pc0 := .wait, pc1 := .idle, turn := true }

def p0AtCS : State := { pc0 := .cs, pc1 := .idle, turn := true }

theorem step_init_p0Step1 : Step initState p0Step1 := by decide

theorem step_p0Step1_p0Step2 : Step p0Step1 p0Step2 := by decide

theorem step_p0Step2_p0Step3 : Step p0Step2 p0Step3 := by decide

theorem step_p0Step3_p0AtCS : Step p0Step3 p0AtCS := by decide

/-- **`p0AtCS` is genuinely REACHED**: a real four-step derivation from `initState`. -/
theorem p0AtCS_reachable : Reachable p0AtCS :=
  Reachable.step
    (Reachable.step
      (Reachable.step
        (Reachable.step Reachable.init step_init_p0Step1)
        step_p0Step1_p0Step2)
      step_p0Step2_p0Step3)
    step_p0Step3_p0AtCS

theorem p0AtCS_pc0 : p0AtCS.pc0 = .cs := by decide

/-- The reached state genuinely has process 1 idle (not "cs is unreachable because process 1
    always blocks it") — process 0 entering alone is a real, unobstructed run. -/
theorem p0AtCS_pc1 : p0AtCS.pc1 = .idle := by decide

end AutoproverCorpus.PetersonMutex
