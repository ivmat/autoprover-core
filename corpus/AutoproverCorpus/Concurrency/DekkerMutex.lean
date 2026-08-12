/-
  AutoproverCorpus.Concurrency.DekkerMutex

  Dekker's algorithm — the first published correct software solution to two-process mutual
  exclusion — guarantees mutual exclusion: the two processes are never simultaneously in the
  critical section. Each process runs the entry/exit protocol
    idle -> setFlag -> {cs, yield} -> ... -> cs -> setTurnExit -> resetFlag -> idle
  using its own flag plus the shared `turn` variable: after raising its own flag, a process
  busy-waits on the OTHER's flag (`setFlag -> cs` fires only once the other's flag is
  observed down); if the other's flag is up AND `turn` currently favors the other, the
  process temporarily LOWERS its own flag and waits for `turn` to favor it again (`yield`)
  before raising the flag and retesting — this is the tie-breaking mechanism `turn` exists
  for, and (unlike Peterson's algorithm) it only affects which process makes progress, not
  whether entry to the critical section is safe: `setFlag -> cs` here always re-checks the
  other's flag literally, so `turn` never appears in the safety argument below (it would
  appear in a liveness/no-deadlock proof, which this module does not undertake — see the
  scope note on the invariant).

  The joint state (both locations plus `turn`) is a finite type; mutual exclusion is proved by
  exhibiting an INDUCTIVE invariant — true at the initial state and preserved by every enabled
  transition, both checked by `decide` over the finite state/transition space — that on its own
  implies the two processes are never both at `cs`. This avoids enumerating reachable states:
  the invariant argument covers every reachable state in one finite, transition-local check.

  Attribution: Dekker's algorithm, as published in E. W. Dijkstra, "Cooperating Sequential
  Processes" (1968), §2.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.DekkerMutex

/-! ### The state space -/

/-- One process's program location. `flagOf` below derives that process's `flag` from its
    location, rather than tracking `flag` as separate mutable state — this is faithful to
    Dekker's algorithm because the flag's value at every point of the protocol is a fixed
    function of control location alone (including the temporary lowering while `yield`ing):
    up throughout `setFlag`/`cs`/`setTurnExit`/`resetFlag` (the process is "in the danger
    zone", trying to enter or occupying the critical section), down at `idle` and at `yield`
    (the process has backed off to let the other through). -/
inductive PC
  | idle | setFlag | yield | cs | setTurnExit | resetFlag
  deriving DecidableEq, BEq, Repr

/-- The derived flag, as described above. -/
def flagOf : PC → Bool
  | .idle => false
  | .setFlag => true
  | .yield => false
  | .cs => true
  | .setTurnExit => true
  | .resetFlag => true

/-- The joint state: each process's location, plus the shared `turn` bit. `turn = true`
    favors process 1 (process 0 must temporarily back off, at `setFlag -> yield`, if it sees
    the other's flag up while `turn` favors process 1); `turn = false` is the symmetric
    marker favoring process 0. `turn` changes only when a process LEAVES the critical
    section (`setTurnExit -> resetFlag`), granting priority to the other. -/
structure State where
  pc0 : PC
  pc1 : PC
  turn : Bool
  deriving DecidableEq, BEq, Repr

/-! ### The transition relation -/

/-- Process 0's own enabled moves, holding process 1's location fixed.
    - `idle -> setFlag`: raise flag 0 (unconditional entry attempt).
    - `setFlag -> cs`: enter, once the other's flag is observed DOWN — the literal re-test
      that makes the safety argument independent of `turn` (see the module header).
    - `setFlag -> yield`: the other's flag is up AND `turn` favors process 1 (`s.turn =
      true`) — back off, lowering flag 0.
    - `yield -> setFlag`: `turn` now favors process 0 (`s.turn = false`) — raise flag 0
      again and go back to re-testing.
    - `cs -> setTurnExit -> resetFlag -> idle`: leave the critical section, granting `turn`
      to process 1 (`setTurnExit -> resetFlag` writes `turn := true`), then lower flag 0. -/
def step0B (s s' : State) : Bool :=
  s.pc1 == s'.pc1 &&
  ((s.pc0 == PC.idle        && s'.pc0 == PC.setFlag     && s'.turn == s.turn) ||
   (s.pc0 == PC.setFlag     && s'.pc0 == PC.cs           && s'.turn == s.turn &&
      !(flagOf s.pc1)) ||
   (s.pc0 == PC.setFlag     && s'.pc0 == PC.yield        && s'.turn == s.turn &&
      flagOf s.pc1 && s.turn == true) ||
   (s.pc0 == PC.yield       && s'.pc0 == PC.setFlag      && s'.turn == s.turn &&
      s.turn == false) ||
   (s.pc0 == PC.cs          && s'.pc0 == PC.setTurnExit  && s'.turn == s.turn) ||
   (s.pc0 == PC.setTurnExit && s'.pc0 == PC.resetFlag    && s'.turn == true) ||
   (s.pc0 == PC.resetFlag   && s'.pc0 == PC.idle         && s'.turn == s.turn))

/-- Process 1's own enabled moves — the mirror image of `step0B`, with `turn`'s polarity
    flipped (process 1 favors itself at `turn = true`, waits while `turn = false`, and
    writes `turn := false` on exit to grant priority to process 0). -/
def step1B (s s' : State) : Bool :=
  s.pc0 == s'.pc0 &&
  ((s.pc1 == PC.idle        && s'.pc1 == PC.setFlag     && s'.turn == s.turn) ||
   (s.pc1 == PC.setFlag     && s'.pc1 == PC.cs           && s'.turn == s.turn &&
      !(flagOf s.pc0)) ||
   (s.pc1 == PC.setFlag     && s'.pc1 == PC.yield        && s'.turn == s.turn &&
      flagOf s.pc0 && s.turn == false) ||
   (s.pc1 == PC.yield       && s'.pc1 == PC.setFlag      && s'.turn == s.turn &&
      s.turn == true) ||
   (s.pc1 == PC.cs          && s'.pc1 == PC.setTurnExit  && s'.turn == s.turn) ||
   (s.pc1 == PC.setTurnExit && s'.pc1 == PC.resetFlag    && s'.turn == false) ||
   (s.pc1 == PC.resetFlag   && s'.pc1 == PC.idle         && s'.turn == s.turn))

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

/-- The invariant, as a decidable `Bool` test: never both at `cs`. Unlike
    `Concurrency.PetersonMutex`'s invariant, no auxiliary `turn`-tracking clause is needed
    here — see the module header for why: `setFlag -> cs` is guarded by the OTHER's derived
    flag being literally down, and `flagOf .cs = true`, so whichever process is at `cs`
    already blocks the other's entry transition by itself, with no help from `turn`.
    `abbrev`, so `decide` can see through it on concrete instances. -/
abbrev InvB (s : State) : Bool := !(s.pc0 == PC.cs && s.pc1 == PC.cs)

abbrev Inv (s : State) : Prop := InvB s = true

/-- The invariant holds at the initial state (vacuously — neither process has even started
    trying to enter). -/
theorem inv_init : Inv initState := by decide

/-- **The inductive step.** Every enabled transition preserves the invariant. Checked by
    `decide` over the whole finite state/transition space (`72 × 72` pairs, reached by casing
    on every field of both states) — no reachability enumeration is needed: this one finite
    check, together with `inv_init`, covers every reachable state by the standard induction
    below. -/
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

/-- The invariant is exactly mutual exclusion. -/
theorem mutual_exclusion_of_inv {s : State} (h : Inv s) :
    ¬ (s.pc0 = .cs ∧ s.pc1 = .cs) := by
  rintro ⟨h0, h1⟩
  unfold Inv InvB at h
  rw [h0, h1] at h
  exact absurd h (by decide)

/-- **Dekker's mutual exclusion theorem.** The two processes are never simultaneously in the
    critical section, at any state reachable from the initial state. -/
theorem dekker_mutual_exclusion {s : State} (h : Reachable s) :
    ¬ (s.pc0 = .cs ∧ s.pc1 = .cs) :=
  mutual_exclusion_of_inv (reachable_inv h)

/-! ### Non-vacuity: the critical section is genuinely reachable

    Two witnesses: (1) process 0 entering alone, uncontested; (2) a genuinely CONTESTED run
    where process 1 gets there first, process 0 then collides with it, and the `turn`-favored
    process 0 forces process 1 to `yield` (exercising the tie-breaking transitions, not just
    the straight-line path) before process 0 proceeds into `cs`. -/

/-- Process 0 running its entry protocol alone, from `initState`, to a concrete state with
    `pc0 = cs`. -/
def p0Step1 : State := { pc0 := .setFlag, pc1 := .idle, turn := false }

def p0AtCS : State := { pc0 := .cs, pc1 := .idle, turn := false }

theorem step_init_p0Step1 : Step initState p0Step1 := by decide

theorem step_p0Step1_p0AtCS : Step p0Step1 p0AtCS := by decide

/-- **`p0AtCS` is genuinely REACHED**: a real two-step derivation from `initState`, with
    process 1 idle throughout (an unobstructed run). -/
theorem p0AtCS_reachable : Reachable p0AtCS :=
  Reachable.step (Reachable.step Reachable.init step_init_p0Step1) step_p0Step1_p0AtCS

theorem p0AtCS_pc0 : p0AtCS.pc0 = .cs := by decide

/-- Contested run, state 1: process 1 raises its flag first. -/
def cState1 : State := { pc0 := .idle, pc1 := .setFlag, turn := false }

/-- Contested run, state 2: process 0 also raises its flag — both flags now up, `turn`
    favoring process 0. -/
def cState2 : State := { pc0 := .setFlag, pc1 := .setFlag, turn := false }

/-- Contested run, state 3: process 1, seeing process 0's flag up while `turn` does NOT
    favor it (`turn = false`), backs off (`setFlag -> yield`), lowering its own flag. -/
def cState3 : State := { pc0 := .setFlag, pc1 := .yield, turn := false }

/-- Contested run, state 4: with process 1's flag now down, process 0 proceeds into `cs` —
    the tie was genuinely broken by `turn`, not by process 1 simply never having tried. -/
def cState4 : State := { pc0 := .cs, pc1 := .yield, turn := false }

theorem step_init_cState1 : Step initState cState1 := by decide
theorem step_cState1_cState2 : Step cState1 cState2 := by decide
theorem step_cState2_cState3 : Step cState2 cState3 := by decide
theorem step_cState3_cState4 : Step cState3 cState4 := by decide

/-- **`cState4` is genuinely REACHED** via a real four-step CONTESTED derivation, exercising
    the `setFlag -> yield` and `yield -> setFlag`-style tie-break machinery (here, process 1's
    `setFlag -> yield` step) on the way to process 0 entering `cs`. -/
theorem cState4_reachable : Reachable cState4 :=
  Reachable.step
    (Reachable.step
      (Reachable.step
        (Reachable.step Reachable.init step_init_cState1)
        step_cState1_cState2)
      step_cState2_cState3)
    step_cState3_cState4

theorem cState4_pc0 : cState4.pc0 = .cs := by decide

/-- The reached state genuinely has process 1 backed off at `yield`, not idle — this is a
    REAL contested resolution, not one process failing to try. -/
theorem cState4_pc1 : cState4.pc1 = .yield := by decide

end AutoproverCorpus.DekkerMutex
