# Corpus Catalog

This is the navigational index for the AutoproverCorpus: 65 Lean 4 modules of
machine-checked classical results, organized into 7 subject areas. Every module is
kernel-checked core Lean with **no mathlib and no external libraries** — each proof
stands on its own. The corpus claims **no novelty**: every result is a formalization of
a known, classical theorem, algorithm property, or textbook counterexample, credited in
its `Attribution:` line. Hypotheses named in a theorem statement are assumed, not
proved, and the claim made by each module is exactly its theorem statements, as accepted
by the Lean kernel — nothing more.

The **Scope** column is the honesty column. Most modules prove the general result their
name suggests (`full`). Some modules are deliberately restricted — a fixed finite
instance, one direction of a biconditional with the converse noted false or unproved, a
safety-only property with no liveness claim, an access-rule fragment of a larger policy,
or a hypothesis (e.g. hash injectivity) that is assumed rather than proved. Those are
flagged `scoped`, with a few words on what is restricted, taken from the module's own
header. Read the Scope column before citing any module as proof of the general theorem
implied by its name.

## Concurrency

| Module | Proves | Attribution | Scope |
|---|---|---|---|
| ConflictSerializability | A schedule is conflict-serializable iff its precedence (conflict) graph is acyclic, with a cyclic non-serializable witness schedule. | Classical (Eswaran, Gray, Lorie and Traiger, 1976; Bernstein et al.). | full |
| DekkerMutex | Dekker's algorithm guarantees mutual exclusion, via a finite inductive invariant checked by `decide`. | Dekker's algorithm, as published in E. W. Dijkstra, "Cooperating Sequential Processes" (1968), §2. | scoped — safety (mutual exclusion) only; liveness/no-deadlock not proved |
| PetersonMutex | Peterson's algorithm guarantees mutual exclusion, via a finite inductive invariant checked by `decide`. | G. L. Peterson, 1981. | full |
| ResourceOrderingAcyclic | Ordered resource acquisition (fixed global order) keeps the wait-for graph acyclic, excluding circular wait. | Classical (Havender, 1968; Coffman conditions, 1971). | scoped — safety only; the deadlock-freedom corollary is disclosed but not proved here |
| SubscheduleSerializability | Removing operations (or a whole transaction) from a conflict-serializable schedule keeps it conflict-serializable. | Classical closure property of conflict-serializability. | scoped — one direction; the converse (upward closure) is refuted with a witness |
| TwoPhaseLocking | Two-phase locking implies conflict-serializability (acyclic precedence graph). | Classical (Eswaran, Gray, Lorie and Traiger, 1976). | full |

Concurrency: 6 modules.

## Distributed

| Module | Proves | Attribution | Scope |
|---|---|---|---|
| AbstractQuorumSystem | Pairwise-intersecting quorums exclude conflicting certification (majorities and Byzantine quorums as instances). | Classical (Malkhi and Reiter, 1998). | scoped — voters cast a single immutable vote (no equivocation); the equivocation-aware strengthening is proved separately |
| ByzantineThreshold | With a node universe of size at most 3f+1, any two quorums of size at least 2f+1 intersect in at least one correct node. | Classical (Pease, Shostak and Lamport, 1980; Bracha; Castro and Liskov, 1999). | full |
| ByzantineTightness | At n = 3f, disagreement is reachable — two quorums can certify contradictory outcomes, so 3f+1 is necessary. | Classical (Pease, Shostak and Lamport, 1980). | full |
| ConsistentCut | A cut is consistent iff it is closed under happens-before. | Classical (Chandy and Lamport, 1985; Mattern, 1989). | full |
| ConsistentCutClosure | Consistent cuts are closed under intersection and union, with the empty/full cuts as bottom/top. | Classical (Mattern, 1989); closure-under-meet-and-join face. | scoped — closure under meet/join only; the lattice laws (absorption, distributivity) are not proved here |
| EquivocationAwareQuorum | With signed votes, at most f faulty (equivocating) voters, and quorum intersection exceeding f, no two quorums certify conflicting outcomes. | Classical (Byzantine quorum systems; Malkhi and Reiter, 1998). | full |
| GCounterConvergence | G-Counter pointwise-max merge forms a join-semilattice; replicas that have seen the same updates converge. | Classical (Shapiro, Preguica, Baquero and Zawirski, 2011). | scoped — three-replica instance |
| LWWConvergence | A total tie-break makes last-writer-wins merge commutative/associative/idempotent (hence convergent); with no tie-break, merge fails. | Classical (last-writer-wins register; Shapiro, Preguica, Baquero and Zawirski, 2011). | scoped — two concrete instances, not a general biconditional |
| LamportClockMonotone | If a scalar clock strictly increases across every happens-before base edge, it strictly increases across the whole relation. | L. Lamport, "Time, Clocks, and the Ordering of Events in a Distributed System", 1978. | scoped — one direction only; the converse is FALSE for scalar clocks, with an explicit counterexample |
| PNCounterConvergence | PN-Counter (paired G-Counters) replicas seeing the same updates converge; the observable value P-N is not monotone. | Classical (Shapiro, Preguica, Baquero and Zawirski, 2011). | full |
| QuorumIntersection | Any two majority subsets of a finite set share a member. | Classical (majority quorums; Thomas, 1979; Gifford, 1979). | full |
| ReplicaConvergence | A commutative, associative, idempotent merge makes replicas that have seen the same updates agree, regardless of delivery order. | Classical (join-semilattice replication; Shapiro, Preguica, Baquero and Zawirski, 2011). | full |
| TwoGeneralsBoundedImpossibility | No k-round deterministic protocol over a lossy channel can guarantee agreement, attack-on-full-delivery, and retreat-on-silence together. | Classical (Akkoyunlu, Ekanadham and Huber, 1969; Gray, 1978). | full |
| TwoPhaseCommitBlocking | Under coordinator crash after prepare, a 2PC participant can remain undecided forever. | Classical (Gray, 1978; Skeen, 1981). | full |
| TwoPhaseCommitBlockingReachable | 2PC blocking, as a reachable execution of the explicit state machine (crash as an event, not a missing case). | Classical (Gray, 1978; Skeen, 1981). | full |
| TwoPhaseCommitMachine | No reachable state of the explicit 2PC machine has one participant committed and another aborted. | Classical (Gray, 1978). | full |
| VectorClockCausality | Vector-clock order holds between two events iff the first happens-before the second, with a concurrency witness. | Classical (Fidge, 1988; Mattern, 1989). | full |

Distributed: 17 modules.

## Order

| Module | Proves | Attribution | Scope |
|---|---|---|---|
| BoundedPath | Every reachability walk over a finite node list can be shortened to a duplicate-free path of length at most the node count. | Classical (graph-theory folklore: every walk contains a simple path). | full |
| FiniteAcyclicSink | A finite nonempty acyclic directed graph has a sink (a node with no outgoing edge). | Classical (every finite nonempty DAG has a sink). | scoped — safety-only statement; no scheduling or liveness claim |
| KnasterTarski | A monotone operator on subsets has a least fixed point, which is also the least pre-fixed point. | Classical (Knaster, 1928; Tarski, 1955). | full |
| NewmanLemma | A locally confluent and terminating abstract rewriting system is confluent. | Classical (Newman, 1942). | full |
| Pigeonhole | A list of mapped values longer than the target's size cannot be duplicate-free. | Classical (Dirichlet). | full |
| SzpilrajnExtension | The one-step order-extension lemma and the finite-maximal-element lemma — the classical ingredients of Szpilrajn's theorem. | Szpilrajn, 1930 (order-extension principle). | scoped — proves the two finite ingredient lemmas plus a concrete 3-element worked instance; the full recursive construction for an arbitrary finite order is not carried out |
| TransitiveClosure | The transitive closure is the least transitive relation containing a relation. | Classical (standard order/relation theory). | full |
| TransitiveReduction | The transitive reduction of a finite directed acyclic graph exists and is unique. | Classical (Aho, Garey and Ullman, 1972). | full |

Order: 8 modules.

## Probability

| Module | Proves | Attribution | Scope |
|---|---|---|---|
| AssociationClosure | Subsets and monotone images of associated random-variable families are associated. | Classical (Esary, Proschan and Walkup, 1967). | full |
| BooleUnionBound | Boole's inequality (union bound) for a finite discrete measure, plus the two-event inclusion-exclusion equality. | Classical (Boole, 1854). | full |
| CauchySchwarzFinite | The finite Cauchy-Schwarz inequality over integer lists, via a sum-of-squares Lagrange identity. | Cauchy (1821); the sum-of-squares proof via the Lagrange identity is classical (Lagrange, 1773, for the 3-term case; the general finite identity is standard). | full |
| ChebyshevList | List-level restatement of Chebyshev's sum inequality, as a corollary of the finite form. | Classical (Chebyshev); corollary form. | full |
| ChebyshevSum | Chebyshev's sum inequality in finite form over integer lists. | Classical (Chebyshev). | full |
| CondorcetJury3 | A majority of three independent better-than-chance voters is more reliable than a single voter. | Classical (Condorcet, 1785); fixed-size finite case. | scoped — fixed jury size three, not the general n-voter theorem |
| CovZeroNotIndep | Zero covariance does not imply independence (explicit finite counterexample). | Classical counterexample (standard probability folklore). | full |
| FrechetDiscreteMeasure | The measure of an intersection is at most the measure of each factor (monotonicity of a finitely additive mass function). | Classical (Frechet, 1935); finite discrete-measure form. | scoped — upper bound only |
| FrechetUpperBound | An intersection of events is contained in each of them, so joint probability never exceeds any marginal. | Classical (Frechet, 1935). | full |
| KroghVedelsby | Ensemble error equals average member error minus average ambiguity (finite rational sum identity). | Classical (Krogh and Vedelsby, 1995). | full |
| MarkovInequality | Discrete/counting form of Markov's inequality for a Nat-valued function on a finite index list. | Markov's inequality (A. A. Markov). | full |

Probability: 11 modules.

## Processes

| Module | Proves | Attribution | Scope |
|---|---|---|---|
| Bisimulation | Bisimilarity is an equivalence relation (identity, converse, composition are bisimulations). | Classical (Park, 1981; Milner). | full |
| Diagnosability | Worked finite automata exhibiting a diagnosable and a non-2-diagnosable discrete-event system. | Classical (Sampath et al., 1995). | scoped — worked finite instances only, not a general diagnosability characterization theorem; the unbounded (for-all-N) negative result is proved separately |
| DiagnosabilityUnbounded | An automaton whose fault is followed only by unobservable events is not N-diagnosable for any N. | Classical (Sampath et al., 1995); unbounded negative form. | full |
| HennessyMilner | Bisimilar states satisfy exactly the same Hennessy-Milner logic formulas. | M. Hennessy and R. Milner, "Algebraic Laws for Nondeterminism and Concurrency", 1985 (the logical characterization of bisimulation traces to their earlier 1980 work). | scoped — the easy direction only (bisimilar implies same formulas); the converse, which additionally needs image-finiteness, is not proved |
| SimulationTraceInclusion | Simulation implies finite-trace inclusion: a simulating implementation exhibits no trace absent from its abstract model. | Classical (Milner). | full |
| TestingPreorder | The De Nicola-Hennessy testing preorder is reflexive and transitive. | Classical (De Nicola and Hennessy, 1984). | full |
| TracePreorderCongruence | The trace-inclusion preorder is preserved by prefix, choice and parallel contexts. | Trace-inclusion congruence for a De Nicola-Hennessy-style process calculus (De Nicola and Hennessy, 1984); scoped here to pure-interleaving trace inclusion. | scoped — pure interleaving (no synchronization); trace-inclusion, weaker than standard may-testing equivalence |

Processes: 7 modules.

## Reliability

| Module | Proves | Attribution | Scope |
|---|---|---|---|
| BirnbaumCriticality | A component is critical for a state vector iff flipping it flips the system; critical components can be counted and ranked. | Classical (Birnbaum, 1969). | full |
| CoherentSystemBounds | For a coherent (monotone, non-degenerate) structure function phi over n components, series(x) ≤ phi(x) ≤ parallel(x) at every state x. | Classical reliability theory (Barlow and Proschan, 1975). | full |
| KOutOfN | The k-out-of-n structure function is monotone; series and parallel are its two extreme special cases. | Classical reliability theory (Birnbaum, 1969; Barlow and Proschan, 1975). | full |
| PivotalDecomposition | Pivotal (Shannon) decomposition of monotone Boolean structure functions, with series and parallel bounds. | Classical (Birnbaum; Barlow and Proschan). | full |
| TripleModularRedundancy | Perfect-voter TMR of three independent e-failing components fails with probability 3e^2 - 2e^3, improving on e for 0 < e < 1/2. | Classical reliability analysis (TMR with a perfect voter; cf. von Neumann, 1956, for the faulty-organ theorem, which this file does NOT prove). | scoped — perfect-voter analysis only; the faulty-organ (von Neumann) case is proved separately |
| VonNeumannFaultyOrgan | Von Neumann multiplexing error analysis when the restoring organ itself is built from unreliable components. | Classical (von Neumann, 1956); scoped finite form. | scoped — an explicit error function with an organ-failure parameter; the full symbolic threshold is not claimed |
| VonNeumannFaultyOrgan2 | Error after a second restoring stage (a nine-gate organ) of the faulty-organ multiplexing analysis. | Classical (von Neumann, 1956); two-stage finite form. | scoped — one extra (two-stage) recursion level; not a general n-level recursive result |

Reliability: 7 modules.

## Security

| Module | Proves | Attribution | Scope |
|---|---|---|---|
| BellLaPadula | Simple-security and star-property together bound write-then-read information flow (no flow from a higher- to a lower-cleared subject); the invariant is preserved under safe access grants. | Bell and LaPadula, 1973. | full |
| BibaIntegrity | The integrity dual of Bell-LaPadula: information cannot flow up in integrity from a lower- to a higher-integrity subject. | K. J. Biba, 1977. | full |
| ChineseWall | An access history built from policy-conforming grants never has one subject access two datasets in the same conflict-of-interest class. | Brewer and Nash, 1989. | scoped — the simple-security (read/access) rule only; the write extension of the classical policy is not formalized |
| HashChainIntegrity | With an abstractly injective link function, equal tips at equal length force equal histories. | Classical (Merkle, 1979; transparency-log folklore). | scoped — link-function injectivity is an assumed hypothesis, not proved; no cryptographic collision-resistance claim is made |
| MerkleInclusion | Merkle inclusion-proof soundness under an injective hash plus leaf/node domain separation (injectivity alone is shown insufficient). | Classical (Merkle, 1979). | scoped — hash injectivity and domain separation are assumed hypotheses, not proved; no cryptographic collision-resistance claim is made |
| MultiDomainNoninterference | Per-observer unwinding conditions imply per-observer noninterference, over an arbitrary set of security domains. | Classical (Goguen and Meseguer, 1982; unwinding in the style of Rushby, 1992). | full |
| Noninterference | The purge lemma and unwinding theorem for Goguen-Meseguer noninterference on a deterministic machine. | Classical (Goguen and Meseguer, 1982). | full |
| SeparationOfDuty | If two roles conflict and no actor holds both, no single actor can complete a dual-control action. | Classical (Clark and Wilson, 1987). | full |
| SeparationOfDutyTxId | The two approvals of a dual-control action on the same transaction must come from two distinct actors. | Classical (Clark and Wilson, 1987); transaction-identified form. | full |

Security: 9 modules.

## Total

7 areas, 65 modules (Concurrency 6, Distributed 17, Order 8, Probability 11, Processes 7, Reliability 7, Security 9); 44 flagged `full`, 21 flagged `scoped`.
