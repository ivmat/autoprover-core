/-
  AutoproverCorpus.Security.MerkleInclusion

  Merkle inclusion-proof soundness under an injective hash plus leaf/node domain separation.
  `hleaf` and `hnode` model an idealized, abstractly injective hash; no cryptographic
  collision-resistance claim is made about any concrete hash — injectivity and domain
  separation are explicit hypotheses, not proved.

  Attribution: Classical (Merkle, 1979).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.MerkleInclusion

/-- `leaf (v : V) | node (l r : Tree V)`. -/
inductive Tree (V : Type) where
  | leaf (v : V)
  | node (l r : Tree V)
  deriving DecidableEq

variable {V D : Type}

/-- The digest of a tree: fold `hleaf`/`hnode` over its structure. -/
def root (hleaf : V → D) (hnode : D → D → D) : Tree V → D
  | .leaf v => hleaf v
  | .node l r => hnode (root hleaf hnode l) (root hleaf hnode r)

/-- `v` genuinely occurs as a leaf of `t`. -/
inductive Mem (v : V) : Tree V → Prop
  | here : Mem v (Tree.leaf v)
  | left {l r : Tree V} (h : Mem v l) : Mem v (Tree.node l r)
  | right {l r : Tree V} (h : Mem v r) : Mem v (Tree.node l r)

/-- `hleaf` is injective (per-theorem HYPOTHESIS, never an `axiom`). -/
def HLeafInjective (hleaf : V → D) : Prop := ∀ v v', hleaf v = hleaf v' → v = v'

/-- `hnode` is injective (per-theorem HYPOTHESIS, never an `axiom`). -/
def HNodeInjective (hnode : D → D → D) : Prop :=
  ∀ a b a' b', hnode a b = hnode a' b' → a = a' ∧ b = b'

/-- Domain separation: no leaf digest ever coincides with a node digest — the
    STATEMENT CORRECTION hypothesis (see header), threaded explicitly, never an
    `axiom`. -/
def LeafNodeDisjoint (hleaf : V → D) (hnode : D → D → D) : Prop :=
  ∀ v a b, hleaf v ≠ hnode a b

/-- One inclusion-proof step: combine the current digest with a sibling, on the side
    given by the bit (`false` = current is left, `true` = current is right). -/
def step (hnode : D → D → D) (d : D) (bs : Bool × D) : D :=
  if bs.1 then hnode bs.2 d else hnode d bs.2

/-- The digest reconstructed by folding an inclusion proof up from a leaf value,
    bottom-up (LEFT fold — oldest/closest-to-leaf step first). -/
def computed (hleaf : V → D) (hnode : D → D → D) (v : V) (pf : List (Bool × D)) : D :=
  pf.foldl (step hnode) (hleaf v)

@[simp] theorem computed_nil (hleaf : V → D) (hnode : D → D → D) (v : V) :
    computed hleaf hnode v [] = hleaf v := rfl

theorem computed_append (hleaf : V → D) (hnode : D → D → D)
    (v : V) (pf : List (Bool × D)) (bs : Bool × D) :
    computed hleaf hnode v (pf ++ [bs]) = step hnode (computed hleaf hnode v pf) bs := by
  unfold computed
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Verification: does the proof, folded up from `v`, reach the claimed root? -/
def verify [DecidableEq D] (hleaf : V → D) (hnode : D → D → D)
    (v : V) (pf : List (Bool × D)) (claimedRoot : D) : Bool :=
  decide (computed hleaf hnode v pf = claimedRoot)

theorem verify_eq_true_iff [DecidableEq D] (hleaf : V → D) (hnode : D → D → D)
    (v : V) (pf : List (Bool × D)) (r : D) :
    verify hleaf hnode v pf r = true ↔ computed hleaf hnode v pf = r :=
  decide_eq_true_iff

/-! ### A list-structural helper: peel the LAST element (tail-peeling) -/

private theorem list_last_cases {α : Type} (l : List α) :
    l = [] ∨ ∃ (l' : List α) (a : α), l = l' ++ [a] := by
  induction l with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    refine Or.inr ?_
    rcases ih with h | ⟨l', a, hl'⟩
    · exact ⟨[], x, by simp [h]⟩
    · exact ⟨x :: l', a, by simp [hl']⟩

/-! ### (a) Completeness -/

/-- **(a) Completeness.** A leaf actually in the tree has a proof that verifies. Built
    by induction on the `Mem` derivation, extending the child's proof by one `step` at
    the END on the way back up. -/
theorem completeness [DecidableEq D] (hleaf : V → D) (hnode : D → D → D)
    {v : V} {t : Tree V} (hmem : Mem v t) :
    ∃ pf : List (Bool × D), verify hleaf hnode v pf (root hleaf hnode t) = true := by
  induction hmem with
  | here => exact ⟨[], by simp [verify, computed, root]⟩
  | @left l r _ ih =>
    obtain ⟨pf, hpf⟩ := ih
    have hc : computed hleaf hnode v pf = root hleaf hnode l :=
      (verify_eq_true_iff hleaf hnode v pf (root hleaf hnode l)).mp hpf
    refine ⟨pf ++ [(false, root hleaf hnode r)], ?_⟩
    rw [verify_eq_true_iff, computed_append, hc]
    rfl
  | @right l r _ ih =>
    obtain ⟨pf, hpf⟩ := ih
    have hc : computed hleaf hnode v pf = root hleaf hnode r :=
      (verify_eq_true_iff hleaf hnode v pf (root hleaf hnode r)).mp hpf
    refine ⟨pf ++ [(true, root hleaf hnode l)], ?_⟩
    rw [verify_eq_true_iff, computed_append, hc]
    rfl

/-! ### (b) Soundness -/

/-- **(b) Soundness — the security-relevant direction.** Under `HLeafInjective`,
    `HNodeInjective`, and `LeafNodeDisjoint` (each modeling an idealized injective hash;
    see header), a verifying proof implies membership. Proved by induction on the tree,
    peeling the last proof step at each level via `list_last_cases`. -/
theorem soundness [DecidableEq D] (hleaf : V → D) (hnode : D → D → D)
    (hleafInj : HLeafInjective hleaf) (hnodeInj : HNodeInjective hnode)
    (hdisj : LeafNodeDisjoint hleaf hnode) :
    ∀ (t : Tree V) (v : V) (pf : List (Bool × D)),
      verify hleaf hnode v pf (root hleaf hnode t) = true → Mem v t := by
  intro t
  induction t with
  | leaf w =>
    intro v pf hv
    have heq : computed hleaf hnode v pf = hleaf w :=
      (verify_eq_true_iff hleaf hnode v pf (hleaf w)).mp hv
    rcases list_last_cases pf with hnil | ⟨pf', bs, happ⟩
    · subst hnil
      have h0 : hleaf v = hleaf w := heq
      have hvw := hleafInj v w h0
      subst hvw
      exact Mem.here
    · subst happ
      exfalso
      rw [computed_append] at heq
      unfold step at heq
      split at heq
      · exact hdisj w bs.2 (computed hleaf hnode v pf') heq.symm
      · exact hdisj w (computed hleaf hnode v pf') bs.2 heq.symm
  | node l r ihl ihr =>
    intro v pf hv
    have heq : computed hleaf hnode v pf = hnode (root hleaf hnode l) (root hleaf hnode r) :=
      (verify_eq_true_iff hleaf hnode v pf _).mp hv
    rcases list_last_cases pf with hnil | ⟨pf', bs, happ⟩
    · subst hnil
      exact absurd heq (hdisj v (root hleaf hnode l) (root hleaf hnode r))
    · subst happ
      rw [computed_append] at heq
      unfold step at heq
      split at heq
      · obtain ⟨h1, h2⟩ := hnodeInj _ _ _ _ heq
        exact Mem.right (ihr v pf' ((verify_eq_true_iff hleaf hnode v pf' _).mpr h2))
      · obtain ⟨h1, h2⟩ := hnodeInj _ _ _ _ heq
        exact Mem.left (ihl v pf' ((verify_eq_true_iff hleaf hnode v pf' _).mpr h1))

/-! ### (c) Instances: the digest carrier is the subtree itself -/

/-- Concrete `hleaf`: the digest of a leaf is literally the leaf node. -/
def cHleaf : Bool → Tree Bool := Tree.leaf

/-- Concrete `hnode`: the digest of an internal node is literally that node. -/
def cHnode : Tree Bool → Tree Bool → Tree Bool := Tree.node

/-- Injectivity follows directly from constructor injectivity. -/
theorem cHleaf_injective : HLeafInjective cHleaf := by
  intro v v' h
  injection h

/-- Injectivity follows directly from constructor injectivity. -/
theorem cHnode_injective : HNodeInjective cHnode := by
  intro a b a' b' h
  injection h with h1 h2
  exact ⟨h1, h2⟩

/-- Domain separation follows directly from constructor no-confusion (`leaf` and `node` are
    different constructors of the same inductive type). -/
theorem cLeafNodeDisjoint : LeafNodeDisjoint cHleaf cHnode := by
  intro v a b h
  injection h

/-- A concrete 2-leaf tree: `node (leaf true) (leaf false)`. -/
def sampleTree : Tree Bool := Tree.node (Tree.leaf true) (Tree.leaf false)

/-- The VALID inclusion proof for `true` (the left leaf): sibling is `leaf false`, side
    bit `false` (current is the left child). Verifies. Proved via `rfl` on the underlying
    digest equality (not `decide` at the outer `Bool` level — the `deriving DecidableEq`
    instance for the recursive `Tree` type does not reduce well under `decide`'s kernel
    evaluator; the digest equality itself is a plain structural computation and closes by
    `rfl`). -/
theorem sample_valid_proof_verifies :
    verify cHleaf cHnode true [(false, Tree.leaf false)] (root cHleaf cHnode sampleTree)
      = true :=
  (verify_eq_true_iff cHleaf cHnode true [(false, Tree.leaf false)]
    (root cHleaf cHnode sampleTree)).mpr rfl

/-- An INVALID inclusion proof for `true` — wrong sibling digest — fails. -/
theorem sample_invalid_proof_fails :
    verify cHleaf cHnode true [(false, Tree.leaf true)] (root cHleaf cHnode sampleTree)
      = false :=
  decide_eq_false (by
    intro h
    injection h with _ h2
    injection h2 with h3
    cases h3)

end AutoproverCorpus.MerkleInclusion
