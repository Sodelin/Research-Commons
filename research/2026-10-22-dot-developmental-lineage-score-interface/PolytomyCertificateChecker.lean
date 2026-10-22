/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution or certificate.

Finite Boolean certificate reflection for the FULL standard-clade target,
with all compatible labelings accounted for by the proposed mixed-star adapter.
This is not a parsed-bitstring verifier or a certified polynomial machine.
-/
import PolytomyExactCoverBridge

namespace PolytomyReductionModel

universe u

noncomputable def finiteCellClades {A : Type u} [DecidableEq A] : BTree A → Finset (Finset A)
  | .leaf a => {{a}}
  | .node l r => insert (cellSet (.node l r))
      (finiteCellClades l ∪ finiteCellClades r)

theorem mem_finiteCellClades {A : Type u} [DecidableEq A]
    (T : BTree A) (C : Finset A) : C ∈ finiteCellClades T ↔ CellClade C T := by
  induction T with
  | leaf a =>
      constructor
      · intro hc
        have he : C = {a} := by simpa [finiteCellClades] using hc
        rw [he]
        exact .root (.leaf a)
      · intro hc
        cases hc with
        | root => simp [finiteCellClades, cellSet, observed]
  | node l r ihl ihr =>
      simp only [finiteCellClades, Finset.mem_insert, Finset.mem_union,
        ihl, ihr, cellClade_node_iff]

theorem cellRefines_iff_finiteClades_subset {A : Type u} [DecidableEq A]
    (R T : BTree A) :
    CellRefines R T ↔ finiteCellClades R ⊆ finiteCellClades T := by
  constructor
  · intro h C hC
    exact (mem_finiteCellClades T C).mpr (h C ((mem_finiteCellClades R C).mp hC))
  · intro h C hC
    exact (mem_finiteCellClades T C).mp (h ((mem_finiteCellClades R C).mpr hC))

/-- Independent target DATA: the verifier receives the actual fixed cell
    blocks and integer budget, not the MSSC source object or its cover proof.
    N,m index the finite cell/type domains used by this restricted star family. -/
structure BlockTargetData (N m : ℕ) where
  blocks : Block m → BTree (Cell N m)
  budget : ℕ

noncomputable def canonicalBlockTarget {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    BlockTargetData N m where
  blocks := canonicalBlockTree D
  budget := realizedFixedCost (canonicalBlockTree D) + K - N

/-- A finite certificate predicate. Every candidate topology is permitted;
    no skeleton/caterpillar witness is supplied to this checker. -/
def canonicalTreeCertificate {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) : Prop :=
  (leaves T).Nodup ∧
  cellSet T = Finset.univ.biUnion (fun b => cellSet (canonicalBlockTree D b)) ∧
  (∀ b : Block m, finiteCellClades (canonicalBlockTree D b) ⊆ finiteCellClades T) ∧
  starScore Finset.univ Prod.snd T ≤ realizedFixedCost (canonicalBlockTree D) + K - N

def blockIndexList (m : ℕ) : List (Block m) :=
  none :: (List.finRange m).map some

theorem mem_blockIndexList {m : ℕ} (b : Block m) : b ∈ blockIndexList m := by
  cases b <;> simp [blockIndexList]

noncomputable def checkBlockTarget {N m : ℕ} (G : BlockTargetData N m)
    (T : BTree (Cell N m)) : Bool :=
  decide ((leaves T).Nodup) &&
  decide (cellSet T = Finset.univ.biUnion (fun b => cellSet (G.blocks b))) &&
  ((blockIndexList m).all fun b : Block m =>
    decide (finiteCellClades (G.blocks b) ⊆ finiteCellClades T)) &&
  decide (starScore Finset.univ Prod.snd T ≤ G.budget)

theorem checkBlockTarget_spec {N m : ℕ} (G : BlockTargetData N m)
    (T : BTree (Cell N m)) : checkBlockTarget G T = true ↔
      StandardBlockRefinement G.blocks T ∧ starScore Finset.univ Prod.snd T ≤ G.budget := by
  simp only [checkBlockTarget, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    mem_blockIndexList, forall_true_left, StandardBlockRefinement,
    cellRefines_iff_finiteClades_subset]
  tauto

/-- Reflection into a Boolean uses only finite equality, membership, natural
    comparison and bounded quantification, not real-valued score comparison. -/
noncomputable def checkCanonicalTree {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) : Bool :=
  checkBlockTarget (canonicalBlockTarget D K) T

theorem checkCanonicalTree_spec {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) :
    checkCanonicalTree D K T = true ↔ canonicalTreeCertificate D K T := by
  simp [checkCanonicalTree, checkBlockTarget, canonicalBlockTarget,
    canonicalTreeCertificate, List.all_eq_true, mem_blockIndexList, and_assoc]

theorem canonicalTreeCertificate_iff {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) :
    canonicalTreeCertificate D K T ↔
      StandardBlockRefinement (canonicalBlockTree D) T ∧
      starScore Finset.univ Prod.snd T ≤
        realizedFixedCost (canonicalBlockTree D) + K - N := by
  simp only [canonicalTreeCertificate, StandardBlockRefinement,
    cellRefines_iff_finiteClades_subset]
  tauto

theorem standardCanonicalRefinement_mixed {N m : ℕ} (D : MSSCInstance N m)
    (T : BTree (Cell N m)) (hT : StandardBlockRefinement (canonicalBlockTree D) T) :
    AllInternalMixed Prod.snd T := by
  obtain ⟨xs, hp, hf⟩ := (standardCanonicalRefinement_iff_frontier D T).mp hT
  obtain ⟨t, ht, hi⟩ := BlockFrontier.has_skeleton (canonicalBlockTree D) hf
  exact (TreeIso.mixed_iff Prod.snd hi).mpr
    (realization_graft_mixed D (canonicalBlockTree D)
      (observed_canonicalBlockTree D) (canonicalBlockTree_mixed D) t)

/-- Soundness and completeness include the original existential compatible
    labeling. Its elimination is justified, not silently assumed. -/
theorem standardCanonicalCartaDecision_iff_checked_tree {N m : ℕ}
    (D : MSSCInstance N m) (lambda : ℝ) (K : ℕ) :
    StandardCanonicalCartaDecision D lambda K ↔
      ∃ T : BTree (Cell N m), checkCanonicalTree D K T = true := by
  constructor
  · rintro ⟨L, hT, hf, hc⟩
    have hm := standardCanonicalRefinement_mixed D (eraseStar L) hT
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm] at hc
    refine ⟨eraseStar L, (checkCanonicalTree_spec D K _).mpr ?_⟩
    apply (canonicalTreeCertificate_iff D K _).mpr
    exact ⟨hT, by exact_mod_cast hc⟩
  · rintro ⟨T, hcheck⟩
    obtain ⟨hT, hc⟩ := (canonicalTreeCertificate_iff D K T).mp
      ((checkCanonicalTree_spec D K T).mp hcheck)
    let L : StarLabeledTree (Cell N m) (Terminal N m) := canonicalStar T
    have he : eraseStar L = T := canonicalStar_erase T
    have hf : StarFeasible Prod.snd L := canonicalStar_feasible Prod.snd T
    have hm : AllInternalMixed Prod.snd (eraseStar L) := by
      rw [he]
      exact standardCanonicalRefinement_mixed D T hT
    refine ⟨L, by simpa only [he] using hT, hf, ?_⟩
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm, he]
    exact_mod_cast hc

/-- A certificate cannot hide an unbounded source tree. The bound is derived
    from independently checked clades and all distinct cells. -/
theorem checked_tree_leaf_bound {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) (hcheck : checkCanonicalTree D K T = true) :
    (leaves T).length ≤ (m + 1) * (N + m * N + 3) := by
  have hT := ((canonicalTreeCertificate_iff D K T).mp
    ((checkCanonicalTree_spec D K T).mp hcheck)).1
  obtain ⟨xs, hp, hf⟩ := (standardCanonicalRefinement_iff_frontier D T).mp hT
  obtain ⟨t, ht, hi⟩ := BlockFrontier.has_skeleton (canonicalBlockTree D) hf
  have hv : ValidJoiningTree t := by simpa only [ValidJoiningTree, ht] using hp
  rw [(TreeIso.leaves_perm hi).length_eq]
  exact valid_canonical_graft_leaf_bound D t hv

theorem checked_tree_vertex_bound {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) (hcheck : checkCanonicalTree D K T = true) :
    internalCount T + (leaves T).length < 2 * ((m + 1) * (N + m * N + 3)) := by
  have hl := checked_tree_leaf_bound D K T hcheck
  have he := leaves_length T
  omega

theorem full_mssc_checked_tree_reduction {N m : ℕ} (D : MSSCInstance N m)
    (K : ℕ) (hN : 0 < N) (hm : 2 ≤ m) (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔
      ∃ T : BTree (Cell N m), checkCanonicalTree D K T = true := by
  exact (full_standard_canonical_carta_reduction D 0 K hN hm hNK hKmN).trans
    (standardCanonicalCartaDecision_iff_checked_tree D 0 K)

/-- Composes the whole upstream bridge and full actual-objective reduction,
    ending in finite Boolean acceptance of an arbitrary bounded cell tree. -/
theorem full_exactTripleCover_checked_tree_reduction {q m : ℕ}
    (D : TripleCoverInstance q m) (hq : 0 < q) (hm : 2 ≤ m) :
    ExactTripleCoverDecision D ↔
      ∃ T : BTree (Cell (3 * q) m),
        checkCanonicalTree D.toMSSCInstance (tripleThreshold q m) T = true := by
  exact (full_exactTripleCover_carta_reduction D 0 hq hm).trans
    (standardCanonicalCartaDecision_iff_checked_tree D.toMSSCInstance 0
      (tripleThreshold q m))

/- The Boolean is a finite reflection specification, not a certified machine.
Raw malformed bitstrings, serialization/deserialization, encoded running time,
formal source NP-hardness and elaboration remain explicit open obligations. -/

end PolytomyReductionModel
