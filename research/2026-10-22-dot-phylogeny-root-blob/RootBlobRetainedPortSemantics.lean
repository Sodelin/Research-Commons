import RootBlobCutFactorization

/-!
# Direct retained-port semantics: one terminal output, not two

Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler, runtime or kernel check was run.
API baseline: mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

This module does not subdivide an original edge. The first internal port is
the chosen terminal b, and the second is a, which may be nonterminal.
Thus its pair table is the transpose of the hand manuscript's (a,b) order.
The existing blendPair formula has exactly this (b,a) orientation:
(E_mu(c) A)^T D_mu. No A/reset commutation is used.

Every resolution retains its original edges and common W/M assignment.
Path exponents may be ZERO. Only the later nucleotide inclusion needs a
positive-weight resolution with a strictly positive exponent.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobDAGNormalization
open RootBlobTreeMarginals RootBlobCutFactorization
namespace RootBlobRetainedPortSemantics
universe u v w x
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2))

/-- Unlike GraphAdmitted, this does not identify every port with a sink. -/
structure PortAdmitted : Prop where
  observed_injective : Function.Injective N.observed
  observed_nonroot : ∀ o, N.observed o ≠ N.root
  edge_rank : ∀ e, N.rank (N.source e) < N.rank (N.target e)
  target_nonroot : ∀ e, N.target e ≠ N.root
  incoming : ∀ v, v ≠ N.root → ∃ e, N.target e = v
  first_sink : ∀ e, N.source e ≠ N.observed 0

theorem portAdmitted_of_graph (hG : RootBlobEdgeIndexed.GraphAdmitted N) :
    PortAdmitted N where
  observed_injective := hG.1
  observed_nonroot := hG.2.1
  edge_rank := hG.2.2.1
  target_nonroot := hG.2.2.2.1
  incoming := hG.2.2.2.2.1
  first_sink := (hG.2.2.2.2.2 _).mpr ⟨0, rfl⟩

/-- Normalization uses rank and stochastic rows, not observation sinks.
This general form also remains available to the separate nucleotide/rate
domains, without changing their transition predicates to OpenTransition. -/
theorem assignmentMass_total_of_rank [Nonempty S]
    (π : S → ℝ) (W : E → ℝ) (M : E → Mat S)
    (hr : ∀ e, N.rank (N.source e) < N.rank (N.target e))
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hπ : (∑ i, π i) = 1)
    (hM : ∀ e i, (∑ j, M e i j) = 1) :
    (∑ a : V → S, RootBlobEdgeIndexed.assignmentMass N π W M a) = 1 := by
  classical
  simp_rw [← product_vertexFactor N W π M]
  apply ranked_normalization N.rank (vertexFactor N W π M)
  · intro v a
    by_cases hv : v = N.root
    · subst v
      simpa only [vertexFactor, if_pos rfl, Function.update_self] using hπ
    · simp only [vertexFactor, if_neg hv]
      rw [Finset.sum_comm]
      calc
        (∑ e, ∑ s, if N.target e = v then
          W e * M e (Function.update a v s (N.source e))
            (Function.update a v s v) else 0) =
            ∑ e, if N.target e = v then W e else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases he : N.target e = v
          · have hs : N.source e ≠ v := by
              intro hh
              have hlt := hr e
              rw [hh, he] at hlt
              exact (Nat.lt_irrefl _) hlt
            simp only [if_pos he, Function.update_of_ne hs, Function.update_self]
            rw [← Finset.mul_sum, hM, mul_one]
          · simp only [if_neg he, Finset.sum_const_zero]
        _ = 1 := hW.2 v hv
  · intro v z a s hvz hrank
    by_cases hv : v = N.root
    · subst v
      simp only [vertexFactor, if_pos rfl, Function.update_of_ne hvz]
    · simp only [vertexFactor, if_neg hv]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : N.target e = v
      · have hs : N.source e ≠ z := by
          intro hh
          have hlt := hr e
          rw [hh, he] at hlt
          exact (not_lt_of_ge hrank) hlt
        simp only [if_pos he, Function.update_of_ne hs, Function.update_of_ne hvz]
      · simp only [if_neg he]

variable (W : E → ℝ) (H : Subgroup (Equiv.Perm S))

theorem assignmentMass_positive (hN : PortAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (π : S → ℝ) (M : E → Mat S)
    (hM : ∀ e, OpenTransition H (M e))
    (a : V → S) (ha : 0 < π (a N.root)) :
    0 < RootBlobEdgeIndexed.assignmentMass N π W M a := by
  classical
  unfold RootBlobEdgeIndexed.assignmentMass
  apply mul_pos ha
  apply Finset.prod_pos
  intro v hv
  obtain ⟨e, he⟩ := hN.incoming v (Finset.mem_erase.mp hv).1
  apply Finset.sum_pos'
  · intro f _
    split_ifs
    · exact le_of_lt (mul_pos (hW.1 f) ((hM f).1.1 _ _))
    · exact le_refl 0
  · refine ⟨e, Finset.mem_univ e, ?_⟩
    simp only [he, if_true]
    exact mul_pos (hW.1 e) ((hM e).1.1 _ _)

theorem pairLaw_positive (hN : PortAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (π : S → ℝ) (M : E → Mat S)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e)) :
    ∀ i j, 0 < RootBlobEdgeIndexed.pairLaw N π W M i j := by
  classical
  have hk : ∃ k, 0 < π k := by
    by_contra h
    push_neg at h
    have hz : ∀ k, π k = 0 := fun k => le_antisymm (h k) (hπ.1.1 k)
    have ht := hπ.1.2
    simp_rw [hz] at ht
    simpa using ht
  obtain ⟨k, hk⟩ := hk
  intro i j
  let a : V → S := fun v =>
    if v = N.observed 0 then i else if v = N.observed 1 then j else k
  have h01 : N.observed 0 ≠ N.observed 1 := by
    intro he
    have hh := hN.observed_injective he
    norm_num at hh
  have hr0 := Ne.symm (hN.observed_nonroot 0)
  have hr1 := Ne.symm (hN.observed_nonroot 1)
  have haroot : a N.root = k := by simp [a, hr0, hr1]
  have haout : ∀ o : Fin 2,
      a (N.observed o) = if o = 0 then i else j := by
    intro o
    fin_cases o <;> simp [a, h01, Ne.symm h01]
  unfold RootBlobEdgeIndexed.pairLaw RootBlobEdgeIndexed.observedLaw
  apply Finset.sum_pos'
  · intro b _
    split_ifs
    · exact RootBlobOpenProof.Edge.assignmentMass_nonnegative N W H π M hW hπ hM b
    · exact le_refl 0
  · refine ⟨a, Finset.mem_univ a, ?_⟩
    rw [if_pos haout]
    apply assignmentMass_positive N W H hN hW π M hM a
    rw [haroot]
    exact hk

theorem soundness [Nonempty S] (hN : PortAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) :
    RootBlobOpenProof.Edge.SourceSoundness N W H := by
  intro π M hπ hM
  refine ⟨pairLaw_positive N W H hN hW π M hπ hM, ?_,
    RootBlobOpenProof.Edge.pairLaw_invariant N W H π M hπ hM⟩
  rw [RootBlobDAGNormalization.Edge.pairLaw_total_eq_assignmentMass N W π M]
  exact assignmentMass_total_of_rank N π W M hN.edge_rank hW hπ.1.2
    (fun e => (hM e).1.2)

variable {W H}

def selectedTree (hN : PortAdmitted N) (σ : RootBlobSwitching.Switching N) :
    ParentTree V where
  root := N.root
  rank := N.rank
  parent := RootBlobSwitching.parent N σ
  parent_rank := by
    intro v
    simpa only [RootBlobSwitching.parent, (σ v).property] using
      hN.edge_rank (σ v).val

theorem selectedTree_mass (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) (π : S → ℝ) (M : E → Mat S)
    (a : V → S) :
    (selectedTree N hN σ).mass π (fun v => M (σ v).val) a =
      RootBlobSwitching.resolvedMass N π M σ a := by
  classical
  unfold ParentTree.mass
  rw [prod_split N.root]
  unfold RootBlobSwitching.resolvedMass
  simp only [ParentTree.factor, selectedTree, dif_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  simp only [v.property, dif_neg]
  rfl

theorem selectedTree_joint (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) (π : S → ℝ) (M : E → Mat S) :
    (selectedTree N hN σ).joint π (fun v => M (σ v).val)
      (N.observed 0) (N.observed 1) =
      RootBlobSwitching.resolvedPair N π M σ := by
  classical
  funext i j
  unfold ParentTree.joint RootBlobSwitching.resolvedPair
  apply Finset.sum_congr rfl
  intro a _
  rw [selectedTree_mass N hN σ π M a]
  have hc : (∀ o : Fin 2, a (N.observed o) = if o = 0 then i else j) ↔
      a (N.observed 0) = i ∧ a (N.observed 1) = j := by
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1⟩
    · rintro ⟨h0, h1⟩ o
      fin_cases o
      · simpa using h0
      · simpa using h1
  rw [hc]
  split_ifs <;> simp

def firstVertex (hN : PortAdmitted N) (σ : RootBlobSwitching.Switching N) :
    (selectedTree N hN σ).NR := ⟨N.observed 0, hN.observed_nonroot 0⟩

theorem firstLeaf (hN : PortAdmitted N) (σ : RootBlobSwitching.Switching N) :
    (selectedTree N hN σ).IsLeaf (firstVertex N hN σ).val := by
  intro v
  exact hN.first_sink (σ v).val

def secondVertex (hN : PortAdmitted N) : {u : V // u ≠ N.observed 0} :=
  ⟨N.observed 1, by
    intro he
    have hh := hN.observed_injective he
    norm_num at hh⟩

def prunedTree (hN : PortAdmitted N) (σ : RootBlobSwitching.Switching N) :
    ParentTree {u : V // u ≠ N.observed 0} :=
  (selectedTree N hN σ).prune (firstVertex N hN σ) (firstLeaf N hN σ)

def parentPort (hN : PortAdmitted N) (σ : RootBlobSwitching.Switching N) :
    {u : V // u ≠ N.observed 0} :=
  ⟨(selectedTree N hN σ).parent (firstVertex N hN σ),
    firstLeaf N hN σ (firstVertex N hN σ)⟩

noncomputable def pathExponent [Nonempty S] (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) : ℕ :=
  ((prunedTree N hN σ).distanceCertificate (S := S)).distance
    (parentPort N hN σ) (secondVertex N hN)

theorem resolved_formula [Nonempty S] (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) (μ : S → ℝ)
    (hμ : (∑ i, μ i) = 1) (t : ℝ) (A : Mat S) :
    RootBlobSwitching.resolvedPair N μ
      (RootBlobOpenProof.Edge.terminalAssignment N A (equalInput μ t)) σ =
      blendPair μ (t ^ pathExponent (S := S) N hN σ) A := by
  rw [← selectedTree_joint N hN σ]
  have hp : (fun v : (selectedTree N hN σ).NR =>
      RootBlobOpenProof.Edge.terminalAssignment N A (equalInput μ t) (σ v).val) =
      (selectedTree N hN σ).terminalMatrices (firstVertex N hN σ) A
        (equalInput μ t) := by
    classical
    funext v
    unfold RootBlobOpenProof.Edge.terminalAssignment ParentTree.terminalMatrices
    rw [(σ v).property]
    rfl
  rw [hp]
  exact (selectedTree N hN σ).terminal_leaf_pair
    (firstVertex N hN σ) (firstLeaf N hN σ) (secondVertex N hN) μ hμ t A

theorem pair_formula [Nonempty S] (hN : PortAdmitted N)
    (W : E → ℝ) (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (μ : S → ℝ) (hμ : (∑ i, μ i) = 1) (t : ℝ) (A : Mat S) :
    RootBlobEdgeIndexed.pairLaw N μ W
      (RootBlobOpenProof.Edge.terminalAssignment N A (equalInput μ t)) =
      blendPair μ (coefficient (RootBlobSwitching.weight N W)
        (pathExponent (S := S) N hN) t) A := by
  rw [RootBlobSwitching.pairLaw_expansion]
  simp_rw [resolved_formula N hN _ μ hμ t A]
  exact RootBlobSwitching.blendPair_average (RootBlobSwitching.weight N W)
    (RootBlobSwitching.weight_total N W hW) μ A
    (fun σ => t ^ pathExponent (S := S) N hN σ)

/-- No positive-exponent assumption appears: coefficient continuity at one
works for a finite sum of nonnegative integer powers, including power zero. -/
theorem realize [Nonempty S] (hN : PortAdmitted N)
    (W : E → ℝ) (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (H : Subgroup (Equiv.Perm S)) {P : Mat S}
    (hP : PositiveInvariantPair H P) :
    ∃ (π : S → ℝ) (M : E → Mat S),
      (∀ i, 0 < π i) ∧ RootAdmitted H π ∧
      (∀ e, OpenTransition H (M e)) ∧
      RootBlobEdgeIndexed.pairLaw N π W M = P := by
  classical
  let μ := secondMarginal P
  let M := conditional P
  let ν := rowAction μ M
  have hμpos : ∀ i, 0 < μ i := marginal_positive hP.1
  have hμ : RootAdmitted H μ := marginal_root hP
  have hM : OpenTransition H M := conditional_open hP
  have hνtotal : (∑ i, ν i) = 1 := rowAction_total hμ.1.2 hM.1.2
  have hνinv : Invariant H ν := rowAction_invariant hμ.2 hM.2
  obtain ⟨t, ht0, ht1, hc0, hnum⟩ := exists_compensation_parameter
    (pathExponent (S := S) N hN) (RootBlobSwitching.weight_total N W hW) hM.1.1 ν
  let c := coefficient (RootBlobSwitching.weight N W) (pathExponent (S := S) N hN) t
  let A := compensate M ν c
  have hc : c ≠ 0 := ne_of_gt hc0
  have hA : OpenTransition H A := by
    refine ⟨⟨?_, compensate_rows hM.1.2 hνtotal hc⟩,
      compensate_invariant hM.2 hνinv⟩
    intro i j
    exact div_pos (hnum i j) hc0
  refine ⟨μ, RootBlobOpenProof.Edge.terminalAssignment N A (equalInput μ t),
    hμpos, hμ, RootBlobOpenProof.Edge.terminalAssignment_open N H hA
      (equalInput_open hμ hμpos ht0 ht1), ?_⟩
  rw [pair_formula N hN W hW μ hμ.1.2 t A]
  change blendPair μ c (compensate M (rowAction μ M) c) = P
  rw [compensate_blend hμ.1.2 hc]
  funext i j
  exact conditional_reconstruct hP.1 i j

theorem openImage_eq [Nonempty S] (hN : PortAdmitted N)
    (W : E → ℝ) (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (H : Subgroup (Equiv.Perm S)) :
    RootBlobEdgeIndexed.openImage N W H = {P | PositiveInvariantPair H P} := by
  apply Set.ext
  intro P
  constructor
  · rintro ⟨π, M, hπ, hM, rfl⟩
    exact soundness N W H hN hW π M hπ hM
  · intro hP
    obtain ⟨π, M, _, hπ, hM, heq⟩ := realize N hN W hW H hP
    exact ⟨π, M, hπ, hM, heq⟩

/-- This is the graph-only strict-exponent fact needed for the LITERAL
nucleotide domain. It does not assume the second port is a sink. -/
theorem exists_positive_pathExponent [Nonempty S] (hN : PortAdmitted N)
    (e : E) (he : N.target e = N.observed 0)
    (hne : N.source e ≠ N.observed 1) :
    ∃ σ : RootBlobSwitching.Switching N, 0 < pathExponent (S := S) N hN σ := by
  classical
  let σ : RootBlobSwitching.Switching N := fun v =>
    if h : v.val = N.observed 0 then ⟨e, he.trans h.symm⟩
    else ⟨Classical.choose (hN.incoming v.val v.property),
      Classical.choose_spec (hN.incoming v.val v.property)⟩
  refine ⟨σ, Nat.pos_of_ne_zero ?_⟩
  intro hz
  have hp := (((prunedTree N hN σ).distanceCertificate (S := S)).zero_iff
    (parentPort N hN σ) (secondVertex N hN)).mp hz
  apply hne
  have hv := congrArg Subtype.val hp
  simpa [parentPort, secondVertex, selectedTree, RootBlobSwitching.parent,
    firstVertex, σ] using hv

end RootBlobRetainedPortSemantics
