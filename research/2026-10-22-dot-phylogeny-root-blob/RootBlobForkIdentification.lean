import RootBlobBinaryReplacement
import Mathlib.Logic.Equiv.Sum

/-!
# Identify the two-sink target and collapse both ports exactly
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No execution or verification.

This module keeps the degree-two-port intermediate distinct from the actual
binary replacement. Both directions use the exact subdivision theorem;
there is no identity-edge parameter or limiting argument.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobEdgeIndexed RootBlobBoundaryGraph
open RootBlobBoundaryAdapter RootBlobBinaryReplacement
open RootBlobComponentConstructor RootBlobCutFactorization RootBlobRelabeling
open RootBlobEdgeSubdivision
namespace RootBlobForkIdentification
universe u v w x y z
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable {G : Network V E O}
variable (R : RootTwoBoundaryRegion G) (hG : GraphAdmitted G)

noncomputable def outsideEquiv : (R.component hG).Outside ≃ R.Outside where
  toFun := fun v => by
    rcases v with ⟨v, hv⟩
    cases v with
    | inl v =>
      cases v with
      | inl v => exact ⟨v, hv⟩
      | inr v => exact False.elim (hv trivial)
    | inr v => exact False.elim (hv trivial)
  invFun := fun v => ⟨oldVertex v.val, v.property⟩
  left_inv := by
    rintro ⟨v, hv⟩
    cases v with
    | inl v =>
      cases v with
      | inl v => rfl
      | inr v => exact False.elim (hv trivial)
    | inr v => exact False.elim (hv trivial)
  right_inv := by intro v; rfl

noncomputable def outerEdgeEquiv : (R.component hG).OuterEdge ≃ R.OuterEdge where
  toFun := fun e => by
    rcases e with ⟨e, he⟩
    cases e with
    | inl e =>
      cases e with
      | inl e => exact ⟨e, he⟩
      | inr e => exact False.elim (he trivial)
    | inr e => exact False.elim (he trivial)
  invFun := fun e => ⟨oldEdge e.val, e.property⟩
  left_inv := by
    rintro ⟨e, he⟩
    cases e with
    | inl e =>
      cases e with
      | inl e => rfl
      | inr e => exact False.elim (he trivial)
    | inr e => exact False.elim (he trivial)
  right_inv := by intro e; rfl

theorem exteriorSource_at_port (e : (R.component hG).OuterEdge) (i : Fin 2)
    (hs : R.augmented.source e.val = port (V := V) i) :
    (R.component hG).exteriorSource e = Sum.inl i := by
  classical
  have hm : R.augmented.source e.val ∈ (R.component hG).vertices := by
    rw [hs]
    exact R.port_mem i
  unfold RootBlobComponentConstructor.exteriorSource
  rw [dif_pos hm]
  apply congrArg Sum.inl
  apply (R.component hG).ports_injective
  exact (Classical.choose_spec ((R.component hG).outgoing_ports e.val hm e.property)).trans hs

theorem exteriorSource_outside (e : R.OuterEdge)
    (hs : G.source e.val ∉ R.vertices) :
    (R.component hG).exteriorSource ((R.outerEdgeEquiv hG).symm e) =
      Sum.inr ((R.outsideEquiv hG).symm ⟨G.source e.val, hs⟩) := by
  classical
  have h0 : e.val ≠ R.pair.first := by
    intro he; exact hs (by simpa [he] using (R.first_outgoing hG).1)
  have h1 : e.val ≠ R.pair.second := by
    intro he; exact hs (by simpa [he] using (R.second_outgoing hG).1)
  have hsource : R.augmented.source (oldEdge e.val) = oldVertex (G.source e.val) := by
    simp [R.source_old, h0, h1]
  have hout : R.augmented.source (oldEdge e.val) ∉ (R.component hG).vertices := by
    simpa [hsource, component] using hs
  unfold RootBlobComponentConstructor.exteriorSource
  rw [dif_neg hout]
  apply congrArg Sum.inr
  apply Subtype.ext
  exact hsource

noncomputable def portFork :=
  subdivideTwice R.replacement (R.exitEdge hG 0) (R.exitEdge hG 1)

noncomputable def portForkVertexEquiv :
    AugV (V := Sum Unit R.Outside) ≃ Sum (Fin 3) (R.component hG).Outside where
  toFun := fun v => match v with
    | Sum.inl (Sum.inl (Sum.inl _)) => Sum.inl 0
    | Sum.inl (Sum.inl (Sum.inr v)) => Sum.inr ((R.outsideEquiv hG).symm v)
    | Sum.inl (Sum.inr _) => Sum.inl 1
    | Sum.inr _ => Sum.inl 2
  invFun := fun v => match v with
    | Sum.inl p => if p = 0 then oldVertex (Sum.inl ())
      else if p = 1 then port 0 else port 1
    | Sum.inr v => oldVertex (Sum.inr (R.outsideEquiv hG v))
  left_inv := by
    intro v
    rcases v with ((u | v) | p) | q
    · cases u; rfl
    · simp [oldVertex]
    · cases p; rfl
    · cases q; rfl
  right_inv := by
    intro v
    cases v with
    | inl p => fin_cases p <;> rfl
    | inr v => simp [oldVertex]

noncomputable def portForkEdgeEquiv :
    AugE (E := R.OuterEdge) ≃ Sum (Fin 2) (R.component hG).OuterEdge where
  toFun := fun e => match e with
    | Sum.inl (Sum.inl e) => Sum.inr ((R.outerEdgeEquiv hG).symm e)
    | Sum.inl (Sum.inr _) => Sum.inl 0
    | Sum.inr _ => Sum.inl 1
  invFun := fun e => match e with
    | Sum.inl i => freshEdge i
    | Sum.inr e => oldEdge (R.outerEdgeEquiv hG e)
  left_inv := by
    intro e
    rcases e with (e | p) | q
    · simp [oldEdge]
    · cases p; rfl
    · cases q; rfl
  right_inv := by
    intro e
    cases e with
    | inl i => fin_cases i <;> rfl
    | inr e => simp [oldEdge]

/-- An explicit admitted rank transported from the actual two subdivisions.
The final binary replacement itself uses root rank 0 and outside rank
original rank + 2. Intermediate port ranks are 2 and 1, respectively. -/
noncomputable def cutForkRank (v : Sum (Fin 3) (R.component hG).Outside) : ℕ :=
  (R.portFork hG).rank ((R.portForkVertexEquiv hG).symm v)

noncomputable def cutFork :=
  cutNetwork rootedFork ((R.component hG).exterior (R.augmented_admitted hG))
    (R.component hG).labels (R.cutForkRank hG)

theorem portFork_source_old (e : R.OuterEdge) :
    (R.portFork hG).source (oldEdge e) =
      if e = R.exitEdge hG 1 then port 1 else
      if e = R.exitEdge hG 0 then port 0 else oldVertex (R.replacement.source e) := by
  classical
  by_cases h1 : e = R.exitEdge hG 1 <;> by_cases h0 : e = R.exitEdge hG 0 <;>
    simp [portFork, subdivideTwice, subdivide, oldEdge, oldVertex, port, h0, h1]

theorem portFork_source_fresh (i : Fin 2) :
    (R.portFork hG).source (freshEdge (E := R.OuterEdge) i) = oldVertex (Sum.inl ()) := by
  classical
  have h01 := R.exit_distinct hG
  have h10 := Ne.symm h01
  have hs0 : R.replacement.source (R.exitEdge hG 0) = Sum.inl () :=
    (R.source_root_iff _).mpr (R.boundary_out hG 0).1
  have hs1 : R.replacement.source (R.exitEdge hG 1) = Sum.inl () :=
    (R.source_root_iff _).mpr (R.boundary_out hG 1).1
  fin_cases i <;>
    simp [portFork, subdivideTwice, subdivide, freshEdge, oldVertex, h10, hs0, hs1]

theorem portFork_source_identified (e : AugE (E := R.OuterEdge)) :
    R.portForkVertexEquiv hG ((R.portFork hG).source e) =
      (R.cutFork hG).source (R.portForkEdgeEquiv hG e) := by
  classical
  cases e with
  | inl e =>
    cases e with
    | inl e =>
      change R.portForkVertexEquiv hG ((R.portFork hG).source (oldEdge e)) =
        (R.cutFork hG).source (Sum.inr ((R.outerEdgeEquiv hG).symm e))
      by_cases h1 : e = R.exitEdge hG 1
      · subst e
        have hport : R.augmented.source (oldEdge (R.boundaryEdge 1)) = port (V := V) 1 :=
          R.source_boundary 1
        have hx := R.exteriorSource_at_port hG ((R.outerEdgeEquiv hG).symm (R.exitEdge hG 1)) 1 hport
        simp [R.portFork_source_old, cutFork, cutNetwork, RootBlobComponentConstructor.exterior,
          hx, boundarySource, rootedFork, portForkVertexEquiv, port]
      by_cases h0 : e = R.exitEdge hG 0
      · subst e
        have hport := R.source_boundary 0
        have hx := R.exteriorSource_at_port hG ((R.outerEdgeEquiv hG).symm (R.exitEdge hG 0)) 0 hport
        simp [R.portFork_source_old, h1, cutFork, cutNetwork, RootBlobComponentConstructor.exterior,
          hx, boundarySource, rootedFork, portForkVertexEquiv, port]
      have hs : G.source e.val ∉ R.vertices := by
        intro hmem
        rcases (R.pair.cover e.val).mp (Or.inl ⟨hmem, e.property⟩) with he | he
        · exact h0 (Subtype.ext (by simpa [exitEdge, boundaryEdge] using he))
        · exact h1 (Subtype.ext (by simpa [exitEdge, boundaryEdge] using he))
      have hx := R.exteriorSource_outside hG e hs
      simp [R.portFork_source_old, h0, h1, replacement, hs, cutFork, cutNetwork,
        RootBlobComponentConstructor.exterior, hx, boundarySource, portForkVertexEquiv, oldVertex]
    | inr e =>
      cases e
      change R.portForkVertexEquiv hG ((R.portFork hG).source (freshEdge (E := R.OuterEdge) 0)) = _
      rw [R.portFork_source_fresh]
      rfl
  | inr e =>
    cases e
    change R.portForkVertexEquiv hG ((R.portFork hG).source (freshEdge (E := R.OuterEdge) 1)) = _
    rw [R.portFork_source_fresh]
    rfl

theorem portFork_identified :
    relabel (R.portFork hG) (R.portForkVertexEquiv hG) (R.portForkEdgeEquiv hG) = R.cutFork hG := by
  classical
  have hr : R.portForkVertexEquiv hG (R.portFork hG).root = (R.cutFork hG).root := rfl
  have ho : (fun o => R.portForkVertexEquiv hG ((R.portFork hG).observed o)) =
      (R.cutFork hG).observed := by funext o; rfl
  have hs : (fun e => R.portForkVertexEquiv hG
      ((R.portFork hG).source ((R.portForkEdgeEquiv hG).symm e))) =
      (R.cutFork hG).source := by
    funext e
    simpa using R.portFork_source_identified hG ((R.portForkEdgeEquiv hG).symm e)
  have ht : (fun e => R.portForkVertexEquiv hG
      ((R.portFork hG).target ((R.portForkEdgeEquiv hG).symm e))) =
      (R.cutFork hG).target := by
    funext e
    cases e with
    | inl i => fin_cases i <;> rfl
    | inr e =>
      rcases e with ⟨e, he⟩
      cases e with
      | inl e =>
        cases e with
        | inl e => rfl
        | inr e => exact False.elim (he trivial)
      | inr e => exact False.elim (he trivial)
  unfold relabel
  rw [hr, ho, hs, ht]
  rfl

theorem portFork_weights_identified (W : E → ℝ) :
    (fun e => weights (weights (R.replacementWeights W)) ((R.portForkEdgeEquiv hG).symm e)) =
      Sum.elim forkWeights
        (((R.component hG).sourceCut (R.augmented_admitted hG)).outsideWeights
          (weights (weights W))) := by
  classical
  funext e
  cases e with
  | inl i => fin_cases i <;> rfl
  | inr e =>
    change R.replacementWeights W (R.outerEdgeEquiv hG e) =
      weights (weights W) ((R.component hG).edgeEquiv.symm (Sum.inr e))
    rw [(R.component hG).edgeEquiv_symm_inr]
    rcases e with ⟨e, he⟩
    cases e with
    | inl e =>
      cases e with
      | inl e => rfl
      | inr e => exact False.elim (he trivial)
    | inr e => exact False.elim (he trivial)

theorem cutFork_admitted : GraphAdmitted (R.cutFork hG) := by
  rw [← R.portFork_identified hG]
  apply graph_admission_relabel
  exact graph_admitted _ _ (graph_admitted _ _ (R.replacement_admitted hG))

theorem cutFork_weights_admitted (W : E → ℝ) (hW : WeightsAdmitted G W) :
    WeightsAdmitted (R.cutFork hG)
      (Sum.elim forkWeights
        (((R.component hG).sourceCut (R.augmented_admitted hG)).outsideWeights
          (weights (weights W)))) := by
  rw [← R.portFork_identified hG, ← R.portFork_weights_identified hG W]
  apply weights_admission_relabel
  exact weights_admitted _ _ _ (weights_admitted _ _ _ (R.replacement_weights_admitted W hW))

section RelabelImage
variable {V' : Type y} [Fintype V'] [DecidableEq V']
variable {E' : Type z} [Fintype E']

theorem modelImage_relabel (N : Network V E O) (eV : V ≃ V') (eE : E ≃ E')
    (W : E → ℝ) (H : Subgroup (Equiv.Perm S)) :
    RootBlobFullModel.modelImage N W H =
      RootBlobFullModel.modelImage (relabel N eV eE) (fun e => W (eE.symm e)) H := by
  classical
  apply Set.ext
  intro L
  constructor
  · rintro ⟨π, M, hπ, hM, hL⟩
    refine ⟨π, (fun e => M (eE.symm e)), hπ, (fun e => hM _), ?_⟩
    rw [observedLaw_relabel]
    exact hL
  · rintro ⟨π, M', hπ, hM', hL⟩
    let M : E → Mat S := fun e => M' (eE e)
    have hm : (fun e => M (eE.symm e)) = M' := by funext e; simp [M]
    refine ⟨π, M, hπ, (fun e => hM' _), ?_⟩
    rw [← observedLaw_relabel N eV eE W π M, hm]
    exact hL
end RelabelImage

/-- Full observed-law equality for the actual port-suppressed replacement.
Every matrix is free and independent within the full open equivariant class;
the original inheritance is only restricted to surviving edge occurrences. -/
theorem modelImage_eq_replacement [Nonempty S]
    (W : E → ℝ) (hW : WeightsAdmitted G W)
    (H : Subgroup (Equiv.Perm S)) (hS : 1 < Fintype.card S) :
    RootBlobFullModel.modelImage G W H =
      RootBlobFullModel.modelImage R.replacement (R.replacementWeights W) H := by
  have hsub := modelImage_eq_subdivideTwice R.replacement
    (R.exitEdge hG 0) (R.exitEdge hG 1) (R.replacementWeights W) H
    (R.replacement_admitted hG)
  have hiso := modelImage_relabel (R.portFork hG) (R.portForkVertexEquiv hG)
    (R.portForkEdgeEquiv hG) (weights (weights (R.replacementWeights W))) H
  rw [R.portFork_identified hG, R.portFork_weights_identified hG W] at hiso
  calc
    _ = RootBlobFullModel.modelImage (R.cutFork hG)
        (Sum.elim forkWeights
          (((R.component hG).sourceCut (R.augmented_admitted hG)).outsideWeights
            (weights (weights W)))) H :=
      R.modelImage_eq_boundaryFork hG W hW H (R.cutForkRank hG) hS
    _ = RootBlobFullModel.modelImage (R.portFork hG)
        (weights (weights (R.replacementWeights W))) H := hiso.symm
    _ = _ := hsub.symm

end RootBlobForkIdentification
