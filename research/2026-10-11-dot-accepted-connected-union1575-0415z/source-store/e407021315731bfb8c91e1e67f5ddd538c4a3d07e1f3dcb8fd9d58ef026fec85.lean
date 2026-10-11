import G1FiniteNormalizationDisplayedTargets

/-! Exact accepted S from PROOFS.md§2.1: the distinct union of NONTRIVIAL
displayed-tree unordered splits. The frozen displayed6 checkpoint preserves
all proper cuts; filtering BOTH side cardinalities≥2 gives the accepted target.
Contributor: dot, 2026-10-03. Frozen source bytes remain unchanged. -/
namespace G1AcceptedNontrivialSplitTarget
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1ActualTwoPortBlob G1SplicedSourceAdmission G1CutChildPorts
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1ReducedCoreCounts
open G1ActualDisplayedClusterSplitTransport G1FiniteNormalizationDisplayedTargets
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

def NontrivialCut (cut : Finset (Finset X)) : Prop := ∀ side ∈ cut, 2 ≤ side.card

lemma nontrivial_unordered_cut_iff (panel D : Finset X) :
    NontrivialCut {D,panel \ D} ↔ 2 ≤ D.card ∧ 2 ≤ (panel \ D).card := by
  simp [NontrivialCut]

noncomputable def acceptedDisplayedSplits (N : RootedBinary V E X) (panel : Finset X) :
    Finset (Finset (Finset X)) := (actualDisplayedSplits N panel).filter NontrivialCut

noncomputable def acceptedRootSuppressedSplits (T : Genealogy X) : Finset (Finset (Finset X)) :=
  (rootSuppressedCuts T).filter NontrivialCut

theorem accepted_S_iff_actual_normalized_evaluator (N : RootedBinary V E X)
    (C : Calendar N.graph) (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ acceptedDisplayedSplits N panel ↔
      ∃ S : N.Switching, ∃ T : Genealogy X, PrunedAt N S panel N.root (some T) ∧
        cut ∈ acceptedRootSuppressedSplits T := by
  simp only [acceptedDisplayedSplits,acceptedRootSuppressedSplits,Finset.mem_filter]
  rw [actual_displayed_splits_iff_normalized_evaluator N C panel cut]
  constructor
  · rintro ⟨⟨S,T,hT,hcut⟩,hn⟩
    exact ⟨S,T,hT,hcut,hn⟩
  · rintro ⟨S,T,hT,hcut,hn⟩
    exact ⟨⟨S,T,hT,hcut⟩,hn⟩

theorem actual_accepted_S_splice (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) (panel : Finset X) :
    acceptedDisplayedSplits (splicedNetwork N hc b hb A) panel = acceptedDisplayedSplits N panel := by
  rw [acceptedDisplayedSplits,acceptedDisplayedSplits,actual_displayed_splits_splice]

universe u v w
theorem actual_steps_preserve_accepted_S {Y : Type w} [Fintype Y]
    {S T : Source.{u,v,w} Y} (steps : Steps S T) (panel : Finset Y) :
    acceptedDisplayedSplits T.network panel = acceptedDisplayedSplits S.network panel := by
  unfold acceptedDisplayedSplits
  rw [(actual_steps_displayed_targets steps panel).2.1]

theorem actual_bounded_originated_core_preserves_accepted_C_S_Q {Y : Type w} [Fintype Y]
    (O : Source.{u,v,w} Y) (H : OriginalParentRegistry O.network) :
    ∃ (T : Source Y) (D : Decoration O T), Steps O T ∧ Originated O H D ∧ Reduced T ∧
      (hybrids T.network).card ≤ 2 * Fintype.card Y - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card Y - 5 ∧
      Fintype.card T.Edge ≤ 8 * Fintype.card Y - 8 ∧
      (∀ panel : Finset Y, actualDisplayedClusters T.network panel = actualDisplayedClusters O.network panel ∧
        acceptedDisplayedSplits T.network panel = acceptedDisplayedSplits O.network panel) ∧
      (∀ q : Fin 4 ↪ Y, normalizedDisplayedCutQuartets T.network q = normalizedDisplayedCutQuartets O.network q) := by
  obtain ⟨T,D,steps,origin,reduced,hh,hv,he,targets,hq⟩ :=
    actual_bounded_originated_core_preserves_displayed_targets O H
  exact ⟨T,D,steps,origin,reduced,hh,hv,he,
    fun panel => ⟨(targets panel).1,actual_steps_preserve_accepted_S steps panel⟩,hq⟩

#print axioms actual_bounded_originated_core_preserves_accepted_C_S_Q
end G1AcceptedNontrivialSplitTarget
