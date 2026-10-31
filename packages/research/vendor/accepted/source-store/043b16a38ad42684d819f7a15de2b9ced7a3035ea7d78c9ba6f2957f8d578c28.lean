import G1ActualCircularSplitCompatibility

/-! Exact all-S-compatible ORIGINAL taxon circles, using the accepted
NONTRIVIAL split union. Both-direction actual normalized switching evaluation
and finite source-splice preservation are derived from the checked S binding.
This is the order target; no geometric embedding orders are substituted. -/
namespace G1AcceptedAllCompatibleCircularOrders
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization GProgram.SourceForest
open G1ExactCircularOrderCarrier G1ActualCircularSplitCompatibility G1AcceptedNontrivialSplitTarget
open G1ActualGraphNormalization G1ActualTwoPortBlob G1SplicedSourceAdmission G1CutChildPorts
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1ReducedCoreCounts
open G1ActualDisplayedClusterSplitTransport G1FiniteNormalizationDisplayedTargets
open UnifiedLean.Source.NativeParentRouting
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def sourceCompatibleOrders (N : RootedBinary V E X) : Finset (TaxonCircle X) :=
  compatibleOrders (acceptedDisplayedSplits N Finset.univ)

theorem exact_all_source_compatible_orders_iff (N : RootedBinary V E X) (circle : TaxonCircle X) :
    circle ∈ sourceCompatibleOrders N ↔
      ∀ cut ∈ acceptedDisplayedSplits N Finset.univ, SplitCompatible circle cut :=
  actual_all_split_compatible_orders_iff _ _

/-- EVERY actual normalized displayed-tree evaluation contributes constraints,
and these are ALL the order constraints of the accepted target. -/
theorem actual_orders_iff_every_normalized_switching (N : RootedBinary V E X)
    (C : Calendar N.graph) (circle : TaxonCircle X) :
    circle ∈ sourceCompatibleOrders N ↔
      ∀ switching : N.Switching, ∀ tree : Genealogy X,
        PrunedAt N switching Finset.univ N.root (some tree) →
        ∀ cut ∈ acceptedRootSuppressedSplits tree, SplitCompatible circle cut := by
  rw [exact_all_source_compatible_orders_iff]
  constructor
  · intro h switching tree htree cut hcut
    apply h cut
    exact (accepted_S_iff_actual_normalized_evaluator N C Finset.univ cut).mpr
      ⟨switching,tree,htree,hcut⟩
  · intro h cut hcut
    obtain ⟨switching,tree,htree,hcut⟩ :=
      (accepted_S_iff_actual_normalized_evaluator N C Finset.univ cut).mp hcut
    exact h switching tree htree cut hcut

theorem actual_splice_preserves_every_compatible_circle (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    sourceCompatibleOrders (splicedNetwork N hc b hb A) = sourceCompatibleOrders N := by
  unfold sourceCompatibleOrders
  rw [actual_accepted_S_splice N hc b hb A Finset.univ]

universe u v w
theorem actual_steps_preserve_every_compatible_circle {Y : Type w} [Fintype Y]
    {S T : Source.{u,v,w} Y} (steps : Steps S T) :
    sourceCompatibleOrders T.network = sourceCompatibleOrders S.network := by
  unfold sourceCompatibleOrders
  rw [actual_steps_preserve_accepted_S steps Finset.univ]

/-- A bounded Originated physical core preserves the exact FULL C/S/Q/order
targets. Whole asynchronous stochastic interpretation remains a separate gate. -/
theorem actual_bounded_originated_core_preserves_C_S_Q_and_all_circles {Y : Type w} [Fintype Y]
    (O : Source.{u,v,w} Y) (H : OriginalParentRegistry O.network) :
    ∃ (T : Source Y) (D : Decoration O T), Steps O T ∧ Originated O H D ∧ Reduced T ∧
      (hybrids T.network).card ≤ 2 * Fintype.card Y - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card Y - 5 ∧
      Fintype.card T.Edge ≤ 8 * Fintype.card Y - 8 ∧
      (∀ panel : Finset Y, actualDisplayedClusters T.network panel = actualDisplayedClusters O.network panel ∧
        acceptedDisplayedSplits T.network panel = acceptedDisplayedSplits O.network panel) ∧
      (∀ q : Fin 4 ↪ Y, normalizedDisplayedCutQuartets T.network q = normalizedDisplayedCutQuartets O.network q) ∧
      sourceCompatibleOrders T.network = sourceCompatibleOrders O.network := by
  obtain ⟨T,D,steps,origin,reduced,hh,hv,he,targets,hq⟩ :=
    actual_bounded_originated_core_preserves_accepted_C_S_Q O H
  exact ⟨T,D,steps,origin,reduced,hh,hv,he,targets,hq,actual_steps_preserve_every_compatible_circle steps⟩

#print axioms actual_orders_iff_every_normalized_switching
#print axioms actual_bounded_originated_core_preserves_C_S_Q_and_all_circles
end G1AcceptedAllCompatibleCircularOrders
