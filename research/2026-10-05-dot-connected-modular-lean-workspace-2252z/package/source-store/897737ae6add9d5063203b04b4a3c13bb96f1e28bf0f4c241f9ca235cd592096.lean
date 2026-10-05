import G1ActualDisplayedQuartetTransport
import G1FiniteOriginalDecoratedCore

/-! All constructed graph normalization steps preserve the ACTUAL displayed
cluster/split/quartet unions. A finite bounded ORIGINAL-provenance decorated
core with these same targets is constructed. Stochastic repeated interpreter
admission and all-n sharpness remain separate G1 gates. -/
namespace G1FiniteNormalizationDisplayedTargets
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1ActualTwoPortBlob G1CutChildPorts
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ActualDisplayedClusterSplitTransport G1ActualDisplayedQuartetTransport
open G1ReducedCoreCounts
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_step_displayed_targets {S T : Source.{u,v,w} X} (step : Step S T) (panel : Finset X) :
    actualDisplayedClusters T.network panel = actualDisplayedClusters S.network panel ∧
    actualDisplayedSplits T.network panel = actualDisplayedSplits S.network panel ∧
    ∀ q : Fin 4 ↪ X, normalizedDisplayedCutQuartets T.network q = normalizedDisplayedCutQuartets S.network q := by
  cases step with
  | splice b hb hp =>
    exact ⟨actual_displayed_clusters_splice S.network S.cutChild b hb _ panel,
      actual_displayed_splits_splice S.network S.cutChild b hb _ panel,
      fun q => actual_normalized_displayed_quartets_splice S.network S.calendar S.cutChild b hb _ q⟩

theorem actual_steps_displayed_targets {S T : Source.{u,v,w} X} (steps : Steps S T) (panel : Finset X) :
    actualDisplayedClusters T.network panel = actualDisplayedClusters S.network panel ∧
    actualDisplayedSplits T.network panel = actualDisplayedSplits S.network panel ∧
    ∀ q : Fin 4 ↪ X, normalizedDisplayedCutQuartets T.network q = normalizedDisplayedCutQuartets S.network q := by
  induction steps with
  | refl => exact ⟨rfl,rfl,fun _ => rfl⟩
  | @tail T U _ step ih =>
    obtain ⟨hc,hs,hq⟩ := actual_step_displayed_targets step panel
    exact ⟨hc.trans ih.1,hs.trans ih.2.1,fun q => (hq q).trans (ih.2.2 q)⟩

/-- Complete ORIGINAL-provenance physical core existence and all documented
displayed C/S/Q targets, with original census caps. No desired source law,
target equality, level bound or fitted demographic parameter is an input. -/
theorem actual_bounded_originated_core_preserves_displayed_targets (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) :
    ∃ (T : Source X) (D : Decoration O T), Steps O T ∧ Originated O H D ∧ Reduced T ∧
      (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧
      Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 ∧
      (∀ panel : Finset X, actualDisplayedClusters T.network panel = actualDisplayedClusters O.network panel ∧
        actualDisplayedSplits T.network panel = actualDisplayedSplits O.network panel) ∧
      (∀ q : Fin 4 ↪ X, normalizedDisplayedCutQuartets T.network q = normalizedDisplayedCutQuartets O.network q) := by
  obtain ⟨T,D,steps,origin,reduced,hh,hv,he⟩ := actual_finite_original_decorated_core O H
  refine ⟨T,D,steps,origin,reduced,hh,hv,he,?_,?_⟩
  · intro panel
    have h := actual_steps_displayed_targets steps panel
    exact ⟨h.1,h.2.1⟩
  · exact (actual_steps_displayed_targets steps Finset.univ).2.2

#print axioms actual_bounded_originated_core_preserves_displayed_targets
end G1FiniteNormalizationDisplayedTargets
