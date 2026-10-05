import G1ActualWholeUnrootedCutTreeFamily
import G1FiniteNormalizationDisplayedTargets

/-! The constructed bounded ORIGINAL-provenance physical core preserves
the ENTIRE actual displayed rooted-tree family and the entire documented
root-suppressed cut-tree family, for every taxon panel. Complete family
co-occurrence is kept distinct from all earlier C/S/Q union conclusions. -/
namespace G1FiniteCoreWholeDisplayedTreeFamilies
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualGraphNormalization G1ActualTwoPortBlob G1CutChildPorts
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1ReducedCoreCounts
open G1ActualDisplayedTreeFamily G1ActualWholeUnrootedCutTreeFamily
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_step_whole_displayed_tree_families {S T : Source.{u,v,w} X}
    (step : Step S T) (panel : Finset X) :
    actualDisplayedRootedTrees T.network T.calendar panel = actualDisplayedRootedTrees S.network S.calendar panel ∧
      actualDisplayedUnrootedCutTreeFamily T.network T.calendar panel =
        actualDisplayedUnrootedCutTreeFamily S.network S.calendar panel := by
  cases step with
  | splice b hb hp =>
    exact ⟨actual_displayed_rooted_tree_family_splice S.network S.calendar S.cutChild b hb _ panel,
      actual_whole_unrooted_cut_tree_family_splice S.network S.calendar S.cutChild b hb _ panel⟩

theorem actual_steps_whole_displayed_tree_families {S T : Source.{u,v,w} X}
    (steps : Steps S T) (panel : Finset X) :
    actualDisplayedRootedTrees T.network T.calendar panel = actualDisplayedRootedTrees S.network S.calendar panel ∧
      actualDisplayedUnrootedCutTreeFamily T.network T.calendar panel =
        actualDisplayedUnrootedCutTreeFamily S.network S.calendar panel := by
  induction steps with
  | refl => exact ⟨rfl,rfl⟩
  | @tail T U _ step ih =>
    have h := actual_step_whole_displayed_tree_families step panel
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem actual_steps_every_whole_tree_readout_family {S T : Source.{u,v,w} X}
    (steps : Steps S T) (panel : Finset X) {Output : Type*} [DecidableEq Output]
    (readout : UnrankedTree X → Output) :
    (actualDisplayedRootedTrees T.network T.calendar panel).image readout =
      (actualDisplayedRootedTrees S.network S.calendar panel).image readout := by
  rw [(actual_steps_whole_displayed_tree_families steps panel).1]

/-- Source-derived finite physical core with exact inherited census bounds
and WHOLE actual displayed tree-family equality. The stochastic asynchronous
core interpreter is separate; no output-preservation hypothesis is supplied. -/
theorem actual_bounded_originated_core_preserves_whole_displayed_tree_families (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) :
    ∃ (T : Source X) (D : Decoration O T), Steps O T ∧ Originated O H D ∧ Reduced T ∧
      (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧
      Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 ∧
      (∀ panel : Finset X,
        actualDisplayedRootedTrees T.network T.calendar panel = actualDisplayedRootedTrees O.network O.calendar panel ∧
        actualDisplayedUnrootedCutTreeFamily T.network T.calendar panel =
          actualDisplayedUnrootedCutTreeFamily O.network O.calendar panel) := by
  obtain ⟨T,D,steps,origin,reduced,hh,hv,he⟩ := actual_finite_original_decorated_core O H
  exact ⟨T,D,steps,origin,reduced,hh,hv,he,fun panel => actual_steps_whole_displayed_tree_families steps panel⟩

#print axioms actual_steps_every_whole_tree_readout_family
#print axioms actual_bounded_originated_core_preserves_whole_displayed_tree_families
end G1FiniteCoreWholeDisplayedTreeFamilies
