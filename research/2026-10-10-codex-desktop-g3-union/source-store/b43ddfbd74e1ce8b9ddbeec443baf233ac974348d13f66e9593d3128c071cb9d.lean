import G1InitializedOriginatedSpanSeparator
import G1RepeatedExteriorHistoryActualCompletion

/-! Every actual original initialized frontier admits the source-generated
K/history macro for its originated closing bridge span. Physical conditions
are DERIVED; fallback is unnecessary on these canonical real source states.
Contributor: dot, 2026-10-03. -/
namespace G1CanonicalOriginatedMacroPlans
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalDecoratedSpan G1OriginalSpanRegion G1OriginatedNeutralSpanRegion
open G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends G1OriginalSpanClosingPhase
open G1OriginalSpanClosingSourceRow G1OriginatedClosingSourceAdmission G1OriginalExteriorCohort
open G1InitializedOriginatedSpanSeparator G1OriginatedSpanRegistryAdmission
open G1OriginalSpanCalendarDecomposition G1ActualEnteringFrontier G1InitializedFrontierPrefix
open G1ActualJointProgram G1JointForestPreservation G1JointUnrankedForestAssembly
open G1SourceMacroComposition G1RepeatedOriginalExteriorHistoryMacros G1OriginalOpaqueExteriorView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalOriginatedPhysicalPlan (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    PhysicalMacroPlan O.network sample r (closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)) s := by
  let a := D.vertex (T.network.graph.target e)
  let b := D.vertex (T.network.graph.source e)
  let inside := enteringRoots O.network s a
  let outside := exteriorRoots O.network s a
  have hpart := actual_entering_root_partition O.network s a
  have hsep := actual_initialized_originated_span_separator O H D hD sample register gamma common r e he hs
  refine ⟨inside,outside,.node b,Finset.filter_subset _ _,Finset.sdiff_subset,hpart.1,hsep,?_⟩
  intro d hd
  have hbook := actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)
  obtain ⟨first,hfirst,htarget⟩ := actual_start_bridge_endpoint O (bridgeSpan O T D e he) hbook.1
  have hfront : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (O.network.graph.target first))) (initialCode O.network sample register)).support := by
    simpa only [htarget] using hs
  obtain ⟨_,hin,_⟩ := actual_initialized_cut_frontier O.network O.calendar sample register H
    (fun h => gamma h.val) (fun h => common h.val) r first hfirst hfront
  rw [htarget] at hin
  have hl := actual_original_last_cut O (bridgeSpan O T D e he) hbook.2
  exact ⟨actual_agenda_pruned_panel_separation O.network r _ _ _ s hsep
      (current_root_partition_pure (state s) s.property.forest _ _ hpart.1 hpart.2) hd,
    actual_registered_span_closing_exit_support O H gamma common r inside (bridgeSpan O T D e he)
      (actual_originated_bridge_word_registered O H D hD e he) _ hl.2.2 s hin hd⟩

noncomputable def canonicalOriginatedHistoryPlan (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    OriginalHistoryPlan O.network sample r (closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he))
      (originalOutsideCopies O sample (D.vertex (T.network.graph.target e))) s := by
  refine ⟨canonicalOriginatedPhysicalPlan O H D hD sample register gamma common r e he s hs,?_⟩
  have hbook := actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)
  obtain ⟨first,hfirst,htarget⟩ := actual_start_bridge_endpoint O (bridgeSpan O T D e he) hbook.1
  have hfront : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (O.network.graph.target first))) (initialCode O.network sample register)).support := by
    simpa only [htarget] using hs
  have hcohort := actual_initialized_original_exterior_cohort O sample register H gamma common r first hfirst hfront
  rw [htarget] at hcohort
  ext x
  change x ∈ originalExteriorCopies (state s) (exteriorRoots O.network s (D.vertex (T.network.graph.target e))) ↔ _
  simp only [originalExteriorCopies,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (hcohort x).symm

#print axioms canonicalOriginatedPhysicalPlan
#print axioms canonicalOriginatedHistoryPlan
end G1CanonicalOriginatedMacroPlans
