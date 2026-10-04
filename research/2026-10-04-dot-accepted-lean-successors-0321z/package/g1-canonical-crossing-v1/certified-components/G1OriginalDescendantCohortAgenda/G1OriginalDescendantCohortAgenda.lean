import G1SeparatedAgendaSupportCuts

/-! Canonical ORIGINAL descendant cohorts enter every generated bridge word
at its actual one-port interface and remain separated from the original
outside cohort. The old descendant-copy count is unrestricted. -/
namespace G1OriginalDescendantCohortAgenda
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalDecoratedSpan G1OriginalSpanRegion G1OriginatedNeutralSpanRegion
open G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends G1OriginalSpanClosingPhase
open G1OriginatedClosingSourceAdmission G1ClosingSpanSafeSyntax G1DerivedSpanSeparatedAgenda
open G1OriginalSpanCalendarDecomposition G1InitializedFrontierPrefix G1OriginalExteriorCohort
open G1ActiveCoreBridgeCohorts G1ActualJointProgram G1JointSeparatedSourceGeometry
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_initialized_all_original_descendants_at_input (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    ∀ x ∈ originalInsideCopies O sample (D.vertex (T.network.graph.target e)),
      copyLocation (state s) x = .node (D.vertex (T.network.graph.target e)) := by
  have hbook := actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)
  obtain ⟨first,hfirst,htarget⟩ := actual_start_bridge_endpoint O (bridgeSpan O T D e he) hbook.1
  have hfront : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (O.network.graph.target first))) (initialCode O.network sample register)).support := by
    simpa only [htarget] using hs
  have hin := (actual_initialized_cut_frontier O.network O.calendar sample register H
    (fun h => gamma h.val) (fun h => common h.val) r first hfirst hfront).1
  rw [htarget] at hin
  intro x hx
  exact (hin x).mp (Finset.mem_filter.mp hx).2

theorem actual_original_cohort_frontier_population_separator (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    PopulationSeparated (state s) (originalInsideCopies O sample (D.vertex (T.network.graph.target e)))
      (originalOutsideCopies O sample (D.vertex (T.network.graph.target e))) := by
  apply actual_neutral_span_population_separator O (bridgeSpan O T D e he)
    (actual_originated_bridge_region_neutral O H D hD e he)
  · intro x hx
    rw [actual_initialized_all_original_descendants_at_input O H D hD sample register gamma common r e he hs x hx]
    exact actual_span_input_in_region O _
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

theorem actual_initialized_original_cohort_span_separator (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    SeparatedAgenda O.network r (originalInsideCopies O sample (D.vertex (T.network.graph.target e)))
      (originalOutsideCopies O sample (D.vertex (T.network.graph.target e)))
      (closingSpanAgenda O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))
        (originatedLastCut O H D hD e he)) s := by
  let word := bridgeSpan O T D e he
  have hbook := actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)
  have hl := actual_original_last_cut O word hbook.2
  have hn := actual_originated_bridge_region_neutral O H D hD e he
  have hin : ∀ x ∈ originalInsideCopies O sample (D.vertex (T.network.graph.target e)),
      SpanLocation O word (copyLocation (state s) x) := by
    intro x hx
    rw [actual_initialized_all_original_descendants_at_input O H D hD sample register gamma common r e he hs x hx]
    exact actual_span_input_in_region O word
  have hout : ∀ x ∈ originalOutsideCopies O sample (D.vertex (T.network.graph.target e)),
      ¬ O.network.graph.DReach (D.vertex (T.network.graph.target e)) (O.network.leaf (sample x)) :=
    fun x hx => (Finset.mem_filter.mp hx).2
  rw [actual_closing_span_prefix_last]
  exact actual_original_span_separated_agenda O word hn _ hl.2.2 H gamma common r _
    (actual_closing_span_prefix_safe O H gamma common _ _ _ hl.2.1 (actual_span_dates_strict O.network O.calendar word))
    s _ _ hin hout

#print axioms actual_initialized_original_cohort_span_separator
end G1OriginalDescendantCohortAgenda
