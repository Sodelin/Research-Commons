import G1ClosingSpanSafeSyntax

/-! The canonical actual initialized source obtains its multi-span separator
from Originated graph provenance and original cut bookends.
Contributor: dot, 2026-10-03. No separator/output law is an input. -/
namespace G1InitializedOriginatedSpanSeparator
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalDecoratedSpan G1OriginalSpanRegion G1OriginatedNeutralSpanRegion
open G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends G1OriginalSpanClosingPhase
open G1OriginatedClosingSourceAdmission G1ClosingSpanSafeSyntax G1DerivedSpanSeparatedAgenda
open G1OriginalSpanCalendarDecomposition G1ActualEnteringFrontier G1InitializedFrontierPrefix
open G1ActualJointProgram
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_initialized_originated_span_separator (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    SeparatedAgenda O.network r
      (enteringRoots O.network s (D.vertex (T.network.graph.target e)))
      (exteriorRoots O.network s (D.vertex (T.network.graph.target e)))
      (closingSpanAgenda O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))
        (originatedLastCut O H D hD e he)) s := by
  let word := bridgeSpan O T D e he
  have hbook := actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)
  obtain ⟨first,hfirst,htarget⟩ := actual_start_bridge_endpoint O word hbook.1
  have hfront : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (O.network.graph.target first))) (initialCode O.network sample register)).support := by
    simpa only [htarget] using hs
  obtain ⟨_,hin,hout⟩ := actual_initialized_cut_frontier O.network O.calendar sample register H
    (fun h => gamma h.val) (fun h => common h.val) r first hfirst hfront
  rw [htarget] at hin hout
  have hl := actual_original_last_cut O word hbook.2
  have hn := actual_originated_bridge_region_neutral O H D hD e he
  rw [actual_closing_span_prefix_last]
  apply actual_original_span_separated_agenda O word hn _ hl.2.2 H gamma common r _
    (actual_closing_span_prefix_safe O H gamma common _ _ _ hl.2.1 (actual_span_dates_strict O.network O.calendar word))
    s _ _ _ hout
  intro x hx
  rw [hin x hx]
  exact actual_span_input_in_region O word

#print axioms actual_initialized_originated_span_separator
end G1InitializedOriginatedSpanSeparator
