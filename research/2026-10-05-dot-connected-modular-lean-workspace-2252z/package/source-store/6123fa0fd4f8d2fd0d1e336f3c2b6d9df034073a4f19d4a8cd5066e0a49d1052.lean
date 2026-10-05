import G1OriginalExteriorCohort

/-! Every source-generated decorated bridge obtains an ORIGINAL precise
closing cut, compact K row, full compiler binding and derived root support.
Contributor: dot, 2026-10-03. Physical multi-span separation remains separate. -/
namespace G1OriginatedClosingSourceAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceAncestralCompletion
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginatedSpanRegistryAdmission G1OriginalSpanCalendarDecomposition
open G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends G1OriginalSpanClosingPhase
open G1OriginalSpanClosingSourceRow G1OriginalClosingCalendarBinding G1OriginalNodeBatchBinding
open G1ActualJointProgram G1SameOriginalExteriorContinuation G1InitializedFrontierPrefix
open G1ActualKProductInsertion G1ActualJointOpaqueContext
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalLastCut (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (hend : EndsBridge O word) : O.Edge := Classical.choose (actual_end_cut_syntax O word hend)

lemma actual_original_last_cut (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (hend : EndsBridge O word) :
    O.network.graph.IsBridge (originalLastCut O word hend) ∧
    O.network.graph.source (originalLastCut O word hend) = b ∧ EndsAt O (originalLastCut O word hend) word :=
  Classical.choose_spec (actual_end_cut_syntax O word hend)

noncomputable def originatedLastCut (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (e : T.Edge) (he : T.network.graph.IsBridge e) : O.Edge :=
  originalLastCut O (bridgeSpan O T D e he)
    (actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)).2

theorem actual_originated_closing_bridge_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (keep : Finset Copy) (s : Code O.network sample)
    (hkeep : keep ⊆ (state s).live) (hs : AtNodePanel (state s) keep (D.vertex (T.network.graph.target e))) :
    actualCurrentRootK O.network r (closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he))
      s keep hkeep =
      actualCurrentRootK O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s keep hkeep := by
  have hc := actual_original_last_cut O (bridgeSpan O T D e he)
    (actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)).2
  have h := congrArg (fun p => p.map Subtype.val)
    (actual_registered_span_closing_source_row O H gamma common r keep (bridgeSpan O T D e he)
      (actual_originated_bridge_word_registered O H D hD e he) _ hc.2.2 s hs)
  simp only [PMF.map_comp,Function.comp_def,projection] at h
  dsimp only [actualCurrentRootK]
  rw [← actual_current_panel_program_law,← actual_current_panel_program_law]
  simpa only [originatedLastCut] using
    congrArg (fun p => p.map UnifiedLean.Source.UnrankedGenealogyObservation.unrankedForest) h

/-- REAL actual original frontier/closing-phase/SAME-future states reach the
ancestral original population, derived from the ORIGINAL full compiler. -/
theorem actual_originated_closing_future_root_support (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (register : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r (closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)) s).support)
    {z : Code O.network sample}
    (hz : z ∈ (sourceProgram O.network r (originalClosingFuture O H gamma common (originatedLastCut O H D hD e he)) d).support) :
    AncestralRoot O.network z := by
  have hc := actual_original_last_cut O (bridgeSpan O T D e he)
    (actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)).2
  have hfull : z ∈ (sourceProgram O.network r
      (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
      (initialCode O.network sample register)).support := by
    rw [actual_original_closing_calendar_decomposition O H gamma common _ _ _ hc.2.1
      (actual_span_dates_strict O.network O.calendar (bridgeSpan O T D e he)),List.append_assoc,
      actual_source_program_append]
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨s,hs,?_⟩
    rw [actual_source_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨d,hd,hz⟩
  exact initialized_original_calendar_ancestral_support O.network O.calendar sample register H
    (fun h => gamma h.val) (fun h => common h.val) r hfull

#print axioms actual_originated_closing_future_root_support
end G1OriginatedClosingSourceAdmission
