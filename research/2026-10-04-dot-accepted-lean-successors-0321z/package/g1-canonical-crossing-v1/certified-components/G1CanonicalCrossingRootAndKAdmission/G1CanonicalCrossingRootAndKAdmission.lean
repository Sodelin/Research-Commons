import G1OriginalCrossingCalendar

/-! Real canonical crossing frontiers, SAME original future root admission,
and true current-root original-word K labels. No desired row identity is a
plan field. Contributor: dot, 2026-10-03. -/
namespace G1CanonicalCrossingRootAndKAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalDecoratedSpan G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends
open G1OriginalSpanClosingPhase G1OriginalClosingCalendarBinding G1OriginatedClosingSourceAdmission
open G1InitializedFrontierPrefix G1SameOriginalExteriorContinuation G1OriginalCrossingCalendar
open G1ActualKProductInsertion G1OriginalEpochPanelSilence
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_originated_last_cut_source (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e : T.Edge) (he : T.network.graph.IsBridge e) :
    O.network.graph.source (originatedLastCut O H D hD e he) = D.vertex (T.network.graph.source e) :=
  (actual_original_last_cut O (bridgeSpan O T D e he)
    (actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)).2).2.1

/-- Every actual first-frontier continuation through ONE prefix is an actual
second initialized frontier. No stochastic calendar identity is assumed. -/
theorem actual_crossing_second_initialized_frontier (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (a b : O.Vertex) (hab : O.calendar.age a < O.calendar.age b)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (register : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s p : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age a)) (initialCode O.network sample register)).support)
    (hp : p ∈ (sourceProgram O.network r (crossingPrefix O H gamma common a b) s).support) :
    p ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age b)) (initialCode O.network sample register)).support := by
  rw [actual_frontier_original_window_append O H gamma common a b hab,actual_source_program_append]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨s,hs,hp⟩

/-- Original root support is DERIVED for all real three-window/future states.
The second bridge's literal closing cut supplies the unmodified old future. -/
theorem actual_canonical_crossing_same_future_root (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e f : T.Edge) (he : T.network.graph.IsBridge e) (hf : T.network.graph.IsBridge f)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (hab : O.calendar.age (D.vertex (T.network.graph.target e)) < O.calendar.age (D.vertex (T.network.graph.target f)))
    (hbc : O.calendar.age (D.vertex (T.network.graph.target f)) < O.calendar.age (D.vertex (T.network.graph.source e)))
    (hcd : O.calendar.age (D.vertex (T.network.graph.source e)) < O.calendar.age (D.vertex (T.network.graph.source f)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (register : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s p q z d : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support)
    (hp : p ∈ (sourceProgram O.network r (crossingPrefix O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.target f))) s).support)
    (hq : q ∈ (sourceProgram O.network r (crossingConcurrent O H gamma common
      (D.vertex (T.network.graph.target f)) (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)) p).support)
    (hz : z ∈ (sourceProgram O.network r (crossingSuffix O H gamma common
      (D.vertex (T.network.graph.source e)) (D.vertex (T.network.graph.source f))
      (originatedLastCut O H D hD e he) (originatedLastCut O H D hD f hf)) q).support)
    (hd : d ∈ (sourceProgram O.network r (originalClosingFuture O H gamma common
      (originatedLastCut O H D hD f hf)) z).support) : AncestralRoot O.network d := by
  have hpFrontier := actual_crossing_second_initialized_frontier O H gamma common _ _ hab sample register r hs hp
  have hzClosing : z ∈ (sourceProgram O.network r (G1OriginalSpanClosingPhase.closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target f)) (D.vertex (T.network.graph.source f)) (originatedLastCut O H D hD f hf)) p).support := by
    rw [actual_second_crossing_phase O H gamma common _ _ _ _ _
      (actual_originated_last_cut_source O H D hD e he) hbc hcd,actual_source_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨q,hq,hz⟩
  exact actual_originated_closing_future_root_support O H D hD sample register r gamma common f hf hpFrontier hzClosing hd

/-- The first fused private row exposes its TRUE current-root original word
K; the cap is on keep⊆CURRENT live roots, with no old descendant-copy bound. -/
theorem actual_first_crossing_original_word_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (hab : O.calendar.age (D.vertex (T.network.graph.target e)) < O.calendar.age (D.vertex (T.network.graph.target f)))
    (hbc : O.calendar.age (D.vertex (T.network.graph.target f)) < O.calendar.age (D.vertex (T.network.graph.source e)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (keep : Finset Copy)
    (hkeep : keep ⊆ (state s).live)
    (hin : G1OriginalNodeBatchBinding.AtNodePanel (state s) keep (D.vertex (T.network.graph.target e))) :
    actualCurrentRootK O.network r
      (crossingPrefix O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.target f)) ++
        crossingConcurrent O H gamma common (D.vertex (T.network.graph.target f))
          (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)) s keep hkeep =
      actualCurrentRootK O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s keep hkeep := by
  rw [←actual_first_crossing_phase O H gamma common _ _ _ _ hab hbc]
  exact actual_originated_closing_bridge_K O H D hD r gamma common e he keep s hkeep hin

theorem actual_second_crossing_original_word_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e f : T.Edge) (he : T.network.graph.IsBridge e) (hf : T.network.graph.IsBridge f)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (hbc : O.calendar.age (D.vertex (T.network.graph.target f)) < O.calendar.age (D.vertex (T.network.graph.source e)))
    (hcd : O.calendar.age (D.vertex (T.network.graph.source e)) < O.calendar.age (D.vertex (T.network.graph.source f)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (keep : Finset Copy)
    (hkeep : keep ⊆ (state s).live)
    (hin : G1OriginalNodeBatchBinding.AtNodePanel (state s) keep (D.vertex (T.network.graph.target f))) :
    actualCurrentRootK O.network r
      (crossingConcurrent O H gamma common (D.vertex (T.network.graph.target f))
          (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he) ++
        crossingSuffix O H gamma common (D.vertex (T.network.graph.source e))
          (D.vertex (T.network.graph.source f)) (originatedLastCut O H D hD e he) (originatedLastCut O H D hD f hf)) s keep hkeep =
      actualCurrentRootK O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D f hf)) s keep hkeep := by
  rw [←actual_second_crossing_phase O H gamma common _ _ _ _ _
    (actual_originated_last_cut_source O H D hD e he) hbc hcd]
  exact actual_originated_closing_bridge_K O H D hD r gamma common f hf keep s hkeep hin

#print axioms actual_canonical_crossing_same_future_root
#print axioms actual_first_crossing_original_word_K
#print axioms actual_second_crossing_original_word_K
end G1CanonicalCrossingRootAndKAdmission
