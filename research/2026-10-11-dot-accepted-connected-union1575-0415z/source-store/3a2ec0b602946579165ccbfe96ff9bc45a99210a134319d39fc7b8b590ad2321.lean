import G1CanonicalOriginatedMacroPlans

/-! The total canonical planner is explicitly SOME on every real original
frontier. Its exposed macro K is the generated original-span K; no desired
kernel equality is a planner field. Contributor: dot, 2026-10-03. -/
namespace G1CanonicalOriginatedHistoryPlanner
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalDecoratedSpan G1OriginalSpanClosingPhase G1OriginatedClosingSourceAdmission
open G1OriginalExteriorCohort G1CanonicalOriginatedMacroPlans
open G1ActualEnteringFrontier G1InitializedFrontierPrefix
open G1RepeatedOriginalExteriorHistoryMacros G1ActualHistoryEnrichedKMacro
open G1ActualKProductInsertion G1ActualJointEpoch G1ActualJointStageHistory
open G1UnrankedExteriorHistoryKInsertion G1OriginalOpaqueExteriorView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalHistoryPlanner (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample) :
    Option (OriginalHistoryPlan O.network sample r (closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he))
      (originalOutsideCopies O sample (D.vertex (T.network.graph.target e))) s) :=
  if hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support then
    some (canonicalOriginatedHistoryPlan O H D hD sample register gamma common r e he s hs)
  else none

theorem actual_canonical_history_planner_some (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    canonicalHistoryPlanner O H D hD sample register gamma common r e he s =
      some (canonicalOriginatedHistoryPlan O H D hD sample register gamma common r e he s hs) := by
  rw [canonicalHistoryPlanner,dif_pos hs]

theorem actual_canonical_history_row_uses_true_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    admittedHistoryRow O.network r (closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he))
      (originalOutsideCopies O sample (D.vertex (T.network.graph.target e)))
      (canonicalHistoryPlanner O H D hD sample register gamma common r e he) s =
    sourceKHistoryMacro O.network r (enteringRoots O.network s (D.vertex (T.network.graph.target e)))
      (exteriorRoots O.network s (D.vertex (T.network.graph.target e)))
      (closingSpanAgenda O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))
        (originatedLastCut O H D hD e he)) s (Finset.filter_subset _ _) := by
  rw [admittedHistoryRow,actual_canonical_history_planner_some O H D hD sample register gamma common r e he s hs]
  rfl

theorem actual_canonical_history_row_uses_original_span_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    let a := D.vertex (T.network.graph.target e)
    let inside := enteringRoots O.network s a
    let outside := exteriorRoots O.network s a
    let phase := closingSpanAgenda O H gamma common a (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)
    admittedHistoryRow O.network r phase (originalOutsideCopies O sample a)
      (canonicalHistoryPlanner O H D hD sample register gamma common r e he) s =
      (independentProduct
        (actualCurrentRootK O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he))
          s inside (Finset.filter_subset _ _))
        ((sourceStageHistory O.network r phase s).map (exteriorHistory O.network outside))).map
          (fun data => (data.2.map (opaqueExteriorView (state s) outside),
            realHistoryEndpoint O.network r inside outside phase s data)) := by
  dsimp only
  rw [actual_canonical_history_row_uses_true_K O H D hD sample register gamma common r e he s hs,
    sourceKHistoryMacro]
  have hin : ∀ x ∈ enteringRoots O.network s (D.vertex (T.network.graph.target e)),
      copyLocation (state s) x = .node (D.vertex (T.network.graph.target e)) := by
    intro x hx
    obtain ⟨hx,hpop⟩ := Finset.mem_filter.mp hx
    have hr := s.property.forest.representative x hx
    change (state s).ancestor x = x at hr
    change (state s).location ((state s).ancestor x) = _
    rw [hr]
    exact hpop
  have hK := actual_originated_closing_bridge_K O H D hD r gamma common e he
    (enteringRoots O.network s (D.vertex (T.network.graph.target e))) s (Finset.filter_subset _ _) hin
  simp only [enteringRoots] at hK ⊢
  rw [hK]

#print axioms actual_canonical_history_row_uses_original_span_K
#print axioms actual_canonical_history_row_uses_true_K
end G1CanonicalOriginatedHistoryPlanner
