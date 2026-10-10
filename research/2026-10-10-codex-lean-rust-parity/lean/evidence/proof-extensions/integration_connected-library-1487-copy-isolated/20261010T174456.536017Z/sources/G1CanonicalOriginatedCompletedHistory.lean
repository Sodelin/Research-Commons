import G1CanonicalOriginatedHistoryPlanner

/-! Canonical admission of an original-source bridge K/history macro through
its SAME original future and actual unbounded ancestral completion. This is a
single bridge interface; overlapping bridge scheduling remains separate.
Contributor: dot, 2026-10-03. -/
namespace G1CanonicalOriginatedCompletedHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCompletionHarmonic
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanClosingPhase G1OriginalClosingCalendarBinding G1OriginatedClosingSourceAdmission
open G1OriginalExteriorCohort G1CanonicalOriginatedHistoryPlanner
open G1RepeatedOriginalExteriorHistoryMacros G1RepeatedExteriorHistoryActualCompletion
open G1InitializedFrontierPrefix G1SameOriginalExteriorContinuation
open G1SourceMacroActualCompletion G1UnrankedSourceView G1OriginalWholeCausalView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalHistoryStage (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e) :
    OriginalHistoryStage O.network sample r where
  phase := closingSpanAgenda O H gamma common (D.vertex (T.network.graph.target e))
    (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)
  observedOutside := originalOutsideCopies O sample (D.vertex (T.network.graph.target e))
  planner := canonicalHistoryPlanner O H D hD sample register gamma common r e he

/-- All physical separator/exit/cohort and future-root support conditions are
DERIVED from real initialized original source support and Originated provenance.
The macro retains the entire original outside checkpoint path jointly with the
actual completed forest readout. No output-law hypothesis is supplied. -/
theorem actual_canonical_originated_K_completed_exterior_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {Obs : Type*}
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support)
    (readout : UnrankedView O.Vertex O.Edge Copy → Obs) :
    let stages := [canonicalHistoryStage O H D hD sample register gamma common r e he]
    let future := originalClosingFuture O H gamma common (originatedLastCut O H D hD e he)
    historyEnrichedMacroRun O.network r (actualCompletedTerminal O.network r future s readout) stages s =
      actualPhysicalCompletedExteriorHistories O.network r future readout stages s := by
  dsimp only
  apply actual_repeated_K_original_exterior_histories_completed_future
  intro z hz
  have hz' : z ∈ (sourceProgram O.network r
      (closingSpanAgenda O H gamma common (D.vertex (T.network.graph.target e))
        (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he) ++
       originalClosingFuture O H gamma common (originatedLastCut O H D hD e he)) s).support := by
    simpa only [historyLiteralProgram,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      canonicalHistoryStage] using hz
  rw [actual_source_program_append] at hz'
  obtain ⟨d,hd,hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz'
  exact actual_originated_closing_future_root_support O H D hD sample register r gamma common e he hs hd hzd

#print axioms actual_canonical_originated_K_completed_exterior_history
end G1CanonicalOriginatedCompletedHistory
