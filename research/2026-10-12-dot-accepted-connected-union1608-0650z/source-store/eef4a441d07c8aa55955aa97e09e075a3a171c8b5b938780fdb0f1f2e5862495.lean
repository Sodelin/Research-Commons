import G1CanonicalCrossingPhysicalAdmission

/-! Canonical strict crossing bridge source law, retaining every ORIGINAL
outside checkpoint and SAME completed future. All physical admissions are
DERIVED, not supplied as desired-row identities. -/
namespace G1CanonicalCrossingCompletedSourceLaw
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalCrossingCalendar G1OriginalClosingCalendarBinding G1OriginatedClosingSourceAdmission
open G1InitializedFrontierPrefix
open G1CanonicalCrossingCohortPartition G1CanonicalCrossingPhysicalAdmission
open G1ActualCrossingWholeExteriorHistory G1CrossingHistorySameActualCompletion
open G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- For any two source-derived physical bridges with strictly crossing age
intervals, the pending private actor interpreter has the complete ACTUAL old
source/history/future/completion law. No original descendant-copy cap occurs.
Conversion to K-only actors and all-bridge compilation remain separate. -/
theorem actual_canonical_crossing_completed_source_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e f : T.Edge) (he : T.network.graph.IsBridge e) (hf : T.network.graph.IsBridge f)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (hab : O.calendar.age (D.vertex (T.network.graph.target e)) < O.calendar.age (D.vertex (T.network.graph.target f)))
    (hbc : O.calendar.age (D.vertex (T.network.graph.target f)) < O.calendar.age (D.vertex (T.network.graph.source e)))
    (hcd : O.calendar.age (D.vertex (T.network.graph.source e)) < O.calendar.age (D.vertex (T.network.graph.source f)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {Obs : Type*}
    (sample : Copy → X) (register : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support)
    (readout : UnrankedView O.Vertex O.Edge Copy → Obs) :
    let left := crossingLeftCopies O T D sample e
    let right := crossingRightCopies O T D sample f
    let exterior := crossingExteriorCopies O T D sample e f
    let P := crossingPrefix O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.target f))
    let Q := crossingConcurrent O H gamma common (D.vertex (T.network.graph.target f))
      (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)
    let R := crossingSuffix O H gamma common (D.vertex (T.network.graph.source e)) (D.vertex (T.network.graph.source f))
      (originatedLastCut O H D hD e he) (originatedLastCut O H D hD f hf)
    let future := originalClosingFuture O H gamma common (originatedLastCut O H D hD f hf)
    (actualCrossingPendingHistoryRun O.network r left right exterior P Q R s).bind
      (crossingCompletedTerminal O.network r left right exterior future s readout) =
      actualPhysicalCrossingCompletedHistory O.network r left right exterior P Q R future s readout := by
  dsimp only
  let a := canonicalCrossingPhysicalAdmission O H D hD e f he hf gamma common hab hbc hcd sample register r s hs
  exact actual_crossing_history_same_completed_future O.network r _ _ _ a.cover _ _ _ _ s
    a.prefixSeparate a.concurrentFirst a.concurrentOthers a.suffixSeparate a.middlePure a.finalPure a.rootSupport readout

#print axioms actual_canonical_crossing_completed_source_history
end G1CanonicalCrossingCompletedSourceLaw
