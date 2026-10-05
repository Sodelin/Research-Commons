import G1CanonicalOriginalAdjacentRecordedRow

/-! Whole chronological ORIGINAL suffix induction. Every actual boundary and
epoch is processed once, every original root/ancestral checkpoint is retained
jointly, and each next-frontier admission is derived from the SAME initialized
original source. This is the all-date stochastic compiler bridge. -/
namespace G1CanonicalWholeCalendarRecordedSuffix
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalOriginalNodeAsyncBatch G1CanonicalOriginalExitAsyncStep
open G1CanonicalOriginalBoundaryAsyncBatch G1CanonicalOriginalEpochAsync
open G1CanonicalOriginalDateGapRoles G1CanonicalOriginalBoundaryEpochAdmission
open G1CanonicalOriginalAdjacentRecordedRow G1ActualOriginalBoundaryRootHistory
open G1ActualOriginalRootRecordedProgram G1PendingBaseCheckpointRecorder
open G1PendingOriginalRootBlobCheckpointHistory G1PendingActorInterfaceCommutation
open G1ContextualForestReplacement G1SameOriginalExteriorContinuation
open G1ActualJointProgram
open G1InitializedFrontierPrefix G1CanonicalThreeEpochList G1UnrankedSourceView
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

def lastCalendarDate : ℝ → List ℝ → ℝ
  | date,[] => date
  | _,next::later => lastCalendarDate next later

noncomputable def canonicalRecordedCalendarSuffix (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) :
    ℝ → List ℝ → List (AsyncOperation (BridgeActor T) (UnrankedView O.Vertex O.Edge Copy)
      (UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)))
  | date,[] => canonicalRecordedBoundaryOps O H D hD sample gamma common r date
  | date,next::later => canonicalRecordedBoundaryEpochOps O H D hD sample gamma common r date next ++
      canonicalRecordedCalendarSuffix O H D hD sample gamma common r next later

/-- Complete chronological joint source/history suffix row, for arbitrary
finite simultaneous/overlapping actor families. The sole source admission is
actual initialized prefix support; suffix dates are the compiler's own list. -/
theorem actual_real_whole_original_calendar_suffix_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node : O.Vertex) (dates : List ℝ)
    (heq : afterDate O.network O.calendar (O.calendar.age node) = dates) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
        calendarTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) dates) s history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D (lastCalendarDate (O.calendar.age node) dates) result.1)) =
    asyncProgram (canonicalRecordedCalendarSuffix O H D hD sample gamma common r (O.calendar.age node) dates)
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) [] s)) := by
  induction dates generalizing node s history with
  | nil =>
    simpa only [calendarTail,List.append_nil,lastCalendarDate,canonicalRecordedCalendarSuffix] using
      actual_real_original_boundary_root_history O H D hD sample register gamma common r node hs history
  | cons next later ih =>
    have hm : next ∈ afterDate O.network O.calendar (O.calendar.age node) := by rw [heq]; exact List.mem_cons_self
    obtain ⟨nextNode,rfl⟩ := actual_original_date_has_vertex O next (List.mem_filter.mp hm).1
    have hpair := actual_after_date_head_tail O (O.calendar.age node) (O.calendar.age nextNode) later heq
    have hgap := actual_next_original_date_gap O (O.calendar.age node) (O.calendar.age nextNode) later heq
    let first := boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
      [.interval (Real.toNNReal (O.calendar.age nextNode-O.calendar.age node))]
    let last := boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age nextNode) ++
      calendarTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age nextNode) later
    let view := fun result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy) =>
      withBaseHistory result.2 (canonicalExitProjection O H D hD (O.calendar.age nextNode) [] result.1)
    let suffix := canonicalRecordedCalendarSuffix O H D hD sample gamma common r (O.calendar.age nextNode) later
    have hnext (result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy))
        (hr : result ∈ (originalRootRecordedProgram O r first s history).support) :
        (originalRootRecordedProgram O r last result.1 result.2).map
          (fun final => withBaseHistory final.2 (canonicalDateProjection O D
            (lastCalendarDate (O.calendar.age nextNode) later) final.1)) = asyncProgram suffix (view result) := by
      exact ih nextNode hpair.2
        (actual_adjacent_recorded_block_reaches_real_prefix O H sample register gamma common r node nextNode hpair.1 later heq hs history hr)
        result.2
    have hsplit : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
        calendarTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) (O.calendar.age nextNode::later) =
        first ++ last := by simp only [first,last,calendarTail,List.append_assoc,List.singleton_append]
    rw [hsplit]
    change (originalRootRecordedProgram O r (first ++ last) s history).map
      (fun final => withBaseHistory final.2 (canonicalDateProjection O D
        (lastCalendarDate (O.calendar.age nextNode) later) final.1)) = _
    calc
      _ = (originalRootRecordedProgram O r first s history).bind (fun result => asyncProgram suffix (view result)) := by
        rw [actual_original_root_recorded_append,PMF.map_bind]
        exact bind_eq_of_eq_on_support _ _ _ hnext
      _ = ((originalRootRecordedProgram O r first s history).map view).bind (asyncProgram suffix) := by
        rw [PMF.bind_map]; rfl
      _ = _ := by
        rw [actual_real_original_adjacent_recorded_row O H D hD sample register gamma common r node nextNode hpair.1 hgap hs history]
        exact (async_program_append _ _ _).symm

#print axioms actual_real_whole_original_calendar_suffix_history
end G1CanonicalWholeCalendarRecordedSuffix
