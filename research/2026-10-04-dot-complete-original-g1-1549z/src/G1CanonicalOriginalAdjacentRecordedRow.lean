import G1CanonicalOriginalBoundaryEpochAdmission

/-! An actual full old boundary followed by the actual next old epoch is
bound to one concrete pending runtime block. Every old micro-checkpoint is
retained jointly, and its endpoint has the real initialized support needed
at the next original boundary. -/
namespace G1CanonicalOriginalAdjacentRecordedRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1CanonicalOriginalNodeAsyncBatch G1CanonicalOriginalBoundaryAsyncBatch
open G1CanonicalOriginalExitAsyncStep
open G1CanonicalOriginalEpochAsync G1CanonicalOriginalDateGapRoles G1CanonicalOriginalAdjacentSourceSupport
open G1CanonicalOriginalBoundaryEpochAdmission G1ActualOriginalBoundaryRootHistory
open G1ActualOriginalRootRecordedProgram G1PendingBaseCheckpointRecorder
open G1PendingOriginalRootBlobCheckpointHistory G1PendingActorInterfaceCommutation
open G1ContextualForestReplacement G1SameOriginalExteriorContinuation
open G1ActualJointProgram
open G1InitializedFrontierPrefix G1CanonicalThreeEpochList G1UnrankedSourceView
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalRecordedBoundaryEpochOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (date next : ℝ) :=
  canonicalRecordedBoundaryOps O H D hD sample gamma common r date ++
    recordedBlock (pendingRootBlobObservation O)
      (canonicalEpochAsyncOps O D sample r date (Real.toNNReal (next-date)))

/-- Real source admissions derive the complete consecutive-date joint row,
including all original exit/node checkpoints and exactly one epoch endpoint. -/
theorem actual_real_original_adjacent_recorded_row (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node next : O.Vertex) (hlt : O.calendar.age node < O.calendar.age next)
    (hgap : OriginalDateGap O (O.calendar.age node) (O.calendar.age next)) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
        [.interval (Real.toNNReal (O.calendar.age next - O.calendar.age node))]) s history).map
      (fun result => withBaseHistory result.2 (canonicalExitProjection O H D hD (O.calendar.age next) [] result.1)) =
    asyncProgram (canonicalRecordedBoundaryEpochOps O H D hD sample gamma common r
      (O.calendar.age node) (O.calendar.age next))
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) [] s)) := by
  have hproj := actual_original_gap_same_runtime_projection O H D hD (sample := sample)
    (O.calendar.age node) (O.calendar.age next) hlt hgap
  rw [←hproj]
  let epoch := recordedBlock (pendingRootBlobObservation O)
    (canonicalEpochAsyncOps O D sample r (O.calendar.age node) (Real.toNNReal (O.calendar.age next-O.calendar.age node)))
  let view := fun result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy) =>
    withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age node) result.1)
  have hnext (result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy))
      (hr : result ∈ (originalRootRecordedProgram O r
        (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s history).support) :
      (originalRootRecordedProgram O r [.interval (Real.toNNReal (O.calendar.age next-O.calendar.age node))]
        result.1 result.2).map view = asyncProgram epoch (view result) :=
    actual_real_boundary_output_epoch_history O H D hD sample register gamma common r node _ hs
      (actual_original_root_recorded_support_endpoint O r _ s history hr) result.2
  calc
    _ = (originalRootRecordedProgram O r
        (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s history).bind
        (fun result => asyncProgram epoch (view result)) := by
      rw [actual_original_root_recorded_append,PMF.map_bind]
      exact bind_eq_of_eq_on_support _ _ _ hnext
    _ = ((originalRootRecordedProgram O r
        (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s history).map view).bind
        (asyncProgram epoch) := by rw [PMF.bind_map]; rfl
    _ = _ := by
      rw [actual_real_original_boundary_root_history O H D hD sample register gamma common r node hs history]
      exact (async_program_append _ _ _).symm

lemma actual_adjacent_recorded_block_reaches_real_prefix (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node next : O.Vertex) (hlt : O.calendar.age node < O.calendar.age next)
    (later : List ℝ) (heq : afterDate O.network O.calendar (O.calendar.age node) = O.calendar.age next :: later)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (UnrankedView O.Vertex O.Edge Copy))
    {result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy)}
    (hr : result ∈ (originalRootRecordedProgram O r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
        [.interval (Real.toNNReal (O.calendar.age next-O.calendar.age node))]) s history).support) :
    result.1 ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age next))
      (initialCode O.network sample register)).support := by
  have hp := actual_original_root_recorded_support_endpoint O r _ s history hr
  rw [actual_source_program_append] at hp
  obtain ⟨d,hd,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  exact actual_adjacent_original_epoch_reaches_real_prefix O H sample register gamma common r node next hlt later heq hs hd hz

#print axioms actual_real_original_adjacent_recorded_row
end G1CanonicalOriginalAdjacentRecordedRow
