import G1CanonicalOriginalEpochRootHistory
import G1CanonicalOriginalAdjacentSourceSupport

/-! Literal boundary-to-epoch admission on the actual initialized ORIGINAL
source. The node/frontier hypotheses of the epoch theorem follow from the
actual whole boundary support; no runtime trace or source-law equality is
supplied. -/
namespace G1CanonicalOriginalBoundaryEpochAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1CanonicalComponentSegment G1InitializedFrontierPrefix G1OriginalCalendarDecomposition
open G1CanonicalThreeEpochList G1CanonicalOriginalDateGapRoles G1CanonicalOriginalAdjacentSourceSupport
open G1CanonicalOriginalBoundaryAsyncBatch G1CanonicalOriginalEpochAsync
open G1CanonicalOriginalEpochRootHistory G1ActualOriginalBoundaryRootHistory
open G1ActualOriginalRootRecordedProgram G1PendingBaseCheckpointRecorder
open G1UnrankedSourceView
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_original_date_has_vertex (O : Source.{u,v,w} X) (date : ℝ)
    (hm : date ∈ sortedOriginalDates O.network O.calendar) : ∃ node : O.Vertex, O.calendar.age node = date := by
  rw [sortedOriginalDates,Finset.mem_sort] at hm
  obtain ⟨node,_,he⟩ := Finset.mem_image.mp hm
  exact ⟨node,he⟩

lemma actual_after_date_head_tail (O : Source.{u,v,w} X) (date next : ℝ) (later : List ℝ)
    (heq : afterDate O.network O.calendar date = next :: later) :
    date < next ∧ afterDate O.network O.calendar next = later := by
  have hm : next ∈ afterDate O.network O.calendar date := by rw [heq]; exact List.mem_cons_self
  have hp := original_after_ordered O.network O.calendar date
  rw [heq] at hp
  have hlt : date < next := (List.mem_filter.mp hm).2 |> of_decide_eq_true
  refine ⟨hlt,?_⟩
  have hf := filter_after_filter hlt (sortedOriginalDates O.network O.calendar)
  change (afterDate O.network O.calendar date).filter (fun c => decide (next < c)) =
    afterDate O.network O.calendar next at hf
  rw [heq,filter_after_head (List.pairwise_cons.mp hp).1] at hf
  exact hf.symm

/-- The actual full original boundary establishes precisely the independently
proved post-node epoch/history admission. -/
theorem actual_real_boundary_output_epoch_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node : O.Vertex) (duration : ℝ≥0) {s d : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (hd : d ∈ (sourceProgram O.network r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s).support)
    (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r [.interval duration] d history).map
      (fun result => withBaseHistory result.2 (G1CanonicalOriginalNodeAsyncBatch.canonicalDateProjection O D (O.calendar.age node) result.1)) =
      G1PendingActorInterfaceCommutation.asyncProgram
        (recordedBlock (G1PendingOriginalRootBlobCheckpointHistory.pendingRootBlobObservation O)
          (canonicalEpochAsyncOps O D sample r (O.calendar.age node) duration))
        (withBaseHistory history (G1CanonicalOriginalNodeAsyncBatch.canonicalDateProjection O D (O.calendar.age node) d)) := by
  have heq : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) =
      (originalExits O.network O.calendar (O.calendar.age node)).map (fun e => ProgramStep.boundary (.exit e)) ++
      nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) := rfl
  rw [heq,G1SameOriginalExteriorContinuation.actual_source_program_append] at hd
  obtain ⟨front,hfront,hnodes⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_real_original_epoch_root_history O H D hD sample register gamma common r node duration
    (actual_real_after_exits_frontier_support O H sample register gamma common r _ hs hfront) hnodes history

#print axioms actual_real_boundary_output_epoch_history
end G1CanonicalOriginalBoundaryEpochAdmission
