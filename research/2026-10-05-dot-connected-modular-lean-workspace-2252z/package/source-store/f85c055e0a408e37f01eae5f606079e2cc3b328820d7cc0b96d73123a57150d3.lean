import G1CanonicalOriginalEpochAsync
import G1ActualOriginalBoundaryRootHistory

/-! The actual ORIGINAL epoch records exactly one original post-epoch root
checkpoint after all actor/base draws. Artificial tensor serialization steps
add no observations. Every original root/ancestral subtree and SAME register
remain joint with the complete old causal runtime coordinates and history. -/
namespace G1CanonicalOriginalEpochRootHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1CanonicalComponentSegment G1InitializedFrontierPrefix G1UnrankedSourceView
open G1OriginalWholeCausalView G1ActualRootBlobPopulationFootprint
open G1CanonicalOriginalNodeAsyncBatch G1CanonicalOriginalEpochAsync
open G1CanonicalPartialBatchRootObserver G1PendingOriginalRootBlobCheckpointHistory
open G1ActualOriginalRootRecordedProgram G1PendingBaseCheckpointRecorder
open G1PendingActorInterfaceCommutation G1ContextualForestReplacement
open G1SameOriginalExteriorContinuation
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

/-- Genuine source/calendar epoch execution retains every original root
checkpoint, not just an endpoint surrogate. Its source/root admissions are
derived from the SAME real initialized original frontier and node batch. -/
theorem actual_real_original_epoch_root_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node : O.Vertex) (duration : ℝ≥0) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) (initialCode O.network sample register)).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r
      (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) s).support)
    (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r [.interval duration] d history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age node) result.1)) =
      asyncProgram (recordedBlock (pendingRootBlobObservation O)
        (canonicalEpochAsyncOps O D sample r (O.calendar.age node) duration))
        (withBaseHistory history (canonicalDateProjection O D (O.calendar.age node) d)) := by
  let projection := canonicalDateProjection O D (sample := sample) (O.calendar.age node)
  have hobs (z : Code O.network sample) (hz : z ∈ (sourceProgram O.network r [.interval duration] d).support) :
      originalRootBlobView O.network (wholeOriginalView O.network z) = pendingRootBlobObservation O (projection z).1 := by
    apply actual_real_partial_nodes_epoch_root_observer O H D hD sample register gamma common r node hs
      ((Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = O.calendar.age node)).toList) duration
    rw [actual_source_program_append]
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    exact ⟨d,hd,hz⟩
  have hsingle : originalRootRecordedProgram O r [.interval duration] d history =
      (sourceProgram O.network r [.interval duration] d).map
        (fun z => (z,history ++ [originalRootBlobView O.network (wholeOriginalView O.network z)])) := by
    simp only [originalRootRecordedProgram,sourceProgram,PMF.bind_pure,PMF.map,Function.comp_def]
  rw [hsingle,PMF.map_comp]
  calc
    _ = (sourceProgram O.network r [.interval duration] d).map (fun z =>
        withBaseHistory (history ++ [pendingRootBlobObservation O (projection z).1]) (projection z)) := by
      apply map_eq_of_eq_on_support
      intro z hz
      simp only [Function.comp_def,hobs z hz,projection]
    _ = ((sourceProgram O.network r [.interval duration] d).map projection).map
        (fun next => withBaseHistory (history ++ [pendingRootBlobObservation O next.1]) next) := by
      rw [PMF.map_comp]
      rfl
    _ = (asyncProgram (canonicalEpochAsyncOps O D sample r (O.calendar.age node) duration) (projection d)).map
        (fun next => withBaseHistory (history ++ [pendingRootBlobObservation O next.1]) next) := by
      rw [actual_real_original_post_node_epoch_async O H D hD sample register gamma common r node duration hs hd]
    _ = _ := actual_recorded_block_row (pendingRootBlobObservation O) _ history (projection d)

#print axioms actual_real_original_epoch_root_history
end G1CanonicalOriginalEpochRootHistory
