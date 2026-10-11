import G1PendingBaseCheckpointRecorder

/-! Actual old exit micro-checkpoints bind to the pending history recorder.
The genuine source exit occurs first, its possible own cut is closed, and
only then its whole original root-blob/ancestral checkpoint is appended. -/
namespace G1ActualOriginalExitRootCheckpoint
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitCloseReplay G1CanonicalOriginalExitAsyncBatch
open G1CanonicalPartialBatchRootObserver G1ActualRootBlobPopulationFootprint G1PendingOriginalRootBlobCheckpointHistory
open G1PendingBaseCheckpointRecorder G1PendingActorInterfaceCommutation G1InitializedFrontierPrefix
open G1OriginalWholeCausalView G1ContextualForestReplacement
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Genuine original source exit→immediate source-derived close→recording of
its full old root-blob view. This preserves an arbitrary prior history list,
SAME whole register and all runtime coordinates jointly. -/
theorem actual_real_original_exit_root_checkpoint (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) (processed : List O.Edge) (edge : O.Edge)
    (hprocessed : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = O.calendar.age node)
    (hdate : O.calendar.age (O.network.graph.source edge) = O.calendar.age node) (hnew : edge ∉ processed)
    {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (s : Code O.network sample)
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (sourceProgram O.network r [.boundary (.exit edge)] s).map (fun d =>
      withBaseHistory (history ++ [originalRootBlobView O.network (wholeOriginalView O.network d)])
        (canonicalExitProjection O H D hD (O.calendar.age node) (processed ++ [edge]) d)) =
    asyncProgram (recordedBlock (pendingRootBlobObservation O)
      (canonicalRuntimeExitOps O H D hD sample gamma common r (O.calendar.age node) processed edge))
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) processed s)) := by
  let output := canonicalExitProjection O H D hD (sample := sample) (O.calendar.age node) (processed ++ [edge])
  calc
    _ = (sourceProgram O.network r [.boundary (.exit edge)] s).map (fun d =>
        withBaseHistory (history ++ [pendingRootBlobObservation O (output d).1]) (output d)) := by
      apply map_eq_of_eq_on_support
      intro d hd
      have hp' := actual_exit_prefix_support_append O r processed edge initial s d hp hd
      rw [actual_real_partial_exit_root_observer O H D hD sample register gamma common r node hs (processed ++ [edge]) hp']
    _ = ((sourceProgram O.network r [.boundary (.exit edge)] s).map output).map (fun next =>
        withBaseHistory (history ++ [pendingRootBlobObservation O next.1]) next) := by rw [PMF.map_comp]; rfl
    _ = _ := by
      have hrow := actual_real_original_exit_close_replay O H D hD sample register gamma common r node processed edge
        hprocessed hdate hnew hs hp
      simp only [G1TaggedOriginalCalendar.eraseEvent] at hrow
      dsimp only [output]
      rw [hrow]
      exact actual_recorded_block_row _ _ _ _

#print axioms actual_real_original_exit_root_checkpoint
end G1ActualOriginalExitRootCheckpoint
