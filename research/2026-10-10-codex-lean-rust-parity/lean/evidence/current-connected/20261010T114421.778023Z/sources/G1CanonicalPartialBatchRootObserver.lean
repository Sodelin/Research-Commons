import G1WholeFinitePendingPromotion
import G1PendingOriginalRootBlobCheckpointHistory

/-! Root-blob observer admission at EVERY actual partial old exit/node batch.
The observer sees base only; a processed final cut has already promoted its
actor cohort into that base. No future cached K output is observed early. -/
namespace G1CanonicalPartialBatchRootObserver
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalFiniteActiveEpochAdmission G1ActiveCoreBridgeCohorts G1CanonicalOriginalExitAsyncStep
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalNodeAsyncBatch G1ActualBeforeExitActorSupport
open G1ActualRootBlobBaseObserver G1ActualRootBlobPopulationFootprint G1PendingOriginalRootBlobCheckpointHistory
open G1NaturalActiveActorFrontier G1InitializedFrontierPrefix G1OriginalWholeCausalView G1TaggedOriginalCalendar
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

/-- Exact source-derived original root observation after ANY actual partial
exit batch, including final cuts into the root blob and coincident closings.
Its current role set has removed every processed own cut. -/
theorem actual_real_partial_exit_root_observer (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (processed : List O.Edge) {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support) :
    originalRootBlobView O.network (wholeOriginalView O.network d) =
      pendingRootBlobObservation O (canonicalExitProjection O H D hD (O.calendar.age node) processed d).1 := by
  apply actual_original_root_blob_view_from_active_base O H D hD
    (canonicalExitActors O H D hD (O.calendar.age node) processed) d
  intro actor hm
  have ha := Finset.mem_filter.mp (Finset.mem_toList.mp hm)
  have hb := (Finset.mem_filter.mp ha.1).2
  exact actual_real_partial_exit_batch_actor_region O H D hD actor node
    (by simpa only [actorInput,D.calendar] using hb.1)
    (by simpa only [D.calendar] using hb.2)
    sample register gamma common r hs processed ha.2 hd

/-- EVERY source-supported partial original node batch, followed by any
partial original epoch duration, has its full old root-blob/ancestral view in
base. Thus observer admission is not restricted to date endpoints. -/
theorem actual_real_partial_nodes_epoch_root_observer (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (nodes : List O.Vertex) (duration : ℝ≥0) {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r
      (nodes.map (fun v => eraseEvent O H gamma common (.node v)) ++ [.interval duration]) initial).support) :
    originalRootBlobView O.network (wholeOriginalView O.network d) =
      pendingRootBlobObservation O (canonicalDateProjection O D (O.calendar.age node) d).1 := by
  apply actual_original_root_blob_view_from_active_base O H D hD (canonicalDateActors T (O.calendar.age node)) d
  intro actor hm
  have ha := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
  apply actual_safe_program_actor_region O H D hD actor gamma common r _ _ initial _
    (actual_real_frontier_active_actor_region O H D hD actor node ha sample register gamma common r hs) hd
  intro op hop
  rcases List.mem_append.mp hop with hnodes | htime
  · obtain ⟨v,hv,he⟩ := List.mem_map.mp hnodes
    exact Or.inr (Or.inr ⟨v,he.symm⟩)
  · have he : op = .interval duration := by simpa using htime
    exact Or.inl ⟨duration,he⟩

#print axioms actual_real_partial_exit_root_observer
#print axioms actual_real_partial_nodes_epoch_root_observer
end G1CanonicalPartialBatchRootObserver
