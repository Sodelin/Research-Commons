import G1ActualSafeOwnInputRetention

/-! The exact OWN final private exit and immediate release interface are
derived in the existing concrete runtime. The root checkpoint is AFTER the
release, even when multiple original cuts have the same calendar date. -/
namespace G1CanonicalOwnClosingRuntimePosition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitCloseReplay G1CanonicalPendingBoundaryMembership
open G1CanonicalOriginalActorOpening G1ActiveCoreBridgeCohorts G1ActualActorOwnedPrivateSyntax
open G1ActualOriginalOpenCloseAsyncInterface G1ActualOriginalUnrankedLocalKernel G1TaggedOriginalCalendar
open G1PendingActorInterfaceCommutation G1PendingBaseCheckpointRecorder G1PendingOriginalRootBlobCheckpointHistory
open G1OriginalClosingRuntimeDecomposition G1OriginalRuntimeCalendarCuts
open G1ActualOriginalExitBatchRootHistory G1ActualOriginalNodeBatchRootHistory
open G1OriginalCalendarDecomposition G1OriginalSpanClosingPhase G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def beforeOwnCutEdges (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :=
  (originalExits O.network O.calendar (O.calendar.age (O.network.graph.source (actorCut O H D hD actor)))).takeWhile
    (fun edge => decide (edge ≠ actorCut O H D hD actor))

theorem actual_own_final_cut_private_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    canonicalExitAsyncOperation O H D hD sample gamma common r
      (O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) (beforeOwnCutEdges O H D hD actor) (actorCut O H D hD actor) =
      AsyncOperation.localStep actor (originalLocalRow O.network sample r
        (originalInsideCopies O sample (actorInput O D actor)) [eraseEvent O H gamma common (.exit (actorCut O H D hD actor))]) := by
  have ho : eventActor O H D hD (.exit (actorCut O H D hD actor)) = some actor :=
    (actual_original_exit_owner_iff_private_region O H D hD actor _).mpr (actual_actor_cut_in_region O H D hD actor)
  have hp : ∀ edge ∈ beforeOwnCutEdges O H D hD actor,
      O.calendar.age (O.network.graph.source edge) = O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) := by
    intro edge hm
    have hm := List.takeWhile_subset _ hm
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
  have hn : actorCut O H D hD actor ∉ beforeOwnCutEdges O H D hD actor := by
    intro hm
    unfold beforeOwnCutEdges at hm
    have hx : actorCut O H D hD actor ≠ actorCut O H D hD actor :=
      of_decide_eq_true (List.mem_takeWhile_imp (p := fun edge : O.Edge => decide (edge ≠ actorCut O H D hD actor)) hm)
    exact hx rfl
  have ha : actor ∈ canonicalExitActors O H D hD (O.calendar.age (O.network.graph.source (actorCut O H D hD actor)))
      (beforeOwnCutEdges O H D hD actor) := Finset.mem_toList.mpr
    (actual_original_owned_exit_is_pending O H D hD _ _ _ hp rfl hn actor ho)
  simp only [canonicalExitAsyncOperation,ho,originalPendingSlots,if_pos ha]

/-- The actual final cut row, OWN release, and post-release root recording
are three literal concrete operations. The cache is released before observing
the original root-containing population; no timing/order oracle is supplied. -/
theorem actual_own_recorded_cut_release_position (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    recordedBlock (pendingRootBlobObservation O)
      (canonicalRuntimeExitOps O H D hD sample gamma common r
        (O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) (beforeOwnCutEdges O H D hD actor) (actorCut O H D hD actor)) =
    [historyLift (AsyncOperation.localStep actor (originalLocalRow O.network sample r
       (originalInsideCopies O sample (actorInput O D actor)) [eraseEvent O H gamma common (.exit (actorCut O H D hD actor))])),
     historyLift (AsyncOperation.interface actor (originalCloseKernel (originalInsideCopies O sample (actorInput O D actor)))),
     recordBaseCheckpoint (pendingRootBlobObservation O)] := by
  rw [canonicalRuntimeExitOps,actual_cut_closes_actor,actual_own_final_cut_private_kernel]
  rfl

/-- Literal phase prefix followed by the actual final private cut, immediate
OWN close and root checkpoint. This is the source-derived closing barrier
needed by full private-block promotion. -/
theorem actual_own_closing_phase_last_block (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    closingRuntimePhase O H D hD sample gamma common r (actorInput O D actor)
      (D.vertex (T.network.graph.source actor.val)) (actorCut O H D hD actor) =
    (canonicalRecordedNodeBatchOps O H D hD sample gamma common r
       (Finset.univ.filter (fun node : O.Vertex => O.calendar.age node = O.calendar.age (actorInput O D actor))).toList ++
     stoppedRuntimeTail O H D hD sample gamma common r (O.calendar.age (D.vertex (T.network.graph.source actor.val)))
       (O.calendar.age (actorInput O D actor))
       (G1CanonicalThreeEpochList.afterDate O.network O.calendar (O.calendar.age (actorInput O D actor))) ++
     canonicalRecordedExitBatchOps O H D hD sample gamma common r
       (O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) [] (beforeOwnCutEdges O H D hD actor)) ++
     recordedBlock (pendingRootBlobObservation O)
       (canonicalRuntimeExitOps O H D hD sample gamma common r
         (O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) (beforeOwnCutEdges O H D hD actor) (actorCut O H D hD actor)) := by
  unfold closingRuntimePhase closingExits
  rw [←actual_actor_cut_source O H D hD actor]
  rw [actual_recorded_exit_batch_split]
  simp only [canonicalRecordedExitBatchOps,List.nil_append,List.append_nil,List.append_assoc,beforeOwnCutEdges]

#print axioms actual_own_recorded_cut_release_position
#print axioms actual_own_closing_phase_last_block
end G1CanonicalOwnClosingRuntimePosition
