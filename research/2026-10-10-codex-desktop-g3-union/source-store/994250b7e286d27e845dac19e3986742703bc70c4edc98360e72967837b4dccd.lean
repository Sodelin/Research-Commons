import G1CanonicalOwnEntryCoordinateAdmission

/-! Actual entire original runtime split at ONE actor's OWN two interfaces.
Every part is computed from existing original compiler operations and dates.
This is the concrete list admission for interface-delimited K promotion. -/
namespace G1CanonicalOwnTwoInterfaceRuntime
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalOpeningAsyncBatch G1CanonicalOwnOpeningRuntimePosition
open G1ActualOriginalExitBatchRootHistory G1ActualOriginalNodeBatchRootHistory
open G1ActualOriginalOpenCloseAsyncInterface G1ActiveCoreBridgeCohorts G1CanonicalFiniteActiveEpochAdmission
open G1CanonicalInitializedWholeCalendarHistory G1OriginalRuntimeCalendarCuts G1OriginalClosingRuntimeDecomposition
open G1CanonicalOwnClosingRuntimePosition G1OriginalSpanCalendarDecomposition G1OriginalDecoratedSpan
open G1ActualOriginalUnrankedLocalKernel G1TaggedOriginalCalendar
open G1PendingActorInterfaceCommutation G1PendingBaseCheckpointRecorder G1PendingOriginalRootBlobCheckpointHistory
open G1OriginalCalendarDecomposition G1CanonicalThreeEpochList G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

structure OwnRuntimeParts (I S Base : Type*) where
  before : List (AsyncOperation I S Base)
  opening : AsyncOperation I S Base
  interior : List (AsyncOperation I S Base)
  closing : AsyncOperation I S Base
  future : List (AsyncOperation I S Base)

noncomputable def ownRuntimeParts (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    OwnRuntimeParts (BridgeActor T) (UnrankedView O.Vertex O.Edge Copy)
      (UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) :=
  let date := O.calendar.age (actorInput O D actor)
  let upper := O.calendar.age (O.network.graph.source (actorCut O H D hD actor))
  let actors := canonicalExitActors O H D hD date (originalExits O.network O.calendar date)
  let beforeOpeners := sourceOpenPrefix O H D hD actor
  let suffix := sourceOpenSuffix O H D hD actor
  { before := beforeRuntimeBoundary O H D hD sample gamma common r date ++
      canonicalRecordedExitBatchOps O H D hD sample gamma common r date [] (originalExits O.network O.calendar date) ++
      (canonicalOpeningBatchOps O D sample actors beforeOpeners).map historyLift
    opening := historyLift (.interface actor (originalOpenKernel (originalInsideCopies O sample (actorInput O D actor))
      (activeOriginalBase O D sample (actors ++ beforeOpeners))))
    interior := (canonicalOpeningBatchOps O D sample ((actors ++ beforeOpeners) ++ [actor]) suffix).map historyLift ++
      canonicalRecordedNodeBatchOps O H D hD sample gamma common r
        (Finset.univ.filter (fun node : O.Vertex => O.calendar.age node = date)).toList ++
      stoppedRuntimeTail O H D hD sample gamma common r upper date (afterDate O.network O.calendar date) ++
      canonicalRecordedExitBatchOps O H D hD sample gamma common r upper [] (beforeOwnCutEdges O H D hD actor) ++
      [historyLift (.localStep actor (originalLocalRow O.network sample r
        (originalInsideCopies O sample (actorInput O D actor)) [eraseEvent O H gamma common (.exit (actorCut O H D hD actor))]))]
    closing := historyLift (.interface actor (originalCloseKernel (originalInsideCopies O sample (actorInput O D actor))))
    future := [recordBaseCheckpoint (pendingRootBlobObservation O)] ++ closingRuntimeFuture O H D hD sample gamma common r (actorCut O H D hD actor) }

/-- Entire concrete runtime has these OWN open/interior/release positions.
The split is derived from the unchanged original graph/calendar/site lists;
it is not a supplied trace, desired kernel identity or output equality. -/
theorem actual_entire_original_runtime_two_interface_split (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    canonicalRecordedWholeCalendarOps O H D hD sample gamma common r =
      (ownRuntimeParts O H D hD sample gamma common r actor).before ++
      [(ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
      (ownRuntimeParts O H D hD sample gamma common r actor).interior ++
      [(ownRuntimeParts O H D hD sample gamma common r actor).closing] ++
      (ownRuntimeParts O H D hD sample gamma common r actor).future := by
  rw [actual_original_closing_runtime_decomposition O H D hD sample gamma common r
    (actorInput O D actor) (D.vertex (T.network.graph.source actor.val)) (actorCut O H D hD actor)
    (actual_actor_cut_source O H D hD actor)
    (actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)),
    actual_own_closing_phase_last_block,actual_own_recorded_cut_release_position]
  unfold openingRuntimeFrontier
  rw [actual_own_original_opening_runtime_cut O H D hD sample actor]
  simp only [ownRuntimeParts,actual_actor_cut_source,List.map_append,List.map_singleton,List.map_cons,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]

#print axioms actual_entire_original_runtime_two_interface_split
end G1CanonicalOwnTwoInterfaceRuntime
