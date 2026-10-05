import G1ExactPromotionInterfaceRecordLift

/-! The same all-original-bridge K-labelled interpreter jointly carries
EVERY genuine interface-output record. This closes the recorder/label
compatibility gate; real observed source-entry trace admission is separate. -/
namespace G1AllOriginalKLabelsWithEntryRecords
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalOwnTwoInterfaceRuntime
open G1CanonicalPendingTrueKExposure G1CanonicalInitializedWholeCalendarHistory
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1OwnProtocolSignatureTransport G1AllOriginalPromotedKLabels G1PendingBaseCheckpointRecorder
open G1PendingInterfaceEntryRecorder G1ExactPromotionInterfaceRecordLift G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- EVERY original actor retains its single TRUE source K row and real
own-interface functions in the interpreter which records all interface
outputs JOINTLY with the complete retained original base history. -/
theorem actual_all_original_K_labels_and_interface_records (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) :
    ∃ left right,
      (left = [] ∨ left = [.localStep actor (actorWordKernel [])]) ∧
      (right = [] ∨ right = [.localStep actor (actorWordKernel [])]) ∧
      ownProtocolSignature actor (promoteEveryActor (Finset.univ.toList)
        ((canonicalRecordedWholeCalendarOps O H D hD sample gamma common r).map interfaceRecordingLift)) =
        left ++ [interfaceRecordingLift (ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
        [.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor)] ++
        [interfaceRecordingLift (ownRuntimeParts O H D hD sample gamma common r actor).closing] ++ right := by
  obtain ⟨left,right,hl,hr,hs⟩ := actual_all_original_bridge_K_labels O H D hD sample gamma common r actor
  refine ⟨left.map interfaceRecordingLift,right.map interfaceRecordingLift,?_,?_,?_⟩
  · rcases hl with he | he
    · left; simp [he]
    · right; simp [he,interfaceRecordingLift]
  · rcases hr with he | he
    · left; simp [he]
    · right; simp [he,interfaceRecordingLift]
  · rw [actual_every_actor_promotion_record_lift,recorded_signature,hs]
    simp only [List.map_append,List.map_singleton,interfaceRecordingLift]

/-- The observed interface records are retained jointly for any SAME
continuation, not reconstructed from endpoint marginal laws. A source-law
observed-entry interpretation must still derive its actual input support. -/
theorem actual_original_recorded_K_interpreter_same_future (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    {Result : Type*}
    (initial : ((UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
      List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy))
    (future : ((UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
      List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy) → PMF Result) :
    (asyncProgram ((canonicalRecordedWholeCalendarOps O H D hD sample gamma common r).map interfaceRecordingLift) initial).bind future =
    (asyncProgram (promoteEveryActor (Finset.univ.toList)
      ((canonicalRecordedWholeCalendarOps O H D hD sample gamma common r).map interfaceRecordingLift)) initial).bind future := by
  rw [actual_every_actor_promotion_row]

#print axioms actual_all_original_K_labels_and_interface_records
end G1AllOriginalKLabelsWithEntryRecords
