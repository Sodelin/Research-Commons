import G1ActualRootBlobBaseObserver

/-! Concrete pending root-blob readout: only the CURRENT ORIGINAL base
coordinate is an input. Every fixed original checkpoint is source-bound;
unreleased private K outputs are never observed early. Physical close/base
promotion must precede a post-final-cut root checkpoint when necessary. -/
namespace G1PendingOriginalRootBlobCheckpointHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceInitializedCalendar
open G1UnrankedSourceView G1OriginalWholeCausalView G1ActualGraphNormalization
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1OriginalSpanRegion
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler
open G1NaturalActiveActorFrontier G1CanonicalWholeOriginalActiveEpoch G1CanonicalFiniteActiveEpochAdmission
open G1ActualRootBlobPopulationFootprint G1ActualRootBlobBaseObserver
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def pendingRootBlobObservation (O : Source.{u,v,w} X) {Copy : Type*}
    (base : UnrankedView O.Vertex O.Edge Copy) : UnrankedView O.Vertex O.Edge Copy :=
  originalRootBlobView O.network base

/-- On ANY actual canonical before-node frontier, all active cohorts are
off the whole root blob. The full original root observer is exactly base. -/
theorem actual_canonical_frontier_root_blob_observer_from_base (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actors : List (BridgeActor T)) (node : O.Vertex)
    (hactive : ∀ actor ∈ actors, T.calendar.Active (O.calendar.age node) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (G1InitializedFrontierPrefix.actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) (initialCode O.network sample register)).support) :
    originalRootBlobView O.network (wholeOriginalView O.network s) =
      pendingRootBlobObservation O (unrankedView (selectedView (state s) (activeOriginalBase O D sample actors))) := by
  apply actual_original_root_blob_view_from_active_base O H D hD actors s
  intro actor ha
  exact actual_real_frontier_active_actor_region O H D hD actor node (hactive actor ha)
    sample register gamma common r hs

theorem actual_post_node_root_blob_observer_from_base (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actors : List (BridgeActor T)) (node : O.Vertex)
    (hactive : ∀ actor ∈ actors, T.calendar.Active (O.calendar.age node) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (G1InitializedFrontierPrefix.actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) (initialCode O.network sample register)).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r
      (G1CanonicalComponentSegment.nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) s).support) :
    originalRootBlobView O.network (wholeOriginalView O.network d) =
      pendingRootBlobObservation O (unrankedView (selectedView (state d) (activeOriginalBase O D sample actors))) := by
  apply actual_original_root_blob_view_from_active_base O H D hD actors d
  intro actor ha
  exact actual_real_post_node_active_actor_region O H D hD actor node (hactive actor ha)
    sample register gamma common r hs hd

noncomputable def actualOriginalRootBlobCheckpointHistory (O : Source.{u,v,w} X) {T : Source X}
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (frames : List (List (BridgeActor T) × Code O.network sample)) :=
  frames.map (fun frame => originalRootBlobView O.network (wholeOriginalView O.network frame.2))

noncomputable def pendingBaseRootBlobCheckpointHistory (O : Source.{u,v,w} X) {T : Source X}
    (D : Decoration O T) {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (frames : List (List (BridgeActor T) × Code O.network sample)) :=
  frames.map (fun frame => pendingRootBlobObservation O
    (unrankedView (selectedView (state frame.2) (activeOriginalBase O D sample frame.1))))

/-- JOINT pointwise equality at EVERY fixed original checkpoint, preserving
all old root-blob/ancestral clades, populations and the SAME entire register.
Global execution must derive each frame's actual current-region admission. -/
theorem actual_every_original_root_blob_checkpoint_is_pending_base (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (frames : List (List (BridgeActor T) × Code O.network sample))
    (hregion : ∀ frame ∈ frames, ∀ actor ∈ frame.1,
      ∀ x ∈ G1ActiveCoreBridgeCohorts.originalInsideCopies O sample (actorInput O D actor),
        SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state frame.2) x)) :
    actualOriginalRootBlobCheckpointHistory O frames = pendingBaseRootBlobCheckpointHistory O D frames := by
  apply List.map_congr_left
  intro frame hm
  exact actual_original_root_blob_view_from_active_base O H D hD frame.1 frame.2 (hregion frame hm)

#print axioms actual_canonical_frontier_root_blob_observer_from_base
#print axioms actual_post_node_root_blob_observer_from_base
#print axioms actual_every_original_root_blob_checkpoint_is_pending_base
end G1PendingOriginalRootBlobCheckpointHistory
