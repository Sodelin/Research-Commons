import G1ActualFiniteOriginalEpochAsync
import G1CanonicalOriginalNodeAsyncBatch
import G1CanonicalWholeOriginalActiveEpoch

/-! Each actual original epoch is compiled into all active actor rows and
the actual base row, on complete ORIGINAL unranked coordinates. Canonical
physical separation is DERIVED from the actual active regions; the real
initialized post-node frontier discharges those regions. Arbitrarily many
overlapping/coincident actors are allowed, including an empty actor family. -/
namespace G1CanonicalOriginalEpochAsync
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompatibility
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1ActiveCoreBridgeCohorts G1CanonicalActorLifecycleCompiler
open G1OriginalActorOperationOwnership G1OriginalNodeBatchBinding G1CanonicalComponentSegment
open G1CanonicalPendingActorSets G1CanonicalOriginalActorOpening G1CanonicalOriginalNodeAsyncStep
open G1CanonicalOriginalNodeAsyncBatch G1CanonicalFiniteActiveEpochAdmission
open G1CanonicalWholeOriginalActiveEpoch G1ActualOriginalPrivateAsyncStep
open G1ActualOriginalUnrankedLocalKernel G1ActualFiniteOriginalEpochAsync
open G1PendingActorInterfaceCommutation G1ActualFinitePanelProgramTensor
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalEpochAsyncOps (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (r : PositivePairRates O.Edge) (date : ℝ) (duration : ℝ≥0) :=
  let actors := canonicalDateActors T date
  let slots := originalPendingSlots O D sample actors
  actors.map (fun actor => AsyncOperation.localStep actor
      (originalLocalRow O.network sample r (slots actor) [.interval duration])) ++
    [AsyncOperation.exterior
      (originalLocalRow O.network sample r (activeOriginalBase O D sample actors) [.interval duration])]

lemma actual_pending_slots_panel_list (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (actors : List (BridgeActor T)) :
    actors.map (originalPendingSlots O D sample actors) = activeOriginalPanels O D sample actors := by
  unfold activeOriginalPanels
  apply List.map_congr_left
  intro actor hm
  simp only [originalPendingSlots,if_pos hm]

/-- Canonical physical regions derive the ACTUAL source-to-async epoch row;
there is no supplied separator, independence equality, or desired K row. -/
theorem actual_canonical_original_epoch_async_from_region (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (node : O.Vertex) (duration : ℝ≥0) (s : Code O.network sample)
    (hregion : DateActorRegion O D (O.calendar.age node) s) :
    (sourceProgram O.network r [.interval duration] s).map
      (canonicalDateProjection O D (O.calendar.age node)) =
      asyncProgram (canonicalEpochAsyncOps O D sample r (O.calendar.age node) duration)
        (canonicalDateProjection O D (O.calendar.age node) s) := by
  let actors := canonicalDateActors T (O.calendar.age node)
  have hn : actors.Nodup := Finset.nodup_toList _
  have ha : ∀ actor ∈ actors, T.calendar.Active (O.calendar.age node) actor.val := by
    intro actor hm
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
  have hsep : PanelSeparatedAgenda O.network r [.interval duration]
      (actors.map (originalPendingSlots O D sample actors) ++ [activeOriginalBase O D sample actors]) s := by
    rw [actual_pending_slots_panel_list]
    exact actual_finite_active_regions_epoch_admission O H D hD actors hn node ha sample r duration s hregion
  have law := actual_finite_original_source_async_program O.network r [.interval duration] s
    (activeOriginalBase O D sample actors) (originalPendingSlots O D sample actors) actors hn
    (fun actor hm => by simp only [originalPendingSlots,if_neg hm]) hsep
  unfold canonicalDateProjection originalAsyncProjection canonicalEpochAsyncOps
  simpa only [finiteOriginalAsyncCoordinates,actors] using law

/-- At every REAL initialized original post-node frontier all epoch
admissions are derived. This is a source/calendar compiler theorem, not a
conditional supplied product or a two/three-actor surrogate. -/
theorem actual_real_original_post_node_epoch_async (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node : O.Vertex) (duration : ℝ≥0) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (G1InitializedFrontierPrefix.actualFrontierProgram O.network O.calendar H
        (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r
      (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) s).support) :
    (sourceProgram O.network r [.interval duration] d).map
      (canonicalDateProjection O D (O.calendar.age node)) =
      asyncProgram (canonicalEpochAsyncOps O D sample r (O.calendar.age node) duration)
        (canonicalDateProjection O D (O.calendar.age node) d) := by
  apply actual_canonical_original_epoch_async_from_region O H D hD r node duration d
  intro actor hm
  have ha : T.calendar.Active (O.calendar.age node) actor.val :=
    (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
  exact actual_real_post_node_active_actor_region O H D hD actor node ha
    sample register gamma common r hs hd

#print axioms actual_real_original_post_node_epoch_async
end G1CanonicalOriginalEpochAsync
