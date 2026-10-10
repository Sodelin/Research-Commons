import G1CanonicalOutsidePrivateKernelExclusion

/-! The actual two-interface interior carries the ENTIRE original private
word: no own private kernel lies in the derived before/future pieces. This
binds the finite pending fusion's word to TRUE current-root OriginalSpan K. -/
namespace G1CanonicalOwnInteriorPrivateWord
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1CanonicalOwnTwoInterfaceRuntime G1CanonicalOutsidePrivateKernelExclusion
open G1CanonicalBoundaryPrivateWordBinding G1CanonicalActorKernelSourceBindings
open G1OriginalClosingRuntimeDecomposition G1CanonicalOwnClosingRuntimePosition
open G1CanonicalOriginalOpeningAsyncBatch G1CanonicalOriginalExitAsyncStep
open G1ActualOriginalExitBatchRootHistory G1ActualOriginalNodeBatchRootHistory
open G1OriginalPrivateFutureExclusion G1OriginalActorTemporalFootprint G1OriginalSpanRegion
open G1OriginalRuntimeCalendarCuts G1OriginalCalendarDecomposition G1CanonicalThreeEpochList
open G1PendingBaseCheckpointRecorder G1FinitePendingActorPromotion G1UnrankedSourceView
open G1WholeCanonicalPrivateWordTrueK G1CanonicalInitializedWholeCalendarHistory
open G1CanonicalOriginalKOnlyActorRow G1ActiveCoreBridgeCohorts G1InitializedFrontierPrefix
open G1TaggedOriginalCalendar
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_unowned_recorded_exits_no_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) (processed edges : List O.Edge)
    (hp : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = date)
    (hd : ∀ e ∈ edges, O.calendar.age (O.network.graph.source e) = date)
    (hn : (processed ++ edges).Nodup) (ho : ∀ e ∈ edges, eventActor O H D hD (.exit e) ≠ some actor) :
    ownerKernels actor (canonicalRecordedExitBatchOps O H D hD sample gamma common r date processed edges) = [] := by
  rw [actual_recorded_exits_private_kernel_word O H D hD sample gamma common r actor date processed edges hp hd hn]
  apply List.flatMap_eq_nil_iff.mpr
  intro edge hm
  rw [if_neg (ho edge hm)]

theorem actual_own_before_piece_has_no_private_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ownerKernels actor (ownRuntimeParts O H D hD sample gamma common r actor).before = [] := by
  unfold ownRuntimeParts
  rw [owner_kernels_append,owner_kernels_append,actual_before_own_date_has_no_own_kernel,
    owner_kernels_history_lift,owner_kernels_opening_batch]
  have hnone : ∀ edge ∈ originalExits O.network O.calendar (O.calendar.age (actorInput O D actor)),
      eventActor O H D hD (.exit edge) ≠ some actor := by
    intro edge hm ho
    have ht := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
    have hlt := (actual_span_exit_temporal_bounds O _ edge (actual_owned_exit_member O H D hD edge actor ho)).1
    rw [ht] at hlt
    exact (lt_irrefl _) hlt
  rw [actual_unowned_recorded_exits_no_kernel O H D hD sample gamma common r actor (O.calendar.age (actorInput O D actor)) []
    (originalExits O.network O.calendar (O.calendar.age (actorInput O D actor)))
    (fun _ hm => by cases hm) (fun e hm => (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2)
    (by simp only [List.nil_append,originalExits]; exact Finset.nodup_toList _) hnone]
  rfl

theorem actual_own_future_piece_has_no_private_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ownerKernels actor (ownRuntimeParts O H D hD sample gamma common r actor).future = [] := by
  let cut := actorCut O H D hD actor
  let date := O.calendar.age (O.network.graph.source cut)
  let exits := originalExits O.network O.calendar date
  let remaining := (exits.dropWhile (fun e => decide (e ≠ cut))).tail
  have hdate (edge : O.Edge) (hm : edge ∈ exits) : O.calendar.age (O.network.graph.source edge) = date :=
    (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
  have hremaining (edge : O.Edge) (hm : edge ∈ remaining) : edge ∈ exits :=
    List.dropWhile_subset _ (List.mem_of_mem_tail hm)
  have hp : ∀ edge ∈ G1OriginalSpanClosingPhase.closingExits O cut, O.calendar.age (O.network.graph.source edge) = date := by
    intro edge hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hdate edge (List.takeWhile_subset _ hm)
    · have he := List.mem_singleton.mp hm
      subst edge; rfl
  have hcut : cut ∈ exits := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
  have hsplit : exits = G1OriginalSpanClosingPhase.closingExits O cut ++ remaining := original_exit_list_cut exits cut hcut
  have hn : (G1OriginalSpanClosingPhase.closingExits O cut ++ remaining).Nodup := by
    rw [←hsplit]
    exact Finset.nodup_toList _
  have hnone : ∀ edge ∈ remaining, eventActor O H D hD (.exit edge) ≠ some actor := by
    intro edge hm ho
    have he := actual_private_event_at_closing O H D hD (.exit edge) actor ho (hdate edge (hremaining edge hm))
    have he : edge = cut := OriginalEvent.exit.inj he
    rw [he] at hm
    exact original_cut_absent_from_remaining exits cut (Finset.nodup_toList _) hm
  have hnodes : ownerKernels actor (canonicalRecordedNodeBatchOps O H D hD sample gamma common r
      (Finset.univ.filter (fun node : O.Vertex => O.calendar.age node = date)).toList) = [] := by
    rw [actual_recorded_nodes_private_kernel_word]
    apply List.flatMap_eq_nil_iff.mpr
    intro node hm
    have ht := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
    have ho : nodeActorOwner O H D hD node ≠ some actor := by
      intro hh
      have hlt := (actual_span_node_temporal_bounds O _ node (actual_owned_node_member O H D hD node actor hh)).2
      rw [←actual_actor_cut_source O H D hD actor] at hlt
      rw [ht] at hlt
      exact (lt_irrefl _) hlt
    rw [if_neg ho]
  unfold ownRuntimeParts closingRuntimeFuture afterExitRuntimeOps
  simp only [owner_kernels_append,owner_kernels_history_lift,owner_kernels_opening_batch,
    ownerKernels,recordBaseCheckpoint]
  rw [actual_unowned_recorded_exits_no_kernel O H D hD sample gamma common r actor date _ remaining hp
    (fun e hm => hdate e (hremaining e hm)) hn hnone,hnodes,
    actual_runtime_future_tail_has_no_own_kernel O H D hD sample gamma common r actor date
      (afterDate O.network O.calendar date) le_rfl
      (fun next hm => of_decide_eq_true (List.mem_filter.mp hm).2)]
  rfl

/-- Every private kernel of the full compiler is in this ONE derived OWN
interior. The true-K graph word is therefore its actual fusion word. -/
theorem actual_own_interior_kernel_list_is_whole_private_word (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ownerKernels actor (ownRuntimeParts O H D hD sample gamma common r actor).interior =
      ownerKernels actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) := by
  rw [actual_entire_original_runtime_two_interface_split O H D hD sample gamma common r actor]
  simp only [owner_kernels_append,actual_own_before_piece_has_no_private_kernel,
    actual_own_future_piece_has_no_private_kernel,List.nil_append,List.append_nil]
  simp only [ownRuntimeParts,ownerKernels,historyLift,List.nil_append,List.append_nil]

theorem actual_own_interior_fused_row_is_true_current_root_K (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support) :
    actorWordKernel (ownerKernels actor (ownRuntimeParts O H D hD sample gamma common r actor).interior)
      (unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor)))) =
      canonicalOriginalKActorRow O D gamma common r actor.val actor.property s := by
  rw [actual_own_interior_kernel_list_is_whole_private_word]
  exact actual_whole_original_private_fused_row_is_true_K O H D hD sample register gamma common r actor s hs

#print axioms actual_own_interior_kernel_list_is_whole_private_word
#print axioms actual_own_interior_fused_row_is_true_current_root_K
end G1CanonicalOwnInteriorPrivateWord
