import G1CanonicalOwnTwoInterfaceRuntime

/-! Actual private runtime interiors have NO OWN interface. This admission
is derived from original cut IDs and physical opening/closing dates, including
all coincident other-actor opens/releases and every old checkpoint observer. -/
namespace G1CanonicalInteriorInterfaceAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1ActorInterfaceUniqueness G1TaggedOriginalCalendar
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitCloseReplay
open G1CanonicalOriginalOpeningAsyncBatch G1CanonicalOriginalEpochAsync G1CanonicalPendingActorSets
open G1ActualOriginalNodeBatchRootHistory G1ActualOriginalExitBatchRootHistory G1ActualOriginalBoundaryRootHistory
open G1CanonicalOwnEntryCoordinateAdmission G1CanonicalOwnOpeningRuntimePosition G1CanonicalOwnClosingRuntimePosition
open G1CanonicalOwnTwoInterfaceRuntime G1ActualSafeOwnInputRetention G1OriginalPrivateFutureExclusion
open G1OriginalRuntimeCalendarCuts G1OriginalCalendarDecomposition G1CanonicalThreeEpochList
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1PendingBaseCheckpointRecorder
open G1OriginalSpanCalendarDecomposition G1OriginalDecoratedSpan G1PrivateActorLifetimeAdmission
open G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma interior_safe_append {I S Base : Type*} [DecidableEq I] (owner : I)
    (first last : List (AsyncOperation I S Base)) :
    (∀ op ∈ first ++ last, InteriorSafe owner op) ↔
      (∀ op ∈ first, InteriorSafe owner op) ∧ (∀ op ∈ last, InteriorSafe owner op) := by
  constructor
  · intro hs
    exact ⟨fun op hm => hs op (List.mem_append_left _ hm),fun op hm => hs op (List.mem_append_right _ hm)⟩
  · rintro ⟨hs,ht⟩ op hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hs op hm
    · exact ht op hm

lemma interior_safe_history_lift {I S Base Obs : Type*} [DecidableEq I] (owner : I)
    (op : AsyncOperation I S Base) (hs : InteriorSafe owner op) : InteriorSafe owner (historyLift (Obs := Obs) op) := by
  cases op <;> exact hs

lemma interior_safe_recorded_block {I S Base Obs : Type*} [DecidableEq I] (owner : I) (observer : Base → Obs)
    (ops : List (AsyncOperation I S Base)) (hs : ∀ op ∈ ops, InteriorSafe owner op) :
    ∀ op ∈ recordedBlock observer ops, InteriorSafe owner op := by
  intro op hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
    exact interior_safe_history_lift owner old (hs old ho)
  · have he : op = recordBaseCheckpoint observer := List.mem_singleton.mp hm
    subst op; trivial

lemma actual_node_batch_interior_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (nodes : List O.Vertex) :
    ∀ op ∈ canonicalRecordedNodeBatchOps O H D hD sample gamma common r nodes, InteriorSafe actor op := by
  intro op hm
  obtain ⟨node,_,ho⟩ := List.mem_flatMap.mp hm
  apply interior_safe_recorded_block actor _ _ _ op ho
  intro old hm
  have he : old = canonicalNodeAsyncOperation O H D hD sample gamma common r node := List.mem_singleton.mp hm
  subst old
  unfold canonicalNodeAsyncOperation
  cases nodeActorOwner O H D hD node <;> trivial

lemma actual_epoch_block_interior_safe (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (lower upper : ℝ) :
    ∀ op ∈ recordedEpochBlock O D sample r lower upper, InteriorSafe actor op := by
  apply interior_safe_recorded_block
  intro op hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨other,_,rfl⟩ := List.mem_map.mp hm
    trivial
  · have he := List.mem_singleton.mp hm
    subst op; trivial

lemma actual_exit_batch_interior_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) (processed edges : List O.Edge) (hn : actorCut O H D hD actor ∉ edges) :
    ∀ op ∈ canonicalRecordedExitBatchOps O H D hD sample gamma common r date processed edges, InteriorSafe actor op := by
  induction edges generalizing processed with
  | nil => simp [canonicalRecordedExitBatchOps]
  | cons edge edges ih =>
    intro op hm
    rcases List.mem_append.mp hm with hm | hm
    · apply interior_safe_recorded_block actor _ _ _ op hm
      intro old hm
      rcases List.mem_append.mp hm with hm | hm
      · have he := List.mem_singleton.mp hm
        subst old
        unfold canonicalExitAsyncOperation
        cases eventActor O H D hD (.exit edge) <;> trivial
      · obtain ⟨other,hother,rfl⟩ := List.mem_map.mp hm
        change actor ≠ other
        intro he
        subst other
        have hclose : closingActor O H D hD (.exit edge) = some actor := by simpa using hother
        have he := (actual_closing_actor_site_iff O H D hD (.exit edge) actor).mp hclose
        exact hn (List.mem_cons.mpr (Or.inl (OriginalEvent.exit.inj he).symm))
    · exact ih _ (fun he => hn (List.mem_cons_of_mem edge he)) op hm

lemma actual_boundary_interior_safe_away_from_own_dates (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ)
    (hopen : date ≠ O.calendar.age (actorInput O D actor))
    (hclose : date ≠ O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) :
    ∀ op ∈ canonicalRecordedBoundaryOps O H D hD sample gamma common r date, InteriorSafe actor op := by
  unfold canonicalRecordedBoundaryOps
  rw [interior_safe_append,interior_safe_append]
  refine ⟨⟨actual_exit_batch_interior_safe O H D hD sample gamma common r actor date [] _ ?_,?_⟩,
    actual_node_batch_interior_safe O H D hD sample gamma common r actor _⟩
  · intro hm
    have he := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
    exact hclose he.symm
  · have hn : actor ∉ canonicalOriginalOpeningActors O H D hD date := by
      intro hm
      have ha := (actual_original_opening_actor_membership O H D hD date actor).mp hm
      have he := (Finset.mem_filter.mp ha).2
      have he : date = O.calendar.age (actorInput O D actor) := by simpa only [actorInput,D.calendar] using he.symm
      exact hopen he
    intro op hm
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
    apply interior_safe_history_lift
    have hs := actual_other_opening_batch_safe O D sample actor _ _ hn old ho
    cases old <;> simp_all [SafeFor,InteriorSafe]

lemma actual_stopped_runtime_tail_interior_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (stop lower : ℝ) (dates : List ℝ)
    (ho : dates.Pairwise (· < ·)) (hm : stop ∈ dates)
    (haway : ∀ next ∈ dates, next < stop → next ≠ O.calendar.age (actorInput O D actor) ∧
      next ≠ O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) :
    ∀ op ∈ stoppedRuntimeTail O H D hD sample gamma common r stop lower dates, InteriorSafe actor op := by
  induction dates generalizing lower with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons next dates ih =>
    have hp := List.pairwise_cons.mp ho
    by_cases he : next = stop
    · simpa only [stoppedRuntimeTail,if_pos he] using actual_epoch_block_interior_safe O D sample r actor lower next
    · have hs : stop ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
      have hlt := hp.1 _ hs
      have ha := haway next (List.mem_cons_self) hlt
      simp only [stoppedRuntimeTail,if_neg he,interior_safe_append]
      exact ⟨⟨actual_epoch_block_interior_safe O D sample r actor lower next,
        actual_boundary_interior_safe_away_from_own_dates O H D hD sample gamma common r actor next ha.1 ha.2⟩,
        ih next hp.2 hs (fun n hn hns => haway n (List.mem_cons_of_mem next hn) hns)⟩

/-- The complete actual source-derived OWN interior is admitted by the finite
private fusion theorem, including arbitrary overlapping/coincident actors. -/
theorem actual_own_runtime_interior_has_no_own_interface (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ∀ op ∈ (ownRuntimeParts O H D hD sample gamma common r actor).interior, InteriorSafe actor op := by
  unfold ownRuntimeParts
  simp only [interior_safe_append]
  refine ⟨⟨⟨⟨?_,actual_node_batch_interior_safe O H D hD sample gamma common r actor _⟩,?_
    ⟩,actual_exit_batch_interior_safe O H D hD sample gamma common r actor _ [] _ ?_⟩,?_⟩
  · intro op hm
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
    apply interior_safe_history_lift
    have hs := actual_other_opening_batch_safe O D sample actor _ _
      (original_cut_absent_from_remaining _ actor (actual_original_opening_actor_nodup O H D hD _)) old ho
    cases old <;> simp_all [SafeFor,InteriorSafe]
  · have hlt := actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)
    rw [←actual_actor_cut_source O H D hD actor] at hlt
    apply actual_stopped_runtime_tail_interior_safe O H D hD sample gamma common r actor _ _ _
      (original_after_ordered _ _ _) (original_after_member _ _ _ _ hlt)
    intro next hm hns
    have hlo : O.calendar.age (actorInput O D actor) < next := of_decide_eq_true (List.mem_filter.mp hm).2
    exact ⟨ne_of_gt hlo,ne_of_lt hns⟩
  · intro hm
    unfold beforeOwnCutEdges at hm
    have he : actorCut O H D hD actor ≠ actorCut O H D hD actor :=
      of_decide_eq_true (List.mem_takeWhile_imp (p := fun edge : O.Edge => decide (edge ≠ actorCut O H D hD actor)) hm)
    exact he rfl
  · intro op hm
    have he := List.mem_singleton.mp hm
    subst op; trivial

#print axioms actual_own_runtime_interior_has_no_own_interface
end G1CanonicalInteriorInterfaceAdmission
