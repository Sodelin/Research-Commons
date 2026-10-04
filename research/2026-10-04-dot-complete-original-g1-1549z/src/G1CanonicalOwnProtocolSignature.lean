import G1OwnProtocolSignatureTransport

/-! The unchanged chronological compiler has exactly the OWN opening,
complete private word, and OWN release in its private/interface signature.
Physical dates derive absence of OWN interfaces outside that lifetime. -/
namespace G1CanonicalOwnProtocolSignature
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalOpeningAsyncBatch G1CanonicalPendingActorSets
open G1ActualOriginalExitBatchRootHistory G1ActualOriginalNodeBatchRootHistory G1ActualOriginalBoundaryRootHistory
open G1CanonicalOwnOpeningRuntimePosition G1CanonicalOwnEntryCoordinateAdmission G1CanonicalOwnTwoInterfaceRuntime
open G1CanonicalInteriorInterfaceAdmission G1CanonicalOwnInteriorPrivateWord G1CanonicalOutsidePrivateKernelExclusion
open G1OriginalRuntimeCalendarCuts G1OriginalClosingRuntimeDecomposition G1OriginalCalendarDecomposition
open G1CanonicalThreeEpochList G1OriginalDecoratedSpan G1OriginalSpanCalendarDecomposition G1TaggedOriginalCalendar
open G1OriginalPrivateFutureExclusion G1CanonicalInitializedWholeCalendarHistory
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1PendingBaseCheckpointRecorder
open G1ActualSafeOwnInputRetention G1OwnProtocolSignatureTransport G1UnrankedSourceView
open G1WholeFinitePendingPromotion
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma signature_of_interior_safe {I S Base : Type*} [DecidableEq I] (owner : I)
    (ops : List (AsyncOperation I S Base)) (hs : ∀ op ∈ ops, InteriorSafe owner op) :
    ownProtocolSignature owner ops = (ownerKernels owner ops).map (.localStep owner) := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    have ho := hs op List.mem_cons_self
    have ht : ∀ q ∈ ops, InteriorSafe owner q := fun q hq => hs q (List.mem_cons_of_mem op hq)
    have hi := ih ht
    simp only [ownProtocolSignature] at hi
    cases op with
    | localStep other kernel =>
      by_cases he : owner = other
      · subst other; simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,hi]
      · simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,he,hi]
    | interface other kernel =>
      change owner ≠ other at ho
      simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,ho,hi]
    | exterior kernel => simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,hi]

lemma actual_recorded_openings_interior_safe (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (actor : BridgeActor T) (actors opening : List (BridgeActor T)) (hn : actor ∉ opening) :
    ∀ op ∈ (canonicalOpeningBatchOps O D sample actors opening).map
      (historyLift (Obs := UnrankedView O.Vertex O.Edge Copy)), InteriorSafe actor op := by
  intro op hm
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
  apply interior_safe_history_lift
  have hh := actual_other_opening_batch_safe O D sample actor actors opening hn old ho
  cases old <;> simp_all [SafeFor,InteriorSafe]

lemma actual_before_own_date_interior_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ∀ op ∈ beforeRuntimeBoundary O H D hD sample gamma common r (O.calendar.age (actorInput O D actor)),
      InteriorSafe actor op := by
  have hlt := actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)
  rw [←actual_actor_cut_source O H D hD actor] at hlt
  have hm := original_date_scheduled O.network O.calendar (actorInput O D actor)
  have hne : sortedOriginalDates O.network O.calendar ≠ [] := by intro he; rw [he] at hm; exact List.not_mem_nil hm
  obtain ⟨date,dates,he⟩ := List.exists_cons_of_ne_nil hne
  have ho := original_dates_strict O.network O.calendar
  rw [he] at ho hm
  have hp := List.pairwise_cons.mp ho
  unfold beforeRuntimeBoundary
  rw [he]
  by_cases hd : date = O.calendar.age (actorInput O D actor)
  · simp [hd]
  · have hs : O.calendar.age (actorInput O D actor) ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm hd)
    have hb := hp.1 _ hs
    simp only [if_neg hd,interior_safe_append]
    refine ⟨actual_boundary_interior_safe_away_from_own_dates O H D hD sample gamma common r actor date hd
      (ne_of_lt (hb.trans hlt)),?_⟩
    apply actual_stopped_runtime_tail_interior_safe O H D hD sample gamma common r actor _ _ _ hp.2 hs
    intro next hn hnext
    exact ⟨ne_of_lt hnext,ne_of_lt (hnext.trans hlt)⟩

lemma actual_own_before_piece_interior_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ∀ op ∈ (ownRuntimeParts O H D hD sample gamma common r actor).before, InteriorSafe actor op := by
  unfold ownRuntimeParts
  rw [interior_safe_append,interior_safe_append]
  refine ⟨⟨actual_before_own_date_interior_safe O H D hD sample gamma common r actor,
    actual_exit_batch_interior_safe O H D hD sample gamma common r actor _ [] _ ?_⟩,
    actual_recorded_openings_interior_safe O D sample actor _ _ ?_⟩
  · intro hm
    have ht := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
    have hlt := actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)
    rw [←actual_actor_cut_source O H D hD actor,ht] at hlt
    exact (lt_irrefl _) hlt
  · intro hm
    unfold sourceOpenPrefix at hm
    have he : actor ≠ actor := of_decide_eq_true
      (List.mem_takeWhile_imp (p := fun other : BridgeActor T => decide (other ≠ actor)) hm)
    exact he rfl

lemma actual_future_tail_interior_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (lower : ℝ) (dates : List ℝ)
    (ha : ∀ next ∈ dates, O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) < next) :
    ∀ op ∈ recordedRuntimeTail O H D hD sample gamma common r lower dates, InteriorSafe actor op := by
  have hlt := actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)
  rw [←actual_actor_cut_source O H D hD actor] at hlt
  induction dates generalizing lower with
  | nil => simp [recordedRuntimeTail]
  | cons next dates ih =>
    have hn := ha next List.mem_cons_self
    simp only [recordedRuntimeTail,interior_safe_append]
    exact ⟨⟨actual_epoch_block_interior_safe O D sample r actor lower next,
      actual_boundary_interior_safe_away_from_own_dates O H D hD sample gamma common r actor next
        (ne_of_gt (hlt.trans hn)) (ne_of_gt hn)⟩,
      ih next (fun d hd => ha d (List.mem_cons_of_mem next hd))⟩

lemma actual_own_future_piece_interior_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ∀ op ∈ (ownRuntimeParts O H D hD sample gamma common r actor).future, InteriorSafe actor op := by
  have hlt := actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)
  rw [←actual_actor_cut_source O H D hD actor] at hlt
  unfold ownRuntimeParts closingRuntimeFuture afterExitRuntimeOps
  simp only [interior_safe_append]
  refine ⟨?_,⟨⟨actual_exit_batch_interior_safe O H D hD sample gamma common r actor _ _ _ ?_,
    ⟨actual_recorded_openings_interior_safe O D sample actor _ _ ?_,
      actual_node_batch_interior_safe O H D hD sample gamma common r actor _⟩⟩,
    actual_future_tail_interior_safe O H D hD sample gamma common r actor _ _ ?_⟩⟩
  · intro op hm; have he := List.mem_singleton.mp hm; subst op; trivial
  · exact original_cut_absent_from_remaining _ _ (Finset.nodup_toList _)
  · intro hm
    have ha := (actual_original_opening_actor_membership O H D hD _ actor).mp hm
    have he := (Finset.mem_filter.mp ha).2
    have he : O.calendar.age (actorInput O D actor) = O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) :=
      by simpa only [actorInput,D.calendar] using he
    exact (ne_of_lt hlt) he
  · intro next hm
    exact of_decide_eq_true (List.mem_filter.mp hm).2

/-- Exactly one real opening, the ENTIRE source private word, and one real
release, including overlapping lifetimes and every coincident date batch. -/
theorem actual_original_own_protocol_signature (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ownProtocolSignature actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) =
      [(ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
      (ownerKernels actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)).map (.localStep actor) ++
      [(ownRuntimeParts O H D hD sample gamma common r actor).closing] := by
  conv_lhs => rw [actual_entire_original_runtime_two_interface_split O H D hD sample gamma common r actor]
  simp only [own_signature_append]
  rw [signature_of_interior_safe actor _ (actual_own_before_piece_interior_safe O H D hD sample gamma common r actor),
    signature_of_interior_safe actor _ (actual_own_runtime_interior_has_no_own_interface O H D hD sample gamma common r actor),
    signature_of_interior_safe actor _ (actual_own_future_piece_interior_safe O H D hD sample gamma common r actor),
    actual_own_before_piece_has_no_private_kernel,actual_own_future_piece_has_no_private_kernel]
  simp only [List.map_nil,List.nil_append,List.append_nil]
  rw [actual_own_interior_kernel_list_is_whole_private_word]
  simp [ownRuntimeParts,ownProtocolSignature,ownedProtocolOp,historyLift]

/-- Any finite earlier sweep of OTHER actors retains the same two real OWN
interfaces and the complete original word of this unprocessed actor. -/
theorem actual_unprocessed_original_protocol_after_promotions (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (earlier : List (BridgeActor T)) (hn : actor ∉ earlier) :
    ownProtocolSignature actor (promoteEveryActor earlier
      (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)) =
      [(ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
      (ownerKernels actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)).map (.localStep actor) ++
      [(ownRuntimeParts O H D hD sample gamma common r actor).closing] := by
  rw [actual_other_finite_promotions_preserve_own_protocol actor earlier hn,
    actual_original_own_protocol_signature]

#print axioms actual_original_own_protocol_signature
#print axioms actual_unprocessed_original_protocol_after_promotions
end G1CanonicalOwnProtocolSignature
