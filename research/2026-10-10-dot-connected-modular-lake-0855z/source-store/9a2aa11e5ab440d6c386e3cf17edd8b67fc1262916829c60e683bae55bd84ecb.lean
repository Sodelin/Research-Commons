import G1CanonicalInteriorInterfaceAdmission

/-! Actual before-opening/after-closing calendar regions emit NO OWN private
kernel. These are derived physical date/owner facts on the same compiler,
including inactive epochs; they bind a complete fused word to its own interior. -/
namespace G1CanonicalOutsidePrivateKernelExclusion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalEpochAsync G1CanonicalPendingActorSets
open G1CanonicalBoundaryPrivateWordBinding G1CanonicalActorKernelSourceBindings
open G1CanonicalActivePrivateEventWord G1OriginalPrivateWindowBounds G1OriginalPrivateFutureExclusion
open G1TaggedOriginalCalendar G1CanonicalThreeEpochList G1OriginalRuntimeCalendarCuts
open G1ActualOriginalBoundaryRootHistory G1PendingBaseCheckpointRecorder G1FinitePendingActorPromotion
open G1CanonicalInteriorInterfaceAdmission G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_boundary_before_has_no_own_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) (hlt : date < O.calendar.age (actorInput O D actor)) :
    ownerKernels actor (canonicalRecordedBoundaryOps O H D hD sample gamma common r date) = [] := by
  rw [actual_whole_boundary_private_kernel_word]
  have he : originalBoundaryPrivateWord O H D hD actor gamma common date = [] := by
    unfold originalBoundaryPrivateWord
    rw [←actual_boundary_active_filter]
    have hf : (originalBoundaryEvents O date).filter (ownedActiveEvent O H D hD actor) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro event hm
      rw [actual_private_mask_false_before_open O H D hD actor event
        (original_boundary_events_below O date _ hlt hm)]
      simp
    rw [hf]; rfl
  rw [he]; rfl

lemma actual_boundary_after_has_no_own_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) (hlt : O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) < date) :
    ownerKernels actor (canonicalRecordedBoundaryOps O H D hD sample gamma common r date) = [] := by
  rw [actual_whole_boundary_private_kernel_word]
  have he : originalBoundaryPrivateWord O H D hD actor gamma common date = [] := by
    unfold originalBoundaryPrivateWord
    rw [←actual_boundary_active_filter]
    have hf : (originalBoundaryEvents O date).filter (ownedActiveEvent O H D hD actor) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro event hm
      rw [actual_private_mask_false_after_cut O H D hD actor event
        (original_boundary_events_above O _ date hlt hm)]
      simp
    rw [hf]; rfl
  rw [he]; rfl

lemma actual_epoch_outside_has_no_own_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (lower upper : ℝ)
    (houtside : lower < O.calendar.age (actorInput O D actor) ∨
      O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) ≤ lower) :
    ownerKernels actor (recordedEpochBlock O D sample r lower upper) = [] := by
  have hn : actor ∉ canonicalDateActors T lower := by
    intro hm
    have ha := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
    have hlo : O.calendar.age (actorInput O D actor) ≤ lower := by simpa only [actorInput,D.calendar] using ha.1
    have hhi : lower < O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) :=
      by simpa only [actual_actor_cut_source,D.calendar] using ha.2
    rcases houtside with hb | hb
    · exact (not_lt_of_ge hlo) hb
    · exact (not_lt_of_ge hb) hhi
  rw [recordedEpochBlock,owner_kernels_recorded_block,actual_original_epoch_owner_kernel,if_neg hn]

lemma actual_stopped_runtime_before_has_no_own_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (lower : ℝ) (dates : List ℝ)
    (ho : dates.Pairwise (· < ·)) (hm : O.calendar.age (actorInput O D actor) ∈ dates)
    (hlt : lower < O.calendar.age (actorInput O D actor)) :
    ownerKernels actor (stoppedRuntimeTail O H D hD sample gamma common r
      (O.calendar.age (actorInput O D actor)) lower dates) = [] := by
  induction dates generalizing lower with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons next dates ih =>
    have hp := List.pairwise_cons.mp ho
    by_cases he : next = O.calendar.age (actorInput O D actor)
    · simpa only [stoppedRuntimeTail,if_pos he] using
        actual_epoch_outside_has_no_own_kernel O H D hD sample r actor lower next (Or.inl hlt)
    · have hs : O.calendar.age (actorInput O D actor) ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
      have hn := hp.1 _ hs
      simp only [stoppedRuntimeTail,if_neg he,owner_kernels_append]
      rw [actual_epoch_outside_has_no_own_kernel O H D hD sample r actor lower next (Or.inl hlt),
        actual_boundary_before_has_no_own_kernel O H D hD sample gamma common r actor next hn,ih next hp.2 hs hn]
      rfl

/-- Before the actual own opening, the entire chronological runtime prefix
has no private owner kernel. Thus the full source word is not split there. -/
theorem actual_before_own_date_has_no_own_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ownerKernels actor (beforeRuntimeBoundary O H D hD sample gamma common r (O.calendar.age (actorInput O D actor))) = [] := by
  have hm := original_date_scheduled O.network O.calendar (actorInput O D actor)
  have hne : sortedOriginalDates O.network O.calendar ≠ [] := by intro he; rw [he] at hm; exact List.not_mem_nil hm
  obtain ⟨date,dates,he⟩ := List.exists_cons_of_ne_nil hne
  have ho := original_dates_strict O.network O.calendar
  rw [he] at ho hm
  have hp := List.pairwise_cons.mp ho
  unfold beforeRuntimeBoundary
  rw [he]
  by_cases hd : date = O.calendar.age (actorInput O D actor)
  · simp [hd,ownerKernels]
  · have hs : O.calendar.age (actorInput O D actor) ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm hd)
    have hlt := hp.1 _ hs
    simp only [if_neg hd,owner_kernels_append]
    rw [actual_boundary_before_has_no_own_kernel O H D hD sample gamma common r actor date hlt,
      actual_stopped_runtime_before_has_no_own_kernel O H D hD sample gamma common r actor date dates hp.2 hs hlt]
    rfl

lemma actual_runtime_future_tail_has_no_own_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (lower : ℝ) (dates : List ℝ)
    (hlo : O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) ≤ lower)
    (ha : ∀ next ∈ dates, O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) < next) :
    ownerKernels actor (recordedRuntimeTail O H D hD sample gamma common r lower dates) = [] := by
  induction dates generalizing lower with
  | nil => rfl
  | cons next dates ih =>
    have hn := ha next (List.mem_cons_self)
    simp only [recordedRuntimeTail,owner_kernels_append]
    rw [actual_epoch_outside_has_no_own_kernel O H D hD sample r actor lower next (Or.inr hlo),
      actual_boundary_after_has_no_own_kernel O H D hD sample gamma common r actor next hn,
      ih next hn.le (fun d hd => ha d (List.mem_cons_of_mem next hd))]
    rfl

#print axioms actual_before_own_date_has_no_own_kernel
end G1CanonicalOutsidePrivateKernelExclusion
