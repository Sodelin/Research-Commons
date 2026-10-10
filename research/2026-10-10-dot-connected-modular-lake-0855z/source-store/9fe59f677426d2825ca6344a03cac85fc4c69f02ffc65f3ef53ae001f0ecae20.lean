import G1OriginalPrivateFutureExclusion

/-! The private source word emitted by the ENTIRE original compiler is the
exact extracted OriginalSpan word between real opening and literal final cut.
Its fused private row is therefore TRUE independently initialized CURRENT-root
K with every old opaque entering subtree, one derived exit and SAME register.
All actor/date overlap and simultaneous boundaries are allowed. -/
namespace G1WholeCanonicalPrivateWordTrueK
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1TaggedOriginalCalendar
open G1CanonicalOriginalNodeAsyncStep G1CanonicalPendingActorSets G1CanonicalThreeEpochList
open G1CanonicalActivePrivateEventWord G1OriginalEventCalendarCuts G1OriginalPrivateWindowBounds
open G1OriginalClosingEventDecomposition G1OriginalPrivateFutureExclusion
open G1OriginalSpanCalendarDecomposition G1OriginalDecoratedSpan G1ActualActorOwnedPrivateSyntax
open G1CanonicalWholePrivateSourceWord G1CanonicalExtractedPrivateKWord G1CanonicalPendingTrueKExposure
open G1CanonicalOriginalKOnlyActorRow G1CanonicalInitializedWholeCalendarHistory
open G1OriginalExteriorCohort G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open G1FinitePendingActorPromotion G1InitializedFrontierPrefix
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def IntervalAfter (O : Source.{u,v,w} X) (start : ℝ) : OriginalEvent O → Prop
  | .interval lower _ => start ≤ lower
  | _ => True

lemma original_boundary_interval_after (O : Source.{u,v,w} X) (start date : ℝ)
    {event : OriginalEvent O} (hm : event ∈ originalBoundaryEvents O date) : IntervalAfter O start event := by
  rcases List.mem_append.mp hm with hm | hm <;>
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hm <;> trivial

lemma actual_stopped_event_intervals_after (O : Source.{u,v,w} X) (start stop lower : ℝ) (dates : List ℝ)
    (ho : dates.Pairwise (· < ·)) (ha : ∀ next ∈ dates, lower < next) (hlo : start ≤ lower) :
    ∀ event ∈ stopBeforeEventTail O stop lower dates, IntervalAfter O start event := by
  induction dates generalizing lower with
  | nil => simp [stopBeforeEventTail]
  | cons next dates ih =>
    have hp := List.pairwise_cons.mp ho
    have hn := ha next (List.mem_cons_self)
    intro event hm
    by_cases he : next = stop
    · have hx : event = .interval lower next := by simpa [stopBeforeEventTail,he] using hm
      subst event; exact hlo
    · simp only [stopBeforeEventTail,if_neg he,List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hlo
      · rcases List.mem_append.mp hm with hm | hm
        · exact original_boundary_interval_after O start next hm
        · exact ih next hp.2 hp.1 (hlo.trans hn.le) event hm

lemma actual_closing_events_private_predicates_same (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    (closingSpanEvents O (actorInput O D actor) (D.vertex (T.network.graph.source actor.val)) (actorCut O H D hD actor)).filter
      (ownedActiveEvent O H D hD actor) =
    (closingSpanEvents O (actorInput O D actor) (D.vertex (T.network.graph.source actor.val)) (actorCut O H D hD actor)).filter
      (ownedPrivateEvent O H D hD actor) := by
  apply List.filter_congr
  intro event hm
  cases event with
  | node node => rfl
  | exit edge => rfl
  | interval lower upper =>
    have hm : OriginalEvent.interval lower upper ∈ stopBeforeEventTail O (O.calendar.age (D.vertex (T.network.graph.source actor.val)))
        (O.calendar.age (actorInput O D actor)) (afterDate O.network O.calendar (O.calendar.age (actorInput O D actor))) := by
      simpa [closingSpanEvents,originalNodeEvents] using hm
    have hlt := actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)
    have hhi := actual_stopped_event_tail_below O _ (original_after_ordered _ _ _) _
      (original_after_member _ _ _ _ hlt) _ hlt (.interval lower upper) hm
    have hlo := actual_stopped_event_intervals_after O _ _ _ _ (original_after_ordered _ _ _)
      (fun next hn => of_decide_eq_true (List.mem_filter.mp hn).2) le_rfl (.interval lower upper) hm
    have ha : actor ∈ canonicalDateActors T lower := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      change T.calendar.age (T.network.graph.target actor.val) ≤ lower ∧ lower < T.calendar.age (T.network.graph.source actor.val)
      rw [D.calendar,D.calendar]
      exact ⟨hlo,hhi⟩⟩)
    simp [ownedActiveEvent,ownedPrivateEvent,ha]

/-- Entire source compiler word equals the precise graph-derived private
span word. Exterior-only time before opening and after close is absent. -/
theorem actual_whole_original_private_word_is_extracted_span (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :
    originalActorSourceWord O H D hD actor gamma common = extractedActorWord O H D hD actor gamma common := by
  rw [actual_whole_active_private_event_word,
    actual_original_closing_event_decomposition O (actorInput O D actor) (D.vertex (T.network.graph.source actor.val))
      (actorCut O H D hD actor) (G1PrivateActorLifetimeAdmission.actual_actor_cut_source O H D hD actor)
      (actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)),
    List.filter_append,List.filter_append,actual_original_frontier_private_mask_empty,actual_original_future_private_mask_empty,
    List.nil_append,List.append_nil,actual_closing_events_private_predicates_same]
  rw [←actual_owned_private_events_extract_original_ops O H D hD actor gamma common,
    actual_closing_span_event_erasure]
  rfl

/-- TRUE-current-root K exposure for the actual full compiler's fused private
coordinate. The cap is on entering CURRENT roots; all original opaque trees,
descendant labels, single exit population and SAME register are retained. -/
theorem actual_whole_original_private_fused_row_is_true_K (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support) :
    actorWordKernel (ownerKernels actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r))
      (unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor)))) =
      canonicalOriginalKActorRow O D gamma common r actor.val actor.property s := by
  rw [actual_whole_calendar_private_fused_source_row,actual_whole_original_private_word_is_extracted_span]
  have he : originalActorInsideCopies O sample (actorInput O D actor) = originalInsideCopies O sample (actorInput O D actor) := by
    ext x; simp [originalActorInsideCopies,originalOutsideCopies,originalInsideCopies]
  simpa only [canonicalPendingKRow,he] using
    actual_canonical_pending_row_is_true_K_graft O H D hD sample register gamma common r actor s hs

#print axioms actual_whole_original_private_word_is_extracted_span
#print axioms actual_whole_original_private_fused_row_is_true_K
end G1WholeCanonicalPrivateWordTrueK
