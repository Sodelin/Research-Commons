import G1OriginalClosingEventDecomposition

/-! Exact elimination of the component's ORIGINAL future from its private
word, including leftover same-date parallel exits after its own literal cut.
The complete outside source continues unchanged in the whole interpreter. -/
namespace G1OriginalPrivateFutureExclusion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1TaggedOriginalCalendar
open G1CanonicalOriginalNodeAsyncStep G1CanonicalPendingActorSets G1OriginalCalendarDecomposition
open G1PrivateActorLifetimeAdmission G1OriginalActorTemporalFootprint G1OriginalSpanRegion
open G1CanonicalActivePrivateEventWord G1OriginalEventCalendarCuts G1OriginalPrivateWindowBounds
open G1OriginalClosingEventDecomposition G1CanonicalThreeEpochList
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def EventAbove (O : Source.{u,v,w} X) (stop : ℝ) : OriginalEvent O → Prop
  | .interval lower _ => stop ≤ lower
  | .exit edge => stop < O.calendar.age (O.network.graph.source edge)
  | .node node => stop ≤ O.calendar.age node

lemma original_boundary_events_above (O : Source.{u,v,w} X) (stop date : ℝ) (hlt : stop < date)
    {event : OriginalEvent O} (hm : event ∈ originalBoundaryEvents O date) : EventAbove O stop event := by
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨edge,he,rfl⟩ := List.mem_map.mp hm
    change stop < O.calendar.age (O.network.graph.source edge)
    rw [(Finset.mem_filter.mp (Finset.mem_toList.mp he)).2]; exact hlt
  · obtain ⟨node,he,rfl⟩ := List.mem_map.mp hm
    change stop ≤ O.calendar.age node
    rw [(Finset.mem_filter.mp (Finset.mem_toList.mp he)).2]; exact hlt.le

lemma actual_event_tail_above (O : Source.{u,v,w} X) (stop lower : ℝ) (dates : List ℝ)
    (hlo : stop ≤ lower) (ha : ∀ date ∈ dates, stop < date) :
    ∀ event ∈ originalEventTail O lower dates, EventAbove O stop event := by
  induction dates generalizing lower with
  | nil => simp [originalEventTail]
  | cons next dates ih =>
    have hn := ha next (List.mem_cons_self)
    intro event hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hlo
    · rcases List.mem_append.mp hm with hm | hm
      · exact original_boundary_events_above O stop next hn hm
      · exact ih next hn.le (fun d hd => ha d (List.mem_cons_of_mem next hd)) event hm

lemma actual_private_mask_false_after_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    (event : OriginalEvent O) (hb : EventAbove O (O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) event) :
    ownedActiveEvent O H D hD actor event = false := by
  cases event with
  | interval lower upper =>
    have hn : actor ∉ canonicalDateActors T lower := by
      intro hm
      have ha := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2.2
      have ha : lower < O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) := by
        simpa only [actual_actor_cut_source,D.calendar] using ha
      exact (not_lt_of_ge hb) ha
    simp [ownedActiveEvent,hn]
  | node node =>
    have hn : eventActor O H D hD (.node node) ≠ some actor := by
      intro hm
      have ha := (actual_span_node_temporal_bounds O _ node (actual_owned_node_member O H D hD node actor hm)).2
      have ha : O.calendar.age node < O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) := by
        simpa only [actual_actor_cut_source] using ha
      exact (not_lt_of_ge hb) ha
    simp [ownedActiveEvent,hn]
  | exit edge =>
    have hn : eventActor O H D hD (.exit edge) ≠ some actor := by
      intro hm
      have ha := (actual_private_event_time_bounds O H D hD (.exit edge) actor hm).2
      exact (not_lt_of_ge ha) hb
    simp [ownedActiveEvent,hn]

lemma original_cut_absent_from_remaining {A : Type*} [DecidableEq A] (items : List A) (cut : A)
    (hn : items.Nodup) : cut ∉ (items.dropWhile (fun x => decide (x ≠ cut))).tail := by
  induction items with
  | nil => simp
  | cons x items ih =>
    have hp := List.nodup_cons.mp hn
    by_cases he : x = cut
    · subst x; simpa using hp.1
    · simpa [he] using ih hp.2

/-- Leftover same-date ORIGINAL operations remain in the same exterior;
they contain no component-private word operation after its own final cut. -/
theorem actual_original_future_private_mask_empty (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    (originalClosingEventFuture O (actorCut O H D hD actor)).filter (ownedActiveEvent O H D hD actor) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro event hm
  unfold originalClosingEventFuture at hm
  rw [List.append_assoc] at hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨edge,he,rfl⟩ := List.mem_map.mp hm
    have heall : edge ∈ originalExits O.network O.calendar (O.calendar.age (O.network.graph.source (actorCut O H D hD actor))) :=
      List.dropWhile_subset _ (List.mem_of_mem_tail he)
    have ht := (Finset.mem_filter.mp (Finset.mem_toList.mp heall)).2
    have hn : eventActor O H D hD (.exit edge) ≠ some actor := by
      intro ho
      have hx := actual_private_event_at_closing O H D hD (.exit edge) actor ho ht
      have hx : edge = actorCut O H D hD actor := OriginalEvent.exit.inj hx
      exact original_cut_absent_from_remaining _ _ (by unfold originalExits; exact Finset.nodup_toList _) (hx ▸ he)
    simp [ownedActiveEvent,hn]
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨node,he,rfl⟩ := List.mem_map.mp hm
      have ht := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
      rw [actual_private_mask_false_after_cut O H D hD actor (.node node) (by change _ ≤ _; exact ht.ge)]
      simp
    · have hb := actual_event_tail_above O _ _ _ le_rfl
        (fun date hd => of_decide_eq_true (List.mem_filter.mp hd).2) event hm
      rw [actual_private_mask_false_after_cut O H D hD actor event hb]
      simp

theorem actual_original_frontier_private_mask_empty (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    (openingFrontierEvents O (actorInput O D actor)).filter (ownedActiveEvent O H D hD actor) = [] := by
  rw [openingFrontierEvents,List.filter_append,actual_original_prefix_private_mask_empty,List.nil_append]
  apply List.filter_eq_nil_iff.mpr
  intro event hm
  obtain ⟨edge,he,rfl⟩ := List.mem_map.mp hm
  have ht := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
  have hn : eventActor O H D hD (.exit edge) ≠ some actor := by
    intro ho
    have hb := (actual_span_exit_temporal_bounds O _ edge (actual_owned_exit_member O H D hD edge actor ho)).1
    rw [ht] at hb
    exact (lt_irrefl _) hb
  simp [ownedActiveEvent,hn]

#print axioms actual_original_future_private_mask_empty
#print axioms actual_original_frontier_private_mask_empty
end G1OriginalPrivateFutureExclusion
