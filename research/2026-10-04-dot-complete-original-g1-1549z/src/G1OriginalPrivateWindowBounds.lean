import G1OriginalEventCalendarCuts

/-! Actual original chronological prefix exclusion for the private source
word. Bounds are derived from the graph span and exact scheduled dates, not
from a chosen output law or a manually supplied actor lifetime. -/
namespace G1OriginalPrivateWindowBounds
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1TaggedOriginalCalendar
open G1CanonicalOriginalNodeAsyncStep G1CanonicalPendingActorSets
open G1PrivateActorLifetimeAdmission G1OriginalActorTemporalFootprint G1OriginalSpanRegion
open G1CanonicalActivePrivateEventWord G1OriginalEventCalendarCuts
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def EventBelow (O : Source.{u,v,w} X) (stop : ℝ) : OriginalEvent O → Prop
  | .interval lower _ => lower < stop
  | .exit edge => O.calendar.age (O.network.graph.source edge) < stop
  | .node node => O.calendar.age node < stop

lemma original_boundary_events_below (O : Source.{u,v,w} X) (date stop : ℝ) (hlt : date < stop)
    {event : OriginalEvent O} (hm : event ∈ originalBoundaryEvents O date) : EventBelow O stop event := by
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨edge,he,rfl⟩ := List.mem_map.mp hm
    change O.calendar.age (O.network.graph.source edge) < stop
    rw [(Finset.mem_filter.mp (Finset.mem_toList.mp he)).2]
    exact hlt
  · obtain ⟨node,he,rfl⟩ := List.mem_map.mp hm
    change O.calendar.age node < stop
    rw [(Finset.mem_filter.mp (Finset.mem_toList.mp he)).2]
    exact hlt

lemma actual_stopped_event_tail_below (O : Source.{u,v,w} X) (dates : List ℝ)
    (ho : dates.Pairwise (· < ·)) (stop : ℝ) (hm : stop ∈ dates) (lower : ℝ) (hlt : lower < stop) :
    ∀ event ∈ stopBeforeEventTail O stop lower dates, EventBelow O stop event := by
  induction dates generalizing lower with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons next dates ih =>
    have hp := List.pairwise_cons.mp ho
    by_cases hn : next = stop
    · intro event he
      have he : event = .interval lower next := by simpa [stopBeforeEventTail,hn] using he
      subst event; exact hlt
    · have hs : stop ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm hn)
      have hns := hp.1 _ hs
      intro event he
      simp only [stopBeforeEventTail,if_neg hn,List.mem_cons] at he
      rcases he with rfl | he
      · exact hlt
      · rcases List.mem_append.mp he with he | he
        · exact original_boundary_events_below O next stop hns he
        · exact ih hp.2 hs next hns event he

theorem actual_before_boundary_events_below (O : Source.{u,v,w} X) (stop : ℝ)
    (hm : stop ∈ sortedOriginalDates O.network O.calendar) :
    ∀ event ∈ beforeBoundaryEvents O stop, EventBelow O stop event := by
  have hne : sortedOriginalDates O.network O.calendar ≠ [] := by
    intro he; rw [he] at hm; exact List.not_mem_nil hm
  obtain ⟨date,dates,he⟩ := List.exists_cons_of_ne_nil hne
  have ho := original_dates_strict O.network O.calendar
  rw [he] at ho hm
  have hp := List.pairwise_cons.mp ho
  by_cases hd : date = stop
  · simp [beforeBoundaryEvents,he,hd]
  · have hs : stop ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm hd)
    have hlt := hp.1 _ hs
    intro event hm
    simp only [beforeBoundaryEvents,he,if_neg hd] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact original_boundary_events_below O date stop hlt hm
    · exact actual_stopped_event_tail_below O dates hp.2 stop hs date hlt event hm

lemma actual_private_mask_false_before_open (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    (event : OriginalEvent O) (hb : EventBelow O (O.calendar.age (actorInput O D actor)) event) :
    ownedActiveEvent O H D hD actor event = false := by
  cases event with
  | interval lower upper =>
    have hn : actor ∉ canonicalDateActors T lower := by
      intro hm
      have ha := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2.1
      have ha : O.calendar.age (actorInput O D actor) ≤ lower := by simpa only [actorInput,D.calendar] using ha
      exact (not_lt_of_ge ha) hb
    simp [ownedActiveEvent,hn]
  | node node =>
    have hn : eventActor O H D hD (.node node) ≠ some actor := by
      intro hm
      have ha := (actual_private_event_time_bounds O H D hD (.node node) actor hm).1
      exact (not_lt_of_ge ha) hb
    simp [ownedActiveEvent,hn]
  | exit edge =>
    have hn : eventActor O H D hD (.exit edge) ≠ some actor := by
      intro hm
      have ha := (actual_private_event_time_bounds O H D hD (.exit edge) actor hm).1
      exact (not_lt_of_ge ha) hb
    simp [ownedActiveEvent,hn]

/-- The real original prefix before actor opening contains NO private word
operation, including no inactive exterior epoch. -/
theorem actual_original_prefix_private_mask_empty (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    (beforeBoundaryEvents O (O.calendar.age (actorInput O D actor))).filter
      (ownedActiveEvent O H D hD actor) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro event hm
  rw [actual_private_mask_false_before_open O H D hD actor event
    (actual_before_boundary_events_below O _ (original_date_scheduled O.network O.calendar _) event hm)]
  simp

#print axioms actual_original_prefix_private_mask_empty
end G1OriginalPrivateWindowBounds
