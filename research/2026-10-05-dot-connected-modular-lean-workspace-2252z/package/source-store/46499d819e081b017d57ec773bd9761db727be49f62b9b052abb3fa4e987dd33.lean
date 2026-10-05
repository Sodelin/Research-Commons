import G1OriginalActorLifecycleOrder

/-! EVERY private original node/exit is between its source-derived actor
interfaces. Equal-date boundaries are admitted by exact opening/final-cut
identity, not by artificially separating actors' calendar times. -/
namespace G1PrivateActorLifetimeAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginalRecipePopulationOwnership
open G1ConstructedPopulationPartition G1OriginalActorOperationOwnership
open G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends G1OriginalSpanClosingPhase
open G1OriginatedClosingSourceAdmission G1TaggedOriginalCalendar G1OriginalEventSiteUniqueness
open G1CanonicalActorLifecycleCompiler G1ActorInterfaceUniqueness G1OriginalActorLifecycleOrder
open G1OriginalActorTemporalFootprint
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_owned_node_member (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (v : O.Vertex) (actor : BridgeActor T)
    (h : nodeActorOwner O H D hD v = some actor) :
    v ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property) := by
  unfold nodeActorOwner at h
  split_ifs at h with hw
  have ha := Option.some.inj h
  rw [←ha]
  exact Classical.choose_spec hw

lemma actual_owned_exit_member (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (e : O.Edge) (actor : BridgeActor T)
    (h : eventActor O H D hD (.exit e) = some actor) :
    e ∈ edgeRegion O (bridgeSpan O T D actor.val actor.property) := by
  simp only [eventActor] at h
  split_ifs at h with hb
  have ha := Option.some.inj h
  rw [←ha,actual_bridge_span_populations]
  exact actual_population_owner_spec O H D hD e

lemma actual_actor_cut_source (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    O.network.graph.source (actorCut O H D hD actor) = D.vertex (T.network.graph.source actor.val) :=
  (actual_original_last_cut O _
    (actual_bridge_span_bookends O T D actor.val actor.property (actual_originated_recipes_bookended O H D hD actor.val)).2).2.1

lemma actual_actor_cut_ends_at (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    EndsAt O (actorCut O H D hD actor) (bridgeSpan O T D actor.val actor.property) :=
  (actual_original_last_cut O _
    (actual_bridge_span_bookends O T D actor.val actor.property (actual_originated_recipes_bookended O H D hD actor.val)).2).2.2

lemma actual_private_event_time_bounds (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (event : OriginalEvent O) (actor : BridgeActor T)
    (h : eventActor O H D hD event = some actor) :
    siteDate O (.node (actorInput O D actor)) ≤ siteDate O event ∧
      siteDate O event ≤ siteDate O (.exit (actorCut O H D hD actor)) := by
  cases event with
  | interval _ _ => cases h
  | node v =>
    have hv := actual_owned_node_member O H D hD v actor h
    obtain ⟨hlo,hhi⟩ := actual_span_node_temporal_bounds O _ v hv
    change O.calendar.age (actorInput O D actor) ≤ O.calendar.age v ∧
      O.calendar.age v ≤ O.calendar.age (O.network.graph.source (actorCut O H D hD actor))
    rw [actual_actor_cut_source]
    exact ⟨hlo,hhi.le⟩
  | exit e =>
    have he := actual_owned_exit_member O H D hD e actor h
    obtain ⟨hlo,hhi⟩ := actual_span_exit_temporal_bounds O _ e he
    change O.calendar.age (actorInput O D actor) ≤ O.calendar.age (O.network.graph.source e) ∧
      O.calendar.age (O.network.graph.source e) ≤ O.calendar.age (O.network.graph.source (actorCut O H D hD actor))
    rw [actual_actor_cut_source]
    exact ⟨hlo.le,hhi⟩

lemma actual_private_event_at_opening (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (event : OriginalEvent O) (actor : BridgeActor T)
    (h : eventActor O H D hD event = some actor)
    (ht : siteDate O event = siteDate O (.node (actorInput O D actor))) :
    event = .node (actorInput O D actor) := by
  cases event with
  | interval _ _ => cases h
  | node v =>
    exact congrArg OriginalEvent.node (actual_only_input_node_at_start O _ v (actual_owned_node_member O H D hD v actor h) ht)
  | exit e =>
    have hlt := (actual_span_exit_temporal_bounds O _ e (actual_owned_exit_member O H D hD e actor h)).1
    change O.calendar.age (O.network.graph.source e) = O.calendar.age (actorInput O D actor) at ht
    rw [ht] at hlt
    exact False.elim (lt_irrefl _ hlt)

lemma actual_private_event_at_closing (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (event : OriginalEvent O) (actor : BridgeActor T)
    (h : eventActor O H D hD event = some actor)
    (ht : siteDate O event = siteDate O (.exit (actorCut O H D hD actor))) :
    event = .exit (actorCut O H D hD actor) := by
  cases event with
  | interval _ _ => cases h
  | node v =>
    have hlt := (actual_span_node_temporal_bounds O _ v (actual_owned_node_member O H D hD v actor h)).2
    change O.calendar.age v = O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) at ht
    rw [actual_actor_cut_source] at ht
    rw [ht] at hlt
    exact False.elim (lt_irrefl _ hlt)
  | exit e =>
    change O.calendar.age (O.network.graph.source e) = O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) at ht
    rw [actual_actor_cut_source] at ht
    exact congrArg OriginalEvent.exit (actual_only_last_exit_at_end_date O _ _
      (actual_actor_cut_ends_at O H D hD actor) e (actual_owned_exit_member O H D hD e actor h) ht)

/-- Every owned source boundary is within the unique actor lifetime in the
literal finite original event order, including its opening/closing operation.
The open tag precedes that node; the close tag follows that exit. -/
theorem actual_private_site_between_interfaces (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (event : OriginalEvent O) (actor : BridgeActor T)
    (hm : event ∈ originalBoundaryTrace O) (h : eventActor O H D hD event = some actor) :
    (originalBoundaryTrace O).idxOf (.node (actorInput O D actor)) ≤ (originalBoundaryTrace O).idxOf event ∧
      (originalBoundaryTrace O).idxOf event ≤ (originalBoundaryTrace O).idxOf (.exit (actorCut O H D hD actor)) := by
  obtain ⟨hlo,hhi⟩ := actual_private_event_time_bounds O H D hD event actor h
  constructor
  · by_cases he : event = .node (actorInput O D actor)
    · rw [he]
    · have hlt : siteDate O (.node (actorInput O D actor)) < siteDate O event := by
        apply lt_of_le_of_ne hlo
        intro ht
        exact he (actual_private_event_at_opening O H D hD event actor h ht.symm)
      exact (strict_key_index_order _ _ (actual_boundary_trace_chronological O) _ _
        (actual_every_original_node_site O _) hm hlt).le
  · by_cases he : event = .exit (actorCut O H D hD actor)
    · rw [he]
    · have hlt : siteDate O event < siteDate O (.exit (actorCut O H D hD actor)) := by
        apply lt_of_le_of_ne hhi
        intro ht
        exact he (actual_private_event_at_closing O H D hD event actor h ht)
      exact (strict_key_index_order _ _ (actual_boundary_trace_chronological O) _ _ hm
        (actual_every_original_exit_site O _) hlt).le

#print axioms actual_private_site_between_interfaces
end G1PrivateActorLifetimeAdmission
