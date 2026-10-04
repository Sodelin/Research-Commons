import G1TaggedOriginalCalendar

/-! Original actor private sites lie between their actual retained ports.
The only private node at the opening date is the opening node, and the only
private exit at the closing date is the literal original final cut. -/
namespace G1OriginalActorTemporalFootprint
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1SpanRegionExitClosure
open G1OriginalSpanCalendarDecomposition G1OriginalSpanClosingPhase
open G1OriginatedClosingSourceAdmission G1OriginalActorOperationOwnership
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_span_node_temporal_bounds (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) :
    ∀ v ∈ nodeRegion O word, O.calendar.age a ≤ O.calendar.age v ∧ O.calendar.age v < O.calendar.age b := by
  induction word with
  | edge e _ =>
      intro v hv
      have hv := Finset.mem_singleton.mp hv
      subst v
      exact ⟨le_rfl,O.calendar.edge_older e⟩
  | bigon B =>
      intro v hv
      have hv := Finset.mem_singleton.mp hv
      subst v
      exact ⟨le_rfl,actual_span_dates_strict O.network O.calendar (.bigon B)⟩
  | append first last hfirst hlast =>
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨hlo,hhi⟩ := hfirst v hv
        exact ⟨hlo,hhi.trans (actual_span_dates_strict O.network O.calendar last)⟩
      · obtain ⟨hlo,hhi⟩ := hlast v hv
        exact ⟨(actual_span_dates_strict O.network O.calendar first).le.trans hlo,hhi⟩

lemma actual_only_input_node_at_start (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) :
    ∀ v ∈ nodeRegion O word, O.calendar.age v = O.calendar.age a → v = a := by
  induction word with
  | edge e _ => intro v hv _; exact Finset.mem_singleton.mp hv
  | bigon B => intro v hv _; exact Finset.mem_singleton.mp hv
  | append first last hfirst _ =>
      intro v hv hage
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hfirst v hv hage
      · have hbound := (actual_span_node_temporal_bounds O last v hv).1
        rw [hage] at hbound
        exact False.elim ((not_le_of_gt (actual_span_dates_strict O.network O.calendar first)) hbound)

lemma actual_span_exit_temporal_bounds (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) :
    ∀ e ∈ edgeRegion O word,
      O.calendar.age a < O.calendar.age (O.network.graph.source e) ∧
        O.calendar.age (O.network.graph.source e) ≤ O.calendar.age b := by
  intro e he
  have ht := actual_span_edge_target_inside O word e he
  exact ⟨(actual_span_node_temporal_bounds O word _ ht).1.trans_lt (O.calendar.edge_older e),
    actual_span_edge_source_age O word e he⟩

lemma actual_only_last_exit_at_end_date (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (cut : O.Edge) (hc : EndsAt O cut word) :
    ∀ e ∈ edgeRegion O word, O.calendar.age (O.network.graph.source e) = O.calendar.age b → e = cut := by
  intro e he hage
  rcases actual_span_edge_source_inside_or_end O word e he with hv | hv
  · have hlt := (actual_span_node_temporal_bounds O word _ hv).2
    rw [hage] at hlt
    exact False.elim (lt_irrefl _ hlt)
  · exact actual_only_last_edge_at_end O word cut hc e he hv

/-- Equal calendar ages are handled through actual port identity, rather
than a generic strict-crossing assumption on different actors. -/
theorem actual_actor_temporal_footprint (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) :
    (∀ v ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property),
      O.calendar.age (D.vertex (T.network.graph.target actor.val)) ≤ O.calendar.age v ∧
        O.calendar.age v < O.calendar.age (D.vertex (T.network.graph.source actor.val))) ∧
    (∀ e ∈ edgeRegion O (bridgeSpan O T D actor.val actor.property),
      O.calendar.age (D.vertex (T.network.graph.target actor.val)) < O.calendar.age (O.network.graph.source e) ∧
        O.calendar.age (O.network.graph.source e) ≤ O.calendar.age (D.vertex (T.network.graph.source actor.val))) :=
  ⟨actual_span_node_temporal_bounds O _,actual_span_exit_temporal_bounds O _⟩

#print axioms actual_actor_temporal_footprint
end G1OriginalActorTemporalFootprint
