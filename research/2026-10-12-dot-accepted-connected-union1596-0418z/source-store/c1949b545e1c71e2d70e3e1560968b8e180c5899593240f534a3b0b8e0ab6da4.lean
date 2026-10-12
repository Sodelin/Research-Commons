import G1OriginatedNeutralSpanRegion

/-! Original span populations close under every nonclosing original exit.
Contributor: dot, 2026-10-03. Strict original dates prevent any earlier word
edge from sharing the final upper date or masquerading as its last cut. -/
namespace G1SpanRegionExitClosure
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanRegion
open G1OriginalSpanCalendarDecomposition G1OriginalSpanClosingPhase
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_span_edge_source_age (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    ∀ e ∈ edgeRegion O word, O.calendar.age (O.network.graph.source e) ≤ O.calendar.age b := by
  induction word with
  | edge f _ =>
      intro e he
      have he : e = f := Finset.mem_singleton.mp he
      subst e; rfl
  | bigon B =>
      intro e he
      rcases (by simpa only [edgeRegion,Finset.mem_insert,Finset.mem_singleton] using he :
        e = B.parents.parent0 ∨ e = B.parents.parent1) with rfl | rfl
      · rw [show O.network.graph.source B.parents.parent0 = B.upper from B.arm_sources false]
      · rw [show O.network.graph.source B.parents.parent1 = B.upper from B.arm_sources true]
  | append first last hfirst hlast =>
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact (hfirst e he).trans (actual_span_dates_strict O.network O.calendar last).le
      · exact hlast e he

lemma actual_span_edge_source_inside_or_end (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    ∀ e ∈ edgeRegion O word, O.network.graph.source e ∈ nodeRegion O word ∨ O.network.graph.source e = b := by
  induction word with
  | edge f _ =>
      intro e he
      have he : e = f := Finset.mem_singleton.mp he
      subst e; exact Or.inr rfl
  | bigon B =>
      intro e he
      rcases (by simpa only [edgeRegion,Finset.mem_insert,Finset.mem_singleton] using he :
        e = B.parents.parent0 ∨ e = B.parents.parent1) with rfl | rfl
      · exact Or.inr (B.arm_sources false)
      · exact Or.inr (B.arm_sources true)
  | append first last hfirst hlast =>
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · rcases hfirst e he with hp | hp
        · exact Or.inl (Finset.mem_union_left _ hp)
        · apply Or.inl
          rw [hp]
          exact Finset.mem_union_right _ (actual_span_input_in_region O last)
      · rcases hlast e he with hp | hp
        · exact Or.inl (Finset.mem_union_right _ hp)
        · exact Or.inr hp

lemma actual_only_last_edge_at_end (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (lastEdge : O.Edge) (hlast : EndsAt O lastEdge word) :
    ∀ e ∈ edgeRegion O word, O.network.graph.source e = b → e = lastEdge := by
  induction word with
  | edge f _ =>
      intro e he _
      exact (Finset.mem_singleton.mp he).trans hlast
  | bigon _ => exact False.elim hlast
  | append first last _ ihlast =>
      intro e he hsource
      rcases Finset.mem_union.mp he with he | he
      · have hle := actual_span_edge_source_age O first e he
        rw [hsource] at hle
        exact False.elim ((not_le_of_gt (actual_span_dates_strict O.network O.calendar last)) hle)
      · exact ihlast hlast e he hsource

lemma actual_nonclosing_exit_stays_inside (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (lastEdge : O.Edge) (hlast : EndsAt O lastEdge word) :
    ∀ e ∈ edgeRegion O word, e ≠ lastEdge → O.network.graph.source e ∈ nodeRegion O word := by
  intro e he hne
  rcases actual_span_edge_source_inside_or_end O word e he with hp | hp
  · exact hp
  · exact False.elim (hne (actual_only_last_edge_at_end O word lastEdge hlast e he hp))

end G1SpanRegionExitClosure
