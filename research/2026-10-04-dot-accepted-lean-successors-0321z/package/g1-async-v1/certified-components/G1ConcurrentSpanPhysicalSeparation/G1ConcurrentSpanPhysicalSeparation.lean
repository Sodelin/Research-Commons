import G1ConstructedPopulationPartition

/-! Concurrent source-derived span actors have disjoint ORIGINAL populations
and nonterminal node sites. This separation is derived from physical recipe
ownership, not from temporal non-overlap. -/
namespace G1ConcurrentSpanPhysicalSeparation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1ConstructedPopulationPartition
open G1JointSeparatedSourceGeometry
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_span_node_has_incoming_population (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) {v : O.Vertex} (hv : v ∈ nodeRegion O word) :
    ∃ population ∈ edgeRegion O word, O.network.graph.target population = v := by
  induction word with
  | edge e _ =>
      have h : v = O.network.graph.target e := Finset.mem_singleton.mp hv
      exact ⟨e,Finset.mem_singleton_self _,h.symm⟩
  | bigon B =>
      have h : v = B.parents.hybrid := Finset.mem_singleton.mp hv
      exact ⟨B.parents.parent0,Finset.mem_insert_self _ _,B.parents.target0.trans h.symm⟩
  | append first last ihf ihl =>
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨e,he,het⟩ := ihf hv
        exact ⟨e,Finset.mem_union_left _ he,het⟩
      · obtain ⟨e,he,het⟩ := ihl hv
        exact ⟨e,Finset.mem_union_right _ he,het⟩

lemma actual_disjoint_span_populations_disjoint_nodes (O : Source X)
    {a b c d : O.Vertex} (first : OriginalSpan O.network a b) (second : OriginalSpan O.network c d)
    (h : Disjoint (edgeRegion O first) (edgeRegion O second)) :
    Disjoint (nodeRegion O first) (nodeRegion O second) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨e,he,het⟩ := actual_span_node_has_incoming_population O first hv
  have hew := actual_span_incoming_closed O second v hw
    (Finset.mem_filter.mpr ⟨Finset.mem_univ e,het⟩)
  exact Finset.disjoint_left.mp h he hew

theorem actual_distinct_originated_bridge_locations_disjoint (O : Source X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (hf : T.network.graph.IsBridge f) (hef : e ≠ f) (p : Location O.Vertex O.Edge) :
    ¬ (SpanLocation O (bridgeSpan O T D e he) p ∧ SpanLocation O (bridgeSpan O T D f hf) p) := by
  have hp := actual_distinct_originated_bridge_regions_disjoint O H D hD e f he hf hef
  have hn := actual_disjoint_span_populations_disjoint_nodes O _ _ hp
  cases p with
  | node v => exact fun h => Finset.disjoint_left.mp hn h.1 h.2
  | edge g => exact fun h => Finset.disjoint_left.mp hp h.1 h.2
  | rootPopulation v => exact fun h => h.1

/-- At any real or abstract source state whose two panels occupy their own
actual span regions, their complete original populations are separated. No
age non-overlap, descendant leaf cap or desired independence is assumed. -/
theorem actual_concurrent_originated_span_panel_separator (O : Source X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (hf : T.network.graph.IsBridge f) (hef : e ≠ f)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (left right : Finset Copy)
    (hl : ∀ x ∈ left, SpanLocation O (bridgeSpan O T D e he) (copyLocation (state s) x))
    (hr : ∀ x ∈ right, SpanLocation O (bridgeSpan O T D f hf) (copyLocation (state s) x)) :
    PopulationSeparated (state s) left right := by
  intro x hx y hy hpop
  exact actual_distinct_originated_bridge_locations_disjoint O H D hD e f he hf hef _
    ⟨hl x hx,hpop ▸ hr y hy⟩

#print axioms actual_concurrent_originated_span_panel_separator
end G1ConcurrentSpanPhysicalSeparation
