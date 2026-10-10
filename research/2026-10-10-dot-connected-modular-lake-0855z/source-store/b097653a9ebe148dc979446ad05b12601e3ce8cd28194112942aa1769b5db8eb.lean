import G1ActualFinitePanelProgramTensor

/-! Physical actor opening sites are the ONLY retained nodes inside their
original recipe regions. Every remaining internal node is genuinely erased.
This is original-source calendar ownership, not an arbitrary actor assignment.
Contributor: dot, 2026-10-04. -/
namespace G1RetainedActorBoundarySites
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginalRecipePopulationOwnership
open G1ConcurrentSpanPhysicalSeparation G1ConstructedPopulationPartition
open G1OriginalNodeBatchBinding
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_recipe_input_original_population (O : Source X) (label : Recipe O) :
    ∃ population ∈ recipePopulations O label, O.network.graph.target population = label.input := by
  cases label with
  | raw e => exact ⟨e,Finset.mem_singleton_self _,rfl⟩
  | span a b word =>
      exact actual_span_node_has_incoming_population O word (actual_span_input_in_region O word)

lemma actual_current_input_original_population (O T : Source X) (D : Decoration O T) (e : T.Edge) :
    ∃ population ∈ recipePopulations O (D.recipe e),
      O.network.graph.target population = D.vertex (T.network.graph.target e) := by
  obtain ⟨population,hp,ht⟩ := actual_recipe_input_original_population O (D.recipe e)
  exact ⟨population,hp,ht.trans (D.endpoints e).1⟩

lemma actual_nonroot_has_incoming (T : Source X) (v : T.Vertex) (hv : v ≠ T.network.root) :
    ∃ e : T.Edge, T.network.graph.target e = v := by
  have hd : 0 < T.network.graph.inDegree v := by
    by_cases hleaf : ∃ x : X, T.network.leaf x = v
    · obtain ⟨x,rfl⟩ := hleaf
      rw [(T.network.leaf_degrees x).1]
      norm_num
    · have ht := T.network.internal_degrees v hv (fun x h => hleaf ⟨x,h⟩)
      rcases ht with ht | ht
      · rw [ht.1]; norm_num
      · rw [ht.1]; norm_num
  obtain ⟨e,he⟩ := Finset.card_pos.mp hd
  exact ⟨e,(Finset.mem_filter.mp he).2⟩

/-- Any retained original vertex in a bridge actor word must be that actor's
literal current descendant interface. Unique ORIGINAL population ownership
forces the incoming current edge to be this same bridge. -/
theorem actual_retained_actor_node_is_its_input (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (v : T.Vertex)
    (hv : D.vertex v ∈ nodeRegion O (bridgeSpan O T D e he)) : v = T.network.graph.target e := by
  have hne : v ≠ T.network.root := by
    intro hr
    have hn := actual_span_nodes_nonroot O (bridgeSpan O T D e he) (D.vertex v) hv
    exact hn ((congrArg D.vertex hr).trans D.root)
  obtain ⟨f,hf⟩ := actual_nonroot_has_incoming T v hne
  obtain ⟨population,hp,hpt⟩ := actual_current_input_original_population O T D f
  rw [hf] at hpt
  have hi : population ∈ G1OriginalNodeBatchBinding.incomingEdges O.network (D.vertex v) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpt⟩
  have hepop := actual_span_incoming_closed O (bridgeSpan O T D e he) (D.vertex v) hv hi
  rw [actual_bridge_span_populations] at hepop
  obtain ⟨owner,_,hunique⟩ := actual_originated_population_ownership O H D hD population
  have hfe : f = e := (hunique f hp).trans (hunique e hepop).symm
  exact hf.symm.trans (congrArg T.network.graph.target hfe)

/-- Deleted-node private operations cannot be mistaken for another retained
interface. This holds for every Source-derived core, independent of dates. -/
theorem actual_actor_internal_node_not_retained (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (v : O.Vertex)
    (hv : v ∈ nodeRegion O (bridgeSpan O T D e he))
    (hne : v ≠ D.vertex (T.network.graph.target e)) :
    ¬ ∃ kept : T.Vertex, D.vertex kept = v := by
  rintro ⟨kept,hkept⟩
  have hk := actual_retained_actor_node_is_its_input O H D hD e he kept (hkept ▸ hv)
  exact hne (hkept.symm.trans (congrArg D.vertex hk))

#print axioms actual_retained_actor_node_is_its_input
end G1RetainedActorBoundarySites
