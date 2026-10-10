import G1RetainedActorBoundarySites

/-! Every original population/node operation has a source-derived physical
actor or retained-base owner. No manual schedule assignment or desired kernel
law occurs in these compiler ownership definitions. -/
namespace G1OriginalActorOperationOwnership
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginalRecipePopulationOwnership
open G1ConcurrentSpanPhysicalSeparation G1ConstructedPopulationPartition G1RetainedActorBoundarySites
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

abbrev BridgeActor (T : Source X) := {edge : T.Edge // T.network.graph.IsBridge edge}

noncomputable def populationOwner (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (population : O.Edge) : T.Edge :=
  Classical.choose (actual_originated_population_ownership O H D hD population)

lemma actual_population_owner_spec (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (population : O.Edge) :
    population ∈ recipePopulations O (D.recipe (populationOwner O H D hD population)) :=
  (Classical.choose_spec (actual_originated_population_ownership O H D hD population)).1

lemma actual_population_owner_unique (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (population : O.Edge) (edge : T.Edge)
    (he : population ∈ recipePopulations O (D.recipe edge)) :
    edge = populationOwner O H D hD population :=
  (Classical.choose_spec (actual_originated_population_ownership O H D hD population)).2 edge he

noncomputable def nodeActorOwner (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (node : O.Vertex) : Option (BridgeActor T) :=
  if h : ∃ actor : BridgeActor T, node ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property) then
    some (Classical.choose h)
  else none

lemma actual_node_actor_unique (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (node : O.Vertex)
    (first second : BridgeActor T)
    (hf : node ∈ nodeRegion O (bridgeSpan O T D first.val first.property))
    (hs : node ∈ nodeRegion O (bridgeSpan O T D second.val second.property)) : first = second := by
  apply Subtype.ext
  by_contra hne
  have hedge := actual_distinct_originated_bridge_regions_disjoint O H D hD _ _ first.property second.property hne
  exact Finset.disjoint_left.mp (actual_disjoint_span_populations_disjoint_nodes O _ _ hedge) hf hs

lemma actual_node_actor_owner_of_member (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (node : O.Vertex) (actor : BridgeActor T)
    (ha : node ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property)) :
    nodeActorOwner O H D hD node = some actor := by
  have hw : ∃ a : BridgeActor T, node ∈ nodeRegion O (bridgeSpan O T D a.val a.property) := ⟨actor,ha⟩
  rw [nodeActorOwner,dif_pos hw]
  exact congrArg some (actual_node_actor_unique O H D hD node _ actor (Classical.choose_spec hw) ha)

/-- Every ORIGINAL node either survives literally or belongs to the finite
original word of an actual core bridge. This covers deleted internal nodes,
without adding a source graph partition as an assumption. -/
theorem actual_original_node_retained_or_actor (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (node : O.Vertex) :
    (∃ kept : T.Vertex, D.vertex kept = node) ∨
      ∃ actor : BridgeActor T, node ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property) := by
  by_cases hr : node = O.network.root
  · exact Or.inl ⟨T.network.root,D.root.trans hr.symm⟩
  obtain ⟨population,hpt⟩ := actual_nonroot_has_incoming O node hr
  let edge := populationOwner O H D hD population
  have hp := actual_population_owner_spec O H D hD population
  by_cases hb : T.network.graph.IsBridge edge
  · right
    refine ⟨⟨edge,hb⟩,?_⟩
    have he : population ∈ edgeRegion O (bridgeSpan O T D edge hb) := by
      rw [actual_bridge_span_populations]
      exact hp
    rw [←hpt]
    exact actual_span_edge_target_inside O _ population he
  · left
    obtain ⟨raw,hraw⟩ := D.raw_nonbridge edge hb
    have hpraw : population = raw := by
      change population ∈ recipePopulations O (D.recipe edge) at hp
      rw [hraw] at hp
      exact Finset.mem_singleton.mp hp
    have ht := (D.endpoints edge).1
    rw [hraw] at ht
    change O.network.graph.target raw = D.vertex (T.network.graph.target edge) at ht
    exact ⟨T.network.graph.target edge,ht.symm.trans ((congrArg O.network.graph.target hpraw).symm.trans hpt)⟩

theorem actual_unowned_node_is_retained (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (node : O.Vertex) (hn : nodeActorOwner O H D hD node = none) :
    ∃ kept : T.Vertex, D.vertex kept = node := by
  rcases actual_original_node_retained_or_actor O H D hD node with h | ⟨actor,ha⟩
  · exact h
  · rw [actual_node_actor_owner_of_member O H D hD node actor ha] at hn
    cases hn

/-- The original root is always a retained-base event; the entire retained
root blob is handled by the unchanged source semantics and history. -/
theorem actual_original_root_has_no_actor_owner (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    nodeActorOwner O H D hD O.network.root = none := by
  have hn : ¬ ∃ actor : BridgeActor T, O.network.root ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property) := by
    rintro ⟨actor,ha⟩
    exact actual_span_nodes_nonroot O _ _ ha rfl
  rw [nodeActorOwner,dif_neg hn]

#print axioms actual_original_node_retained_or_actor
#print axioms actual_original_root_has_no_actor_owner
end G1OriginalActorOperationOwnership
