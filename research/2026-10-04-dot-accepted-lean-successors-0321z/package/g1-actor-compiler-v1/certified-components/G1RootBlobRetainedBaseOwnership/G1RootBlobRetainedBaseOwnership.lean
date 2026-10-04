import G1OriginalActorOperationOwnership

/-! The ENTIRE original root-containing blob belongs to the retained base,
with actual raw original edge IDs. No private actor replaces root-blob nodes,
edges, registers or history. Contributor: dot, 2026-10-04. -/
namespace G1RootBlobRetainedBaseOwnership
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1DecoratedRootBlobRetention G1OriginalRecipePopulationOwnership
open G1RetainedActorBoundarySites G1OriginalActorOperationOwnership
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_original_root_blob_node_has_no_actor_owner (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (node : O.Vertex) (hn : O.network.graph.SameBlob O.network.root node) :
    nodeActorOwner O H D hD node = none := by
  have hnot : ¬ ∃ actor : BridgeActor T, node ∈ nodeRegion O (G1DecoratedOriginalProvenance.bridgeSpan O T D actor.val actor.property) := by
    rintro ⟨actor,ha⟩
    obtain ⟨kept,hkept,hv⟩ := D.rootBlob_surjective node hn
    have hk := actual_retained_actor_node_is_its_input O H D hD actor.val actor.property kept (hv ▸ ha)
    rw [hk] at hkept
    exact GProgram.G5.ComponentEntries.bridge_target_not_root_component T.network.graph T.network.root
      T.network.acyclic T.network.rooted actor.property (T.network.graph.sameBlob_symm hkept)
  rw [nodeActorOwner,dif_neg hnot]

lemma actual_root_blob_edge_nonbridge (O : Source X) (population : O.Edge)
    (hs : O.network.graph.SameBlob O.network.root (O.network.graph.source population))
    (ht : O.network.graph.SameBlob O.network.root (O.network.graph.target population)) :
    ¬ O.network.graph.IsBridge population := by
  intro hbridge
  exact hbridge (GProgram.G5.ComponentEntries.sameBlob_avoids_bridge O.network.graph hbridge
    ((O.network.graph.sameBlob_symm hs).trans ht))

/-- Every original root-blob population has its original raw retained-base
owner; a source-generated bridge actor can never absorb that population. -/
theorem actual_original_root_blob_population_retained_base (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (population : O.Edge)
    (hs : O.network.graph.SameBlob O.network.root (O.network.graph.source population))
    (ht : O.network.graph.SameBlob O.network.root (O.network.graph.target population)) :
    D.recipe (populationOwner O H D hD population) = .raw population ∧
      ¬ T.network.graph.IsBridge (populationOwner O H D hD population) := by
  obtain ⟨edge,hraw⟩ := actual_original_root_blob_raw_edges_survive O H D hD population hs ht
  have hp : population ∈ recipePopulations O (D.recipe edge) := by
    rw [hraw]
    exact Finset.mem_singleton_self _
  have ho := actual_population_owner_unique O H D hD population edge hp
  rw [←ho]
  exact ⟨hraw,fun hb => actual_root_blob_edge_nonbridge O population hs ht ((D.raw_bridge edge population hraw).mp hb)⟩

#print axioms actual_original_root_blob_node_has_no_actor_owner
#print axioms actual_original_root_blob_population_retained_base
end G1RootBlobRetainedBaseOwnership
