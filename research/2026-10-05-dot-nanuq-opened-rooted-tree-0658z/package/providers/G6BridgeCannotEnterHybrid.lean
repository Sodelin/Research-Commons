import G5MinimalGraphInterface
import G2LiveLineageRouting

/-!
# Original bridge targets have one incoming edge occurrence

Dedicated Sol6.1 source-graph contribution. Rootedness and directed acyclicity
force every underlying bridge target to have a unique incoming original edge
ID. Parallel same-parent arcs remain distinct edge occurrences. No planar,
galled, child-cut, LSA or biological-kernel conclusion is assumed in the generic
lemma. Binary source consequences support the separate nonplanar G6 proof.
-/

namespace GProgram.G6.BridgeEntry

open Nanuq.Source

variable {V E : Type*}

theorem bridge_incoming_unique (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e : E}
    (he : G.IsBridge e) {f : E} (hf : G.target f = G.target e) : f = e := by
  classical
  by_contra hne
  have hs : G.ReachWithout e (G.target e) (G.source f) :=
    G.ureach_single ⟨f,hne,Or.inr ⟨rfl,hf⟩⟩
  have hd := (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr he (G.source f)).mp hs
  exact ha (G.source f) (Relation.TransGen.head' ⟨f,rfl,hf⟩ hd)

theorem bridge_target_indegree_one (G : EdgeGraph V E) (root : V)
    [Fintype E] [DecidableEq V] (ha : G.Acyclic) (hr : ∀ v, G.DReach root v)
    {e : E} (he : G.IsBridge e) : G.inDegree (G.target e) = 1 := by
  classical
  unfold EdgeGraph.inDegree
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨e,by simp,?_⟩
  intro f hf
  exact bridge_incoming_unique G root ha hr he (Finset.mem_filter.mp hf).2

/-- Any two distinct incoming edge OCCURRENCES exclude a bridge, even if their
sources are the same vertex. This does not require binarity or finite vertices. -/
theorem two_incoming_occurrences_not_bridge (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e f : E}
    (hne : f ≠ e) (hf : G.target f = G.target e) : ¬ G.IsBridge e := by
  intro he
  exact hne (bridge_incoming_unique G root ha hr he hf)

/-- Distinct bridge edge occurrences have distinct downstream entry vertices.
This provides distinct child-cut targets/ports without a planar embedding. -/
theorem bridge_targets_injective (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) :
    Function.Injective (fun e : {e : E // G.IsBridge e} => G.target e.val) := by
  intro e f hf
  apply Subtype.ext
  exact (bridge_incoming_unique G root ha hr e.property hf.symm).symm

section OriginalSource

variable {X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem original_bridge_target_not_hybrid (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) : ¬ N.graph.IsHybrid (N.graph.target e) := by
  intro hh
  have hc := bridge_target_indegree_one N.graph N.root N.acyclic N.rooted he
  have ht : N.graph.inDegree (N.graph.target e) = 2 := hh.1
  rw [hc] at ht
  cases ht

theorem incoming_hybrid_edge_not_bridge (N : RootedBinary V E X)
    {e : E} (hh : N.graph.IsHybrid (N.graph.target e)) : ¬ N.graph.IsBridge e := by
  intro he
  exact original_bridge_target_not_hybrid N he hh

theorem original_hybrid_parents_nonbridge {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) :
    ¬ N.graph.IsBridge H.parent0 ∧ ¬ N.graph.IsBridge H.parent1 := by
  constructor
  · apply incoming_hybrid_edge_not_bridge N
    simpa only [H.target0] using H.isHybrid
  · apply incoming_hybrid_edge_not_bridge N
    simpa only [H.target1] using H.isHybrid

end OriginalSource

#print axioms bridge_targets_injective
#print axioms bridge_incoming_unique
#print axioms bridge_target_indegree_one
#print axioms two_incoming_occurrences_not_bridge
#print axioms original_bridge_target_not_hybrid
#print axioms original_hybrid_parents_nonbridge

end GProgram.G6.BridgeEntry
