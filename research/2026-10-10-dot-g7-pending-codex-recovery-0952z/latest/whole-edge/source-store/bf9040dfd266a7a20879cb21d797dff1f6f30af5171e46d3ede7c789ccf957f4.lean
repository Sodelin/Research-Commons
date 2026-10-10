import G1CutChildPorts
import Mathlib.Tactic.Ring

/-!
# Original blob degree balance and exact two-port vertex counts

Contributor: dot, 2026-10-03. Degree/port identities are counted on actual
original edge IDs, including parallel occurrences. Combined with the derived
cut-child hybrid-port injection, every nonroot two-port blob has exactly one
ordinary tree vertex and one hybrid vertex. No bounded core/shape is assumed.
-/
namespace G1BlobDegreeBalance
open Nanuq.Source G1CutChildPorts
open scoped Classical BigOperators
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def internalEdges (N : RootedBinary V E X) (b : N.graph.Blob) : Finset E :=
  Finset.univ.filter (fun e => ¬ N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.source e) = b)

noncomputable def sourceEdges (N : RootedBinary V E X) (b : N.graph.Blob) : Finset E :=
  Finset.univ.filter (fun e => N.graph.blobOf (N.graph.source e) = b)

noncomputable def targetEdges (N : RootedBinary V E X) (b : N.graph.Blob) : Finset E :=
  Finset.univ.filter (fun e => N.graph.blobOf (N.graph.target e) = b)

theorem actual_source_edge_partition (N : RootedBinary V E X) (b : N.graph.Blob) :
    sourceEdges N b = internalEdges N b ∪ outPorts N b := by
  ext e
  by_cases he : N.graph.IsBridge e <;> simp [sourceEdges,internalEdges,outPorts,he]

theorem actual_target_edge_partition (N : RootedBinary V E X) (b : N.graph.Blob) :
    targetEdges N b = internalEdges N b ∪ inPorts N b := by
  ext e
  by_cases he : N.graph.IsBridge e
  · simp [targetEdges,internalEdges,inPorts,he]
  · have hs : N.graph.blobOf (N.graph.source e) = N.graph.blobOf (N.graph.target e) :=
      Quotient.sound (N.graph.nonbridge_sameBlob he)
    simp [targetEdges,internalEdges,inPorts,he,hs]

lemma internal_out_disjoint (N : RootedBinary V E X) (b : N.graph.Blob) :
    Disjoint (internalEdges N b) (outPorts N b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp hf).2.1

lemma internal_in_disjoint (N : RootedBinary V E X) (b : N.graph.Blob) :
    Disjoint (internalEdges N b) (inPorts N b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp hf).2.1

theorem actual_blob_out_degree_count (N : RootedBinary V E X) (b : N.graph.Blob) :
    (∑ v ∈ blobVertices N b, N.graph.outDegree v) = (sourceEdges N b).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
    (blobVertices N b) N.graph.source
  simpa only [EdgeGraph.outDegree,blobVertices,Finset.mem_filter,Finset.mem_univ,true_and,sourceEdges] using h

theorem actual_blob_in_degree_count (N : RootedBinary V E X) (b : N.graph.Blob) :
    (∑ v ∈ blobVertices N b, N.graph.inDegree v) = (targetEdges N b).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
    (blobVertices N b) N.graph.target
  simpa only [EdgeGraph.inDegree,blobVertices,Finset.mem_filter,Finset.mem_univ,true_and,targetEdges] using h

/-- Internal arc counts cancel; every entering/exiting edge is its ORIGINAL
bridge occurrence. This equality is DERIVED for the actual blob vertex set. -/
theorem actual_blob_degree_balance (N : RootedBinary V E X) (b : N.graph.Blob) :
    (∑ v ∈ blobVertices N b, N.graph.outDegree v) + (inPorts N b).card =
      (∑ v ∈ blobVertices N b, N.graph.inDegree v) + (outPorts N b).card := by
  rw [actual_blob_out_degree_count,actual_blob_in_degree_count,
    actual_source_edge_partition,actual_target_edge_partition,
    Finset.card_union_of_disjoint (internal_out_disjoint N b),
    Finset.card_union_of_disjoint (internal_in_disjoint N b)]
  omega

noncomputable def blobTrees (N : RootedBinary V E X) (b : N.graph.Blob) : Finset V :=
  (blobVertices N b).filter (fun v => ¬ N.graph.IsHybrid v)

theorem actual_blob_vertex_partition (N : RootedBinary V E X) (b : N.graph.Blob) :
    blobVertices N b = blobTrees N b ∪ blobHybrids N b := by
  ext v
  by_cases hh : N.graph.IsHybrid v <;> simp [blobTrees,blobHybrids,blobVertices,hh]

theorem actual_tree_hybrid_disjoint (N : RootedBinary V E X) (b : N.graph.Blob) :
    Disjoint (blobTrees N b) (blobHybrids N b) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2.1

theorem actual_blob_vertex_count (N : RootedBinary V E X) (b : N.graph.Blob) :
    (blobVertices N b).card = (blobTrees N b).card + (blobHybrids N b).card := by
  rw [actual_blob_vertex_partition,Finset.card_union_of_disjoint (actual_tree_hybrid_disjoint N b)]

lemma actual_blob_tree_degrees (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hn : N.NonleafBlob b)
    (v : V) (hv : v ∈ blobTrees N b) : N.graph.inDegree v = 1 ∧ N.graph.outDegree v = 2 := by
  have hvm := (Finset.mem_filter.mp hv).1
  have hvb := (Finset.mem_filter.mp hvm).2
  have hvr : v ≠ N.root := by intro h; exact hb (h ▸ hvb).symm
  have hvl : ∀ x : X, N.leaf x ≠ v := by
    intro x hx
    exact hn x ((congrArg N.graph.blobOf hx).trans hvb)
  rcases N.internal_degrees v hvr hvl with ht | hh
  · exact ht
  · exact False.elim ((Finset.mem_filter.mp hv).2 hh)

theorem actual_nonroot_nonleaf_outdegree (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hn : N.NonleafBlob b) :
    (∑ v ∈ blobVertices N b, N.graph.outDegree v) =
      2 * (blobTrees N b).card + (blobHybrids N b).card := by
  rw [actual_blob_vertex_partition,Finset.sum_union (actual_tree_hybrid_disjoint N b)]
  have ht : ∑ v ∈ blobTrees N b, N.graph.outDegree v = (blobTrees N b).card * 2 :=
    Finset.sum_const_nat (fun v hv => (actual_blob_tree_degrees N b hb hn v hv).2)
  have hh : ∑ v ∈ blobHybrids N b, N.graph.outDegree v = (blobHybrids N b).card * 1 :=
    Finset.sum_const_nat (fun v hv => (Finset.mem_filter.mp hv).2.1.2)
  rw [ht,hh]
  omega

theorem actual_nonroot_nonleaf_indegree (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hn : N.NonleafBlob b) :
    (∑ v ∈ blobVertices N b, N.graph.inDegree v) =
      (blobTrees N b).card + 2 * (blobHybrids N b).card := by
  rw [actual_blob_vertex_partition,Finset.sum_union (actual_tree_hybrid_disjoint N b)]
  have ht : ∑ v ∈ blobTrees N b, N.graph.inDegree v = (blobTrees N b).card * 1 :=
    Finset.sum_const_nat (fun v hv => (actual_blob_tree_degrees N b hb hn v hv).1)
  have hh : ∑ v ∈ blobHybrids N b, N.graph.inDegree v = (blobHybrids N b).card * 2 :=
    Finset.sum_const_nat (fun v hv => (Finset.mem_filter.mp hv).2.1.1)
  rw [ht,hh]
  omega

theorem actual_blob_vertices_nonempty (N : RootedBinary V E X) (b : N.graph.Blob) :
    (blobVertices N b).Nonempty := by
  induction b using Quotient.inductionOn with
  | h v => exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩

theorem actual_nonroot_two_port_outgoing_one (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) :
    (outPorts N b).card = 1 := by
  have hi := actual_nonroot_incoming_port_one N b hb
  have ht := actual_port_count N b
  omega

theorem actual_nonroot_two_port_nonleaf (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) : N.NonleafBlob b := by
  have ho := actual_nonroot_two_port_outgoing_one N b hb hp
  have he : (outPorts N b).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e,he⟩ := he
  have he := (Finset.mem_filter.mp he).2
  intro x hx
  have hs : N.graph.blobOf (N.graph.source e) = N.graph.blobOf (N.leaf x) := he.2.trans hx.symm
  exact N.no_edge_source_leaf x e ((N.blobOf_leaf_eq_iff x (N.graph.source e)).mp hs)

/-- Exact actual vertex census, derived solely from binary degrees, bridge
quotient entry, and the accepted cut-child predicate. No blob shape premise. -/
theorem actual_nonroot_two_port_census (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) :
    (blobHybrids N b).card = 1 ∧ (blobTrees N b).card = 1 ∧ (blobVertices N b).card = 2 := by
  have hh := actual_nonroot_hybrid_port_bound N hc b hb
  have hi := actual_nonroot_incoming_port_one N b hb
  have ho := actual_nonroot_two_port_outgoing_one N b hb hp
  have hn := actual_nonroot_two_port_nonleaf N b hb hp
  have hd := actual_blob_degree_balance N b
  rw [actual_nonroot_nonleaf_outdegree N b hb hn,actual_nonroot_nonleaf_indegree N b hb hn] at hd
  have hv := actual_blob_vertex_count N b
  have hpv : 0 < (blobVertices N b).card := Finset.card_pos.mpr (actual_blob_vertices_nonempty N b)
  omega

end G1BlobDegreeBalance
