import G1BlobDegreeBalance
import G1NonrootBigonKernel

/-!
# Actual nonroot two-port blobs are original parallel bigons

Contributor: dot, 2026-10-03. The fragment and its two original cut interfaces
are EXTRACTED from actual bridge-deletion blob membership, binary degrees,
LSA rooting and the accepted cut-child property. This removes the supplied
literal-shape premise from the local G1 component interface. Root-containing
blob exclusion is actual quotient membership, not merely upper != root.
-/
namespace G1ActualTwoPortBlob
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1BlobDegreeBalance G1NonrootBigonKernel
open scoped Classical BigOperators
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_two_port_vertex_witnesses (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) :
    ∃ u h : V, u ∈ blobTrees N b ∧ h ∈ blobHybrids N b ∧
      (∀ v, N.graph.blobOf v = b ↔ v = u ∨ v = h) := by
  have hs := actual_nonroot_two_port_census N hc b hb hp
  obtain ⟨u,hu,hunique⟩ := Finset.card_eq_one_iff_existsUnique.mp hs.2.1
  obtain ⟨h,hh,hhunique⟩ := Finset.card_eq_one_iff_existsUnique.mp hs.1
  refine ⟨u,h,hu,hh,?_⟩
  intro v
  constructor
  · intro hv
    have hm : v ∈ blobVertices N b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
    rw [actual_blob_vertex_partition] at hm
    rcases Finset.mem_union.mp hm with ht | hh
    · exact Or.inl (hunique v ht)
    · exact Or.inr (hhunique v hh)
  · rintro (rfl | rfl)
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    · exact (Finset.mem_filter.mp hh).2.2

lemma actual_hybrid_parents_exist (N : RootedBinary V E X) (h : V) (hh : N.graph.IsHybrid h) :
    ∃ H : GProgram.G2.OriginalHybridParents N, H.hybrid = h := by
  have hpos : 0 < (Finset.univ.filter (fun e : E => N.graph.target e = h)).card := by
    change 0 < N.graph.inDegree h
    rw [hh.1]
    decide
  obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
  have het := (Finset.mem_filter.mp he).2
  obtain ⟨f,hft,hfe⟩ := N.graph.hybrid_has_partner hh e
  exact ⟨⟨h,hh,e,f,het,hft,hfe.symm⟩,rfl⟩

lemma actual_two_port_fragment_exists (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) :
    ∃ B : NonrootBigon N,
      N.graph.blobOf B.upper = b ∧ N.graph.blobOf B.parents.hybrid = b ∧
      (∀ v, N.graph.blobOf v = b ↔ v = B.upper ∨ v = B.parents.hybrid) := by
  obtain ⟨u,h,hu,hh,hvertices⟩ := actual_two_port_vertex_witnesses N hc b hb hp
  have hub := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
  have hhb := (Finset.mem_filter.mp hh).2.2
  have hhy := (Finset.mem_filter.mp hh).2.1
  obtain ⟨H,hH⟩ := actual_hybrid_parents_exist N h hhy
  have huroot : u ≠ N.root := by intro hr; exact hb (hr ▸ hub).symm
  have hsource : ∀ bit, N.graph.source (H.parent bit) = u := by
    intro bit
    have ht : N.graph.target (H.parent bit) = h := by
      cases bit <;> simp [GProgram.G2.OriginalHybridParents.parent,H.target0,H.target1,hH]
    have hn : ¬ N.graph.IsBridge (H.parent bit) := actual_hybrid_parent_nonbridge N _ (ht ▸ hhy)
    have hsb : N.graph.blobOf (N.graph.source (H.parent bit)) = b :=
      (Quotient.sound (N.graph.nonbridge_sameBlob hn)).trans (ht ▸ hhb)
    rcases (hvertices _).mp hsb with hs | hs
    · exact hs
    · exact False.elim (N.graph.acyclic_no_loop N.acyclic (H.parent bit) (hs.trans ht.symm))
  let B : NonrootBigon N := ⟨H,u,huroot,hsource⟩
  refine ⟨B,hub,?_,?_⟩
  · exact hH ▸ hhb
  · intro v
    simpa only [B,hH] using hvertices v

lemma actual_two_port_internal_count (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) :
    (internalEdges N b).card = 2 := by
  have hs := actual_nonroot_two_port_census N hc b hb hp
  have ho := actual_nonroot_two_port_outgoing_one N b hb hp
  have hd := actual_blob_out_degree_count N b
  rw [actual_nonroot_nonleaf_outdegree N b hb (actual_nonroot_two_port_nonleaf N b hb hp),
    actual_source_edge_partition,Finset.card_union_of_disjoint (internal_out_disjoint N b)] at hd
  omega

lemma edge_pair_exhaustive {A : Type*} [DecidableEq A] (s : Finset A) (e f : A)
    (hne : e ≠ f) (he : e ∈ s) (hf : f ∈ s) (hcard : s.card = 2) :
    ∀ g ∈ s, g = e ∨ g = f := by
  have hsub : ({e,f} : Finset A) ⊆ s := by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨he,hf⟩
  have hp : ({e,f} : Finset A).card = 2 := by simp [hne]
  have hs : ({e,f} : Finset A) = s := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro g hg
  rw [← hs] at hg
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hg

/-- A constructed graph-extraction witness, never a supplied source premise. -/
structure ActualBlobBigon (N : RootedBinary V E X) (b : N.graph.Blob) where
  fragment : NonrootBigon N
  upper_in_blob : N.graph.blobOf fragment.upper = b
  hybrid_in_blob : N.graph.blobOf fragment.parents.hybrid = b
  vertices_exact : ∀ v, N.graph.blobOf v = b ↔ v = fragment.upper ∨ v = fragment.parents.hybrid
  entry : E
  entry_bridge : N.graph.IsBridge entry
  entry_target : N.graph.target entry = fragment.upper
  entry_source_outside : N.graph.blobOf (N.graph.source entry) ≠ b
  child : E
  child_bridge : N.graph.IsBridge child
  child_source : N.graph.source child = fragment.parents.hybrid
  child_target_outside : N.graph.blobOf (N.graph.target child) ≠ b
  internal_edges_exact : ∀ e, e ∈ internalEdges N b ↔
    e = fragment.parents.parent0 ∨ e = fragment.parents.parent1

/-- Every actual nonroot two-port blob is EXACTLY an original parallel bigon
with one original entering cut edge and one original hybrid-child cut edge.
It lies entirely outside the actual root-containing bridge-deletion blob. -/
theorem actual_nonroot_two_port_blob_extraction (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) :
    Nonempty (ActualBlobBigon N b) := by
  obtain ⟨B,hU,hH,hvertices⟩ := actual_two_port_fragment_exists N hc b hb hp
  have hi := actual_nonroot_incoming_port_one N b hb
  obtain ⟨entry,he,heunique⟩ := Finset.card_eq_one_iff_existsUnique.mp hi
  have he := (Finset.mem_filter.mp he).2
  have het : N.graph.target entry = B.upper := by
    rcases (hvertices _).mp he.2 with h | h
    · exact h
    · have hh : N.graph.IsHybrid (N.graph.target entry) := h ▸ B.parents.isHybrid
      exact False.elim (actual_hybrid_parent_nonbridge N entry hh he.1)
  let child := hybridChild N B.parents.hybrid B.parents.isHybrid
  have hcs : N.graph.source child = B.parents.hybrid := hybridChild_source N _ _
  have hcb : N.graph.IsBridge child := hc child (hcs ▸ B.parents.isHybrid)
  have hInternal0 : B.parents.parent0 ∈ internalEdges N b := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · exact actual_hybrid_parent_nonbridge N _ (B.parents.target0 ▸ B.parents.isHybrid)
    · exact (congrArg N.graph.blobOf (B.arm_sources false)).trans hU
  have hInternal1 : B.parents.parent1 ∈ internalEdges N b := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · exact actual_hybrid_parent_nonbridge N _ (B.parents.target1 ▸ B.parents.isHybrid)
    · exact (congrArg N.graph.blobOf (B.arm_sources true)).trans hU
  refine ⟨⟨B,hU,hH,hvertices,entry,he.1,het,?_,child,hcb,hcs,?_,?_⟩⟩
  · intro hs
    exact N.graph.bridge_blob_ne he.1 (hs.trans he.2.symm)
  · intro ht
    exact N.graph.bridge_blob_ne hcb (((congrArg N.graph.blobOf hcs).trans hH).trans ht.symm)
  · intro e
    constructor
    · exact edge_pair_exhaustive _ _ _ B.parents.different hInternal0 hInternal1
        (actual_two_port_internal_count N hc b hb hp) e
    · rintro (rfl | rfl)
      · exact hInternal0
      · exact hInternal1

noncomputable def extractedBigon (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hp : (allPorts N b).card = 2) :
    ActualBlobBigon N b := Classical.choice (actual_nonroot_two_port_blob_extraction N hc b hb hp)

end G1ActualTwoPortBlob
