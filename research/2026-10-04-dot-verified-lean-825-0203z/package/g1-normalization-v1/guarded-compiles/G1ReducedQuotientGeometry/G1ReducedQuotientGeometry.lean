import G1ActualGraphNormalization
import GraphPortConsequences

/-! Actual blob-quotient branching and edge census. Contributor: dot,
2026-10-03. Reducedness is the literal absence of nonroot two-port blobs;
all branching and count consequences are derived from graph/LSA data. -/
namespace G1ReducedQuotientGeometry
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ActualGraphNormalization
open scoped Classical BigOperators
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

lemma actual_root_no_incoming_bridge (N : RootedBinary V E X) (e : N.graph.BridgeEdge) :
    N.graph.bridgeQuotient.target e ≠ N.graph.blobOf N.root := by
  intro ht
  exact N.blob_quotient_acyclic _
    (Relation.TransGen.tail' (N.blob_quotient_rooted (N.graph.bridgeQuotient.source e)) ⟨e,rfl,ht⟩)

lemma actual_nonleaf_outport_positive (N : RootedBinary V E X) (b : N.graph.Blob)
    (hn : N.NonleafBlob b) : 0 < (outPorts N b).card := by
  apply Finset.card_pos.mpr
  refine Quotient.inductionOn b ?_ hn
  intro v hn
  obtain ⟨x,hx⟩ := N.every_vertex_reaches_leaf v
  have hp := N.graph.dreach_projects_to_blobs hx
  rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c,⟨e,hs,ht⟩,hrest⟩
  · exact False.elim (hn x heq.symm)
  · exact ⟨e.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property,hs⟩⟩

/-- The whole original root blob branches at least twice. LSA supplies a
source-side taxon for any chosen outgoing bridge, forcing a SECOND port. -/
theorem actual_root_blob_outports_two (N : RootedBinary V E X) :
    2 ≤ (outPorts N (N.graph.blobOf N.root)).card := by
  let b := N.graph.blobOf N.root
  have hn : N.NonleafBlob b := N.blob_leaf_ne_root
  obtain ⟨e,he⟩ := Finset.card_pos.mp (actual_nonleaf_outport_positive N b hn)
  have he' := (Finset.mem_filter.mp he).2
  let edge : N.graph.BridgeEdge := ⟨e,he'.1⟩
  obtain ⟨x,hx⟩ := N.bridge_source_side_contains_taxon e
  let p := N.blobProjection b hn x
  have hp : N.graph.bridgeQuotient.source p.val = b := by
    rcases p.property with hs | ht
    · exact hs
    · exact False.elim (actual_root_no_incoming_bridge N p.val ht)
  have hpout : p.val.val ∈ outPorts N b :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.val.property,hp⟩
  have hne : e ≠ p.val.val := by
    intro h
    have hep : edge = p.val := Subtype.ext h
    have hspec := N.blobProjection_spec b hn x
    have hsource : N.graph.bridgeQuotient.ReachWithout p.val b (N.blobLeaf x) := by
      have hproj := N.graph.reach_projects_without edge hx
      rw [he'.2,hep] at hproj
      exact hproj
    rcases hspec with ⟨_,htarget⟩ | ⟨ht,_⟩
    · exact N.graph.bridgeQuotient.bridge_sides_disjoint (N.graph.quotient_edge_is_bridge p.val)
        (by simpa only [hp] using hsource) htarget
    · exact actual_root_no_incoming_bridge N p.val ht
  have hsubset : {e,p.val.val} ⊆ outPorts N b := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact he
    · exact Finset.mem_singleton.mp hf ▸ hpout
  have hcard := Finset.card_le_card hsubset
  simpa [hne] using hcard

/-- Every nonroot nonleaf reduced blob has at least two ACTUAL outgoing
bridges. A single outgoing bridge would be an actual two-port blob. -/
theorem actual_reduced_nonroot_branching (N : RootedBinary V E X)
    (hr : ∀ b : N.graph.Blob, b ≠ N.graph.blobOf N.root → Fintype.card (N.BlobPort b) ≠ 2)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hn : N.NonleafBlob b) :
    2 ≤ (outPorts N b).card := by
  have hp := actual_nonleaf_outport_positive N b hn
  have hi := actual_nonroot_incoming_port_one N b hb
  have ha := actual_port_count N b
  have hq := actual_quotient_port_card N b
  have hx := hr b hb
  omega

/-- Every actual quotient edge has a distinct nonroot target; all nonroot
blobs are hit. The quotient edge census is derived, not a tree-size field. -/
noncomputable def actualBridgeTargetEquiv (N : RootedBinary V E X) :
    N.graph.BridgeEdge ≃ {b : N.graph.Blob // b ≠ N.graph.blobOf N.root} :=
  Equiv.ofBijective (fun e => ⟨N.graph.bridgeQuotient.target e,actual_root_no_incoming_bridge N e⟩) (by
    constructor
    · intro e f h
      exact N.blob_quotient_uniqueIncoming e f (congrArg Subtype.val h)
    · intro b
      rcases Relation.ReflTransGen.cases_tail (N.blob_quotient_rooted b.val) with h | ⟨a,_,e,hs,ht⟩
      · exact False.elim (b.property h)
      · exact ⟨e,Subtype.ext ht⟩)

theorem actual_bridge_blob_census (N : RootedBinary V E X) :
    Fintype.card N.graph.BridgeEdge + 1 = Fintype.card N.graph.Blob := by
  have h := Fintype.card_congr (actualBridgeTargetEquiv N)
  have hc := Fintype.card_subtype_compl (fun b : N.graph.Blob => b = N.graph.blobOf N.root)
  have hp : Fintype.card {b : N.graph.Blob // b = N.graph.blobOf N.root} = 1 := by simp
  rw [hp] at hc
  have hn : 1 ≤ Fintype.card N.graph.Blob := Fintype.card_pos_iff.mpr ⟨N.graph.blobOf N.root⟩
  change Fintype.card N.graph.BridgeEdge = Fintype.card {b : N.graph.Blob // ¬ b = N.graph.blobOf N.root} at h
  omega

end G1ReducedQuotientGeometry
