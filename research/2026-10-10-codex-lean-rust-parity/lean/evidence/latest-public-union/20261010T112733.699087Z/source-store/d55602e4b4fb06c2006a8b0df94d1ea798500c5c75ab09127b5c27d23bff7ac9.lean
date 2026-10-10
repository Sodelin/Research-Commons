import G1SpliceLSA
import Mathlib.Data.Fintype.Sum

/-!
# Constructed LSA-rooted binary cut-child core splice

Contributor: dot, 2026-10-03. The actual reduced RootedBinary graph is built
from the proved splice degrees, reachability, acyclicity and LSA. Cut-child
and the unchanged original calendar on retained nodes are derived. Exact
vertex/edge decrements provide termination for repeated graph normalization.
Its synthetic edge is a SOURCE-DERIVED DECORATED edge, not an ordinary scalar
demographic replacement. No probability/kernel equality is assumed here.
-/
namespace G1SplicedSourceAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint
open G1BigonSpliceGraph G1SpliceCutTransport G1SpliceRootBlob G1SpliceDegrees G1SpliceLSA
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Every source-graph admission field below is proved for the constructed
splice. Original taxa and root retain their original identity. -/
noncomputable def splicedNetwork (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    RootedBinary (SplicedVertex N b A) (SplicedEdge N b A) X where
  graph := spliceGraph N hc b A
  root := retainedRoot N b hb A
  leaf := retainedTaxa N b A
  at_least_two_taxa := N.at_least_two_taxa
  root_degrees := by
    rw [actual_splice_indegree,actual_splice_outdegree]
    exact N.root_degrees
  leaf_degrees x := by
    rw [actual_splice_indegree,actual_splice_outdegree]
    exact N.leaf_degrees x
  internal_degrees v hv hleaf := by
    have hvr : v.val ≠ N.root := by intro h; exact hv (Subtype.ext h)
    have hvl : ∀ x : X, N.leaf x ≠ v.val := by
      intro x h
      exact hleaf x (Subtype.ext h)
    rcases N.internal_degrees v.val hvr hvl with ht | hh
    · exact Or.inl ⟨by rw [actual_splice_indegree]; exact ht.1,
        by rw [actual_splice_outdegree]; exact ht.2⟩
    · exact Or.inr ((actual_splice_hybrid_iff N hc b A v).mpr hh)
  acyclic := actual_splice_acyclic N hc b A
  rooted := actual_splice_rooted N hc b hb A
  least_stable := actual_splice_least_stable N hc b hb A

theorem actual_spliced_cut_child (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    CutChild (splicedNetwork N hc b hb A) := by
  intro e hh
  change (spliceGraph N hc b A).IsHybrid ((spliceGraph N hc b A).source e) at hh
  change (spliceGraph N hc b A).IsBridge e
  cases e with
  | inr u => cases u; exact actual_new_edge_bridge N hc b A
  | inl e =>
      have hhy := (actual_splice_hybrid_iff N hc b A ((spliceGraph N hc b A).source (.inl e))).mp hh
      exact (actual_retained_bridge_iff N hc b A e).mpr (hc e.val hhy)

/-- The retained-node calendar is literally the original one. The synthetic
edge spans the actual original entry/arm/child dates; no new node ages exist. -/
noncomputable def splicedCalendar (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (C : Calendar N.graph) : Calendar (splicedNetwork N hc b hb A).graph where
  age v := C.age v.val
  edge_older e := by
    cases e with
    | inl e => exact C.edge_older e.val
    | inr u =>
        have he := C.edge_older A.entry
        have hp := C.edge_older A.fragment.parents.parent0
        have hd := C.edge_older A.child
        rw [A.entry_target] at he
        rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false,
          A.fragment.parents.target0] at hp
        rw [A.child_source] at hd
        exact hd.trans (hp.trans he)

theorem actual_splice_vertex_decrement (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Fintype.card (SplicedVertex N b A) + 2 = Fintype.card V := by
  have hp := Fintype.card_subtype_eq_or_eq_of_ne (actual_upper_hybrid_distinct N b A)
  have hc := Fintype.card_subtype_compl (fun v : V => v = A.fragment.upper ∨ v = A.fragment.parents.hybrid)
  have hle := Fintype.card_subtype_le (fun v : V => v = A.fragment.upper ∨ v = A.fragment.parents.hybrid)
  rw [hp] at hc hle
  have hcore : Fintype.card (SplicedVertex N b A) = Fintype.card V - 2 := by
    simpa only [Fintype.card_subtype,not_or,SplicedVertex] using hc
  omega

theorem actual_splice_strictly_smaller (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Fintype.card (SplicedVertex N b A) < Fintype.card V := by
  have h := actual_splice_vertex_decrement N b A
  omega

theorem actual_splice_edge_decrement (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Fintype.card (SplicedEdge N b A) + 3 = Fintype.card E := by
  have hm : Fintype.card {e : E // e ∈ removedEdges N b A} = 4 := by
    simpa only [Fintype.card_coe] using actual_four_removed_edges N b A
  have hc := Fintype.card_subtype_compl (fun e : E => e ∈ removedEdges N b A)
  rw [hm] at hc
  have hret : Fintype.card (RetainedEdge N b A) = Fintype.card E - 4 := hc
  have hge : 4 ≤ Fintype.card E := by
    have h := Finset.card_le_univ (removedEdges N b A)
    rwa [actual_four_removed_edges] at h
  have hsum : Fintype.card (SplicedEdge N b A) = Fintype.card (RetainedEdge N b A) + 1 := by
    simp only [SplicedEdge,Fintype.card_sum,Fintype.card_unit]
  omega

end G1SplicedSourceAdmission
