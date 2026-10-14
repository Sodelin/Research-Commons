import G1ReducedCoreCounts
import G1BinaryCoreBudgets

/-! Source-only census of actual nonroot two-port exceptions.
This is a graph statement about every original RootedBinary CutChild source.
It does not bound the exceptional set by protected marks or certificate
supports. Those physical decomposition obligations remain separate. -/
namespace Astra.TwoPortExceptionCount

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source G1CutChildPorts G1ReducedQuotientGeometry G1ReducedCoreCounts
open G1BinaryCoreBudgets
open scoped Classical BigOperators

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Actual exceptional blobs, not an externally supplied graph budget. -/
noncomputable def twoPortBlobs (N : RootedBinary V E X) : Finset N.graph.Blob :=
  (internalBlobs N).filter (fun b => Fintype.card (N.BlobPort b) = 2)

lemma nonroot_branching_of_not_two (N : RootedBinary V E X)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (hn : N.NonleafBlob b)
    (hne : Fintype.card (N.BlobPort b) ≠ 2) : 2 ≤ (outPorts N b).card := by
  have hp := actual_nonleaf_outport_positive N b hn
  have hi := actual_nonroot_incoming_port_one N b hb
  have ha := actual_port_count N b
  have hq := actual_quotient_port_card N b
  omega

lemma internal_outport_with_exception (N : RootedBinary V E X)
    (b : N.graph.Blob) (hb : b ∈ internalBlobs N) :
    2 ≤ (outPorts N b).card +
      (if Fintype.card (N.BlobPort b) = 2 then 1 else 0) := by
  have hi := (Finset.mem_filter.mp hb).2
  by_cases hp : Fintype.card (N.BlobPort b) = 2
  · have ho := actual_nonleaf_outport_positive N b hi.2
    simp only [hp, if_true]
    omega
  · simpa only [hp, if_false, Nat.add_zero] using
      nonroot_branching_of_not_two N b hi.1 hi.2 hp

/-- The selected quotient census extends to arbitrary sources by charging
one unit for each actual unary internal quotient vertex. -/
theorem actual_internal_blob_exception_budget (N : RootedBinary V E X) :
    (internalBlobs N).card + 2 ≤ Fintype.card X + (twoPortBlobs N).card := by
  have hu : (∑ b ∈ internalBlobs N,
      if Fintype.card (N.BlobPort b) = 2 then 1 else 0) =
      (twoPortBlobs N).card := by
    simp [twoPortBlobs]
  have hi : 2 * (internalBlobs N).card ≤
      (∑ b ∈ internalBlobs N, (outPorts N b).card) + (twoPortBlobs N).card := by
    have h := Finset.sum_le_sum (s := internalBlobs N) (f := fun _ => 2)
      (g := fun b => (outPorts N b).card +
        if Fintype.card (N.BlobPort b) = 2 then 1 else 0)
      (fun b hb => internal_outport_with_exception N b hb)
    simpa only [Finset.sum_add_distrib, hu, Finset.sum_const,
      smul_eq_mul, Nat.mul_comm] using h
  have hd : Disjoint {N.graph.blobOf N.root} (internalBlobs N) := by
    apply Finset.disjoint_left.mpr
    intro b hb hi
    exact (Finset.mem_filter.mp hi).2.1 (Finset.mem_singleton.mp hb)
  have hs : {N.graph.blobOf N.root} ∪ internalBlobs N ⊆
      (Finset.univ : Finset N.graph.Blob) := Finset.subset_univ _
  have ht := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun b => (outPorts N b).card) hs (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_union hd, Finset.sum_singleton] at ht
  have hr := actual_root_blob_outports_two N
  have hb := actual_total_blob_census N
  have he := actual_bridge_blob_census N
  have ho := actual_total_outport_census N
  omega

/-- Parallel occurrences and the actual hybrid-child injection are retained.
No reduced target, law identity or assumed hybrid bound is an input. -/
theorem actual_hybrid_exception_budget (N : RootedBinary V E X) (hc : CutChild N) :
    (hybrids N).card + 2 ≤ 2 * Fintype.card X + (twoPortBlobs N).card := by
  have hh := Fintype.card_le_of_injective (hybridBridge N hc)
    (actual_hybrid_bridge_injective N hc)
  simp only [Fintype.card_coe] at hh
  have hi := actual_internal_blob_exception_budget N
  have hb := actual_total_blob_census N
  have he := actual_bridge_blob_census N
  omega

/-- Division-free natural-number form of the corresponding binary census.
Turning the actual exceptional set into a protected/support bound is not
asserted here. -/
theorem actual_vertex_edge_exception_budget (N : RootedBinary V E X) (hc : CutChild N) :
    Fintype.card V + 5 ≤ 6 * Fintype.card X + 2 * (twoPortBlobs N).card ∧
      Fintype.card E + 8 ≤ 8 * Fintype.card X + 3 * (twoPortBlobs N).card := by
  have hh := actual_hybrid_exception_budget N hc
  obtain ⟨hv, he⟩ := actual_binary_vertex_edge_census N
  constructor <;> omega

-- Future actual type/axiom audit requests, not execution evidence.
#check actual_internal_blob_exception_budget
#check actual_hybrid_exception_budget
#check actual_vertex_edge_exception_budget
#print axioms actual_internal_blob_exception_budget
#print axioms actual_hybrid_exception_budget
#print axioms actual_vertex_edge_exception_budget

end Astra.TwoPortExceptionCount
