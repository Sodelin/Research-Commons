import guards.NanuqActualAnchorPatterns
import guards.NanuqActualQuartetPortBranching

set_option debug.skipKernelTC false

/-! Original-source anchor identity for four distinct taxa, with each local
entry evaluated on the admitted actual rooted cap. Port-count alternatives,
three-port bridge values and four-port cap equality are all derived. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical BigOperators
open Nanuq.PortPatterns
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def actualBlobTupleMean (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (v : Fin 4 → X) : ℚ :=
  if hi : Function.Injective (fun i => N.blobProjection b hb (v i)) then
    (N.actualEveryNonleafRootedCapSource b hb).rawQuartetMean
      ⟨fun i => N.blobProjection b hb (v i),hi⟩ else 0

noncomputable def actualBlobTupleAnchor (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (v : Fin 4 → X) : ℚ :=
  tupleAnchor (fun i => N.blobProjection b hb (v i)) (N.actualBlobTupleMean b hb v)

theorem actual_blob_anchor_by_port_count (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b) :
    N.actualBlobTupleAnchor b hb q =
      (if portCount (fun i => N.blobProjection b hb (q i)) = 4 then 2 else 0) * N.rawQuartetMean q +
      (if portCount (fun i => N.blobProjection b hb (q i)) = 3 then 1 else 0) * N.rawQuartetMean q := by
  let f := fun i => N.blobProjection b hb (q i)
  change tupleAnchor f (N.actualBlobTupleMean b hb q) =
    (if portCount f = 4 then 2 else 0) * N.rawQuartetMean q +
    (if portCount f = 3 then 1 else 0) * N.rawQuartetMean q
  by_cases h4 : portCount f = 4
  · have hi := (portCount_four_iff_injective f).mp h4
    have h3 : portCount f ≠ 3 := by omega
    have hm : N.actualBlobTupleMean b hb q = N.rawQuartetMean q := by
      unfold actualBlobTupleMean
      rw [dif_pos hi]
      exact (N.actual_four_port_rooted_cap_distinct_set_and_mean q b hb hi).2.symm
    change tupleAnchor f (N.actualBlobTupleMean b hb q) = _
    rw [tupleAnchor_injective f _ hi,hm]
    simp [h4]
  · by_cases h3 : portCount f = 3
    · have ha := N.actual_three_port_anchor_value q b hb (N.actualBlobTupleMean b hb q) h3
      change tupleAnchor f (N.actualBlobTupleMean b hb q) = _
      rw [ha]
      simp [h3]
    · have hc : portCount f ≤ 2 := by have h := portCount_le_four f;omega
      change tupleAnchor f (N.actualBlobTupleMean b hb q) = _
      rw [tupleAnchor_at_most_two f _ hc]
      simp [h4,h3]

theorem actual_distinct_anchor_identity (q : Fin 4 ↪ X) :
    2 * N.rawQuartetMean q =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b}, N.actualBlobTupleAnchor b.val b.property q := by
  simp_rw [N.actual_blob_anchor_by_port_count q]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul]
  have h4 : (∑ b : {b : N.graph.Blob // N.NonleafBlob b},
      if portCount (fun i => N.blobProjection b.val b.property (q i)) = 4 then (2 : ℚ) else 0) =
      ((Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (fun i => N.blobProjection b.val b.property (q i)) = 4)).card : ℚ) * 2 := by
    simp [← Finset.sum_filter]
  have h3 : (∑ b : {b : N.graph.Blob // N.NonleafBlob b},
      if portCount (fun i => N.blobProjection b.val b.property (q i)) = 3 then (1 : ℚ) else 0) =
      ((Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (fun i => N.blobProjection b.val b.property (q i)) = 3)).card : ℚ) := by
    simp [← Finset.sum_filter]
  rw [h4,h3]
  rcases N.actual_quartet_blob_port_branching q with ⟨hc4,hc3⟩ | ⟨hc4,hc3⟩
  · rw [hc4,hc3];simp
  · rw [hc4,hc3];simp
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_distinct_anchor_identity
