import SmallBlob
import PortAttachmentLabels
import G6BridgeCannotEnterHybrid

/-! UNCOMPILED original singleton-blob case. No Jordan curve, galledness,
port-attachment injectivity, or geometric order premise is introduced. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.SmallBlob
open Nanuq.Source Nanuq.RawBlock Nanuq.PortAttachmentLabels
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (b : N.graph.Blob)
variable (v : BlobVertex N.graph b) (hall : ∀ w : BlobVertex N.graph b, w=v)

theorem singleton_no_hybrid : ¬ N.graph.IsHybrid v.val := by
  classical
  intro hh
  have hpos : 0<(Finset.univ.filter (fun e => N.graph.target e=v.val)).card := by
    change 0<N.graph.inDegree v.val
    rw [hh.1]
    decide
  obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
  have ht : N.graph.target e=v.val := (Finset.mem_filter.mp he).2
  have hnb : ¬N.graph.IsBridge e :=
    GProgram.G6.BridgeEntry.incoming_hybrid_edge_not_bridge N (by simpa only [ht] using hh)
  have hs : N.graph.blobOf (N.graph.source e)=b :=
    (Quotient.sound (N.graph.nonbridge_sameBlob hnb)).trans (by simpa only [ht] using v.property)
  have hempty := singleton_no_edges N b v hall
  exact hempty.false ⟨e,hnb,hs⟩

theorem singleton_port_card_le_three : Fintype.card (N.BlobPort b)≤3 := by
  classical
  let I : Finset E := Finset.univ.filter
    (fun e => N.graph.source e=v.val ∨ N.graph.target e=v.val)
  let f : N.BlobPort b → ↥I := fun p => ⟨p.val.val,by
    have h := port_id_incident N b p
    have hi : (N.originalPortInner b p).val=v.val := congrArg Subtype.val (hall _)
    simpa [I,hi] using h⟩
  have hf : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val hpq))
  have hcard := Fintype.card_le_of_injective f hf
  have hb := binary_incidence_bound N v.val
  have hset : {e | N.graph.source e=v.val ∨ N.graph.target e=v.val}=(I : Set E) := by
    ext e; simp [I]
  rw [hset,Set.ncard_coe_finset] at hb
  have hi : Fintype.card ↥I=I.card := Fintype.card_coe I
  omega

theorem singleton_nonleaf_port_card (hb : N.NonleafBlob b) :
    Fintype.card (N.BlobPort b)=2 ∨ Fintype.card (N.BlobPort b)=3 := by
  have hlo := N.actual_nonleaf_blob_has_two_ports b hb
  have hhi := singleton_port_card_le_three N b v hall
  omega

theorem singleton_no_four_distinct_ports : IsEmpty (Fin 4 ↪ N.BlobPort b) := by
  refine ⟨fun q => ?_⟩
  have hlo := Fintype.card_le_of_injective q q.injective
  have hhi := singleton_port_card_le_three N b v hall
  simp only [Fintype.card_fin] at hlo
  omega

#print axioms singleton_no_hybrid
#print axioms singleton_nonleaf_port_card
#print axioms singleton_no_four_distinct_ports
end Nanuq.SmallBlob
