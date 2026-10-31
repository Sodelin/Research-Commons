import ContextCut
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

def LabelledQuartet (G : EdgeGraph V E) (label : V → Nat) (a b c d : Nat) : Prop :=
  ∃ w x y z, (G.outDegree w=0 ∧ G.outDegree x=0 ∧ G.outDegree y=0 ∧ G.outDegree z=0) ∧
    (label w=a ∧ label x=b ∧ label y=c ∧ label z=d) ∧ G.HasQuartet w x y z

/-- The label map need not be injective: all terminal occurrences and all
original edge witnesses are retained, before adjacent-copy order is addressed. -/
theorem actual_labelled_witness_iff {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    {t : BinarySyntax V} (ht : Represents G t root) (label : V → Nat) (a b c d : Nat) :
    LabelledQuartet G label a b c d ↔ (encode label t).Witness [] a b c d := by
  rw [encode_witness_iff]
  constructor
  · rintro ⟨w,x,y,z,⟨hw,hx,hy,hz⟩,⟨lw,lx,ly,lz⟩,e,he,hq⟩
    obtain ⟨u,hu,hrep⟩ := edge_has_subtree ht e ((ht.mem_nodes_iff _).mpr (hr _))
    obtain ⟨inner,hctx⟩ := below_context hu
    have hp := (context_partition_for_edge ha hui root hr ht hctx e hrep).2.2
    refine ⟨u,inner,hctx,?_⟩
    simp only [List.append_nil]
    rcases hq with h | h
    · exact Or.inr ⟨List.mem_map.mpr ⟨w,(hp w hw).2.mp h.1,lw⟩,
        List.mem_map.mpr ⟨x,(hp x hx).2.mp h.2.1,lx⟩,
        List.mem_map.mpr ⟨y,(hp y hy).1.mp h.2.2.1,ly⟩,
        List.mem_map.mpr ⟨z,(hp z hz).1.mp h.2.2.2,lz⟩⟩
    · exact Or.inl ⟨List.mem_map.mpr ⟨w,(hp w hw).1.mp h.2.2.1,lw⟩,
        List.mem_map.mpr ⟨x,(hp x hx).1.mp h.2.2.2,lx⟩,
        List.mem_map.mpr ⟨y,(hp y hy).2.mp h.1,ly⟩,
        List.mem_map.mpr ⟨z,(hp z hz).2.mp h.2.1,lz⟩⟩
  · rintro ⟨u,inner,hctx,hcut⟩
    simp only [List.append_nil] at hcut
    rcases hctx.eq_or_below with ⟨hroot,hout⟩ | hu
    · simp [hout,Cut] at hcut
    · obtain ⟨e,hrep⟩ := subtree_has_edge ht hu
      obtain ⟨hsu,hso,hp⟩ := context_partition_for_edge ha hui root hr ht hctx e hrep
      rcases hcut with h | h
      · obtain ⟨w,hw,lw⟩ := List.mem_map.mp h.1
        obtain ⟨x,hx,lx⟩ := List.mem_map.mp h.2.1
        obtain ⟨y,hy,ly⟩ := List.mem_map.mp h.2.2.1
        obtain ⟨z,hz,lz⟩ := List.mem_map.mp h.2.2.2
        exact ⟨w,x,y,z,⟨hsu w hw,hsu x hx,hso y hy,hso z hz⟩,⟨lw,lx,ly,lz⟩,
          e,all_edges_bridge G ha hui e,Or.inr ⟨(hp y (hso y hy)).2.mpr hy,
          (hp z (hso z hz)).2.mpr hz,(hp w (hsu w hw)).1.mpr hw,(hp x (hsu x hx)).1.mpr hx⟩⟩
      · obtain ⟨w,hw,lw⟩ := List.mem_map.mp h.1
        obtain ⟨x,hx,lx⟩ := List.mem_map.mp h.2.1
        obtain ⟨y,hy,ly⟩ := List.mem_map.mp h.2.2.1
        obtain ⟨z,hz,lz⟩ := List.mem_map.mp h.2.2.2
        exact ⟨w,x,y,z,⟨hso w hw,hso x hx,hsu y hy,hsu z hz⟩,⟨lw,lx,ly,lz⟩,
          e,all_edges_bridge G ha hui e,Or.inl ⟨(hp w (hso w hw)).2.mpr hw,
          (hp x (hso x hx)).2.mpr hx,(hp y (hsu y hy)).1.mpr hy,(hp z (hsu z hz)).1.mpr hz⟩⟩

#print axioms actual_labelled_witness_iff
end Nanuq.GraphReceiver
