import NanuqActualRootedCapSwitching

/-! Cut readout on the actual rooted cap. A nonroot cap's fresh root only
subdivides its incoming-port attachment. Local port walks lift through that
root, preserving every internal cut occurrence. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

def actualRootedCapVertexLift (b : N.graph.Blob) :
    N.CappedBlobVertex b → N.RootedCapVertex b :=
  Sum.elim Sum.inl (fun p => Sum.inr (Sum.inl p))

namespace OriginalBlobSwitching
variable {N} {b : N.graph.Blob} (L : N.OriginalBlobSwitching b) (hb : N.NonleafBlob b)

noncomputable def rootedCapInternalEdge (f : L.InternalChoiceEdge) :
    (L.toActualRootedCapSwitching hb).Edge := ⟨Sum.inl f.val,f.property⟩

noncomputable def rootedCapPortEdge (p : N.BlobPort b) :
    (L.toActualRootedCapSwitching hb).Edge := ⟨Sum.inr (Sum.inl p),True.intro⟩

noncomputable def rootedCapStemEdge (t : N.RootedCapRootTag b) :
    (L.toActualRootedCapSwitching hb).Edge := ⟨Sum.inr (Sum.inr t),True.intro⟩

theorem rooted_cap_port_walk_without_internal (f : L.InternalChoiceEdge) (p : N.BlobPort b) :
    (L.toActualRootedCapSwitching hb).graph.ReachWithout (L.rootedCapInternalEdge hb f)
      (Sum.inl (N.originalPortInner b p)) (Sum.inr (Sum.inl p)) := by
  by_cases hp : N.graph.bridgeQuotient.source p.val = b
  · exact Relation.ReflTransGen.single ⟨L.rootedCapPortEdge hb p,
      (by intro h;cases congrArg Subtype.val h),Or.inl ⟨by simp [Switching.graph,
        rootedCapPortEdge,actualEveryNonleafRootedCapSource,actualRootedCapSource,
        actualRootedCapGraph,hp],rfl⟩⟩
  · have ht := p.property.resolve_left hp
    have hr : b ≠ N.graph.blobOf N.root := by
      intro h
      exact N.original_root_blob_has_no_incoming_port p.val (ht.trans h)
    have hi : N.originalIncomingBlobPort b hr = p :=
      N.original_incoming_port_unique b _ p (N.originalIncomingBlobPort_target b hr) ht
    have he : N.originalRootedCapEntry b = N.originalPortInner b p := by
      simp [originalRootedCapEntry,hr,hi]
    have hstem : (L.toActualRootedCapSwitching hb).graph.ReachWithout
        (L.rootedCapInternalEdge hb f) (Sum.inl (N.originalPortInner b p))
        (N.actualRootedCapRoot b) := by
      exact Relation.ReflTransGen.single ⟨L.rootedCapStemEdge hb ⟨(),hr⟩,
        (by intro h;cases congrArg Subtype.val h),Or.inr ⟨rfl,congrArg Sum.inl he⟩⟩
    exact hstem.tail ⟨L.rootedCapPortEdge hb p,
      (by intro h;cases congrArg Subtype.val h),Or.inl ⟨by simp [Switching.graph,
        rootedCapPortEdge,actualEveryNonleafRootedCapSource,actualRootedCapSource,
        actualRootedCapGraph,hp],rfl⟩⟩

theorem local_cap_internal_cut_walk_lifts (f : L.InternalChoiceEdge)
    {a c : N.CappedBlobVertex b}
    (h : L.localCappedGraph.ReachWithout (Sum.inl f) a c) :
    (L.toActualRootedCapSwitching hb).graph.ReachWithout (L.rootedCapInternalEdge hb f)
      (N.actualRootedCapVertexLift b a) (N.actualRootedCapVertexLift b c) := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨g,hg,hinc⟩ := hs
    rcases g with k | p
    · apply ih.tail
      refine ⟨L.rootedCapInternalEdge hb k,?_,?_⟩
      · intro he
        exact hg (congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val he))))
      · rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
        · exact Or.inl ⟨congrArg (N.actualRootedCapVertexLift b) hs,
            congrArg (N.actualRootedCapVertexLift b) ht⟩
        · exact Or.inr ⟨congrArg (N.actualRootedCapVertexLift b) hs,
            congrArg (N.actualRootedCapVertexLift b) ht⟩
    · have hw := L.rooted_cap_port_walk_without_internal hb f p
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact ih.trans (by
          change Sum.inl (N.originalPortInner b p) = v at hs
          change Sum.inr p = w at ht
          rw [← hs,← ht];exact hw)
      · exact ih.trans (by
          change Sum.inl (N.originalPortInner b p) = w at hs
          change Sum.inr p = v at ht
          rw [← hs,← ht];exact (L.toActualRootedCapSwitching hb).graph.ureach_symm hw)

theorem local_cap_oriented_quartet_lifts (f : L.InternalChoiceEdge)
    (a c d e : N.CappedBlobVertex b)
    (h : L.localCappedGraph.OrientedQuartet (Sum.inl f) a c d e) :
    (L.toActualRootedCapSwitching hb).graph.OrientedQuartet (L.rootedCapInternalEdge hb f)
      (N.actualRootedCapVertexLift b a) (N.actualRootedCapVertexLift b c)
      (N.actualRootedCapVertexLift b d) (N.actualRootedCapVertexLift b e) :=
  ⟨L.local_cap_internal_cut_walk_lifts hb f h.1,
    L.local_cap_internal_cut_walk_lifts hb f h.2.1,
    L.local_cap_internal_cut_walk_lifts hb f h.2.2.1,
    L.local_cap_internal_cut_walk_lifts hb f h.2.2.2⟩
end OriginalBlobSwitching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.OriginalBlobSwitching.local_cap_oriented_quartet_lifts
