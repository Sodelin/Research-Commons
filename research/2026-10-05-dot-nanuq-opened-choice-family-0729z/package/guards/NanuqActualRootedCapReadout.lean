import guards.NanuqActualRootedCapSwitching

set_option debug.skipKernelTC false

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

noncomputable def actualRootedCapQuartet (q : Fin 4 ↪ X) (b : N.graph.Blob)
    (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) : Fin 4 ↪ N.BlobPort b :=
  ⟨fun i => N.blobProjection b hb (q i),hinj⟩

namespace Switching
variable {N} (S : N.Switching)

theorem original_oriented_quartet_rooted_caps (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (f : S.Edge) (hf : S.graph.IsBridge f) (i j k l : Fin 4) (hkl : k ≠ l)
    (hcover : ∀ t : Fin 4, t = i ∨ t = j ∨ t = k ∨ t = l)
    (h : S.graph.OrientedQuartet f (N.leaf (q i)) (N.leaf (q j))
      (N.leaf (q k)) (N.leaf (q l))) :
    ∃ g : ((S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb).Edge,
      ((S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb).graph.IsBridge g ∧
      ((S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb).graph.OrientedQuartet g
        (N.actualRootedCapLeaf b (N.blobProjection b hb (q i)))
        (N.actualRootedCapLeaf b (N.blobProjection b hb (q j)))
        (N.actualRootedCapLeaf b (N.blobProjection b hb (q k)))
        (N.actualRootedCapLeaf b (N.blobProjection b hb (q l))) := by
  obtain ⟨g,_,_,hg⟩ := S.original_oriented_quartet_caps q b hb hinj f hf i j k l hkl hcover h
  let L := S.restrictOriginalBlobSwitching b
  let T := L.toActualRootedCapSwitching hb
  let eg := S.originalRestrictionInternalEquiv b g
  have hl := ((S.actualCappedBlobGraph b).oriented_quartet_edge_equiv_iff L.localCappedGraph
    (S.originalRestrictionCapEquiv b) (S.original_restriction_cap_source b)
    (S.original_restriction_cap_target b) (Sum.inl g) _ _ _ _).mp hg
  exact ⟨L.rootedCapInternalEdge hb eg,
    T.graph.uniqueIncoming_all_bridges T.selected_uniqueIncoming T.selected_acyclic _,
    L.local_cap_oriented_quartet_lifts hb eg _ _ _ _ hl⟩

theorem actual_rooted_cap_resolves_of_original (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (r : Nanuq.Quartet.Resolution) (h : S.graph.Resolves (fun i => N.leaf (q i)) r) :
    ((S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb).graph.Resolves
      (fun i => N.actualRootedCapLeaf b (N.blobProjection b hb (q i))) r := by
  cases r
  · obtain ⟨f,hf,h | h⟩ := h
    · obtain ⟨g,hg,hgq⟩ := S.original_oriented_quartet_rooted_caps q b hb hinj f hf 0 1 2 3
        (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨g,hg,Or.inl hgq⟩
    · obtain ⟨g,hg,hgq⟩ := S.original_oriented_quartet_rooted_caps q b hb hinj f hf 2 3 0 1
        (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨g,hg,Or.inr hgq⟩
  · obtain ⟨f,hf,h | h⟩ := h
    · obtain ⟨g,hg,hgq⟩ := S.original_oriented_quartet_rooted_caps q b hb hinj f hf 0 2 1 3
        (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨g,hg,Or.inl hgq⟩
    · obtain ⟨g,hg,hgq⟩ := S.original_oriented_quartet_rooted_caps q b hb hinj f hf 1 3 0 2
        (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨g,hg,Or.inr hgq⟩
  · obtain ⟨f,hf,h | h⟩ := h
    · obtain ⟨g,hg,hgq⟩ := S.original_oriented_quartet_rooted_caps q b hb hinj f hf 0 3 1 2
        (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨g,hg,Or.inl hgq⟩
    · obtain ⟨g,hg,hgq⟩ := S.original_oriented_quartet_rooted_caps q b hb hinj f hf 1 2 0 3
        (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨g,hg,Or.inr hgq⟩

theorem actual_rooted_cap_resolve_eq (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) :
    ((S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb).resolve
      (N.actualRootedCapQuartet q b hb hinj) = S.resolve q := by
  have h := S.actual_rooted_cap_resolves_of_original q b hb hinj (S.resolve q) (S.resolve_spec q)
  exact (((S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb).resolves_iff_eq_resolve
    (N.actualRootedCapQuartet q b hb hinj) (S.resolve q)).mp h |>.symm
end Switching

theorem actual_rooted_cap_switching_map_surjective (b : N.graph.Blob) (hb : N.NonleafBlob b) :
    Function.Surjective (fun S : N.Switching =>
      (S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb) := by
  intro T
  obtain ⟨S,hS⟩ := N.actual_blob_switching_restriction_surjective b T.fromActualRootedCapSwitching
  change S.restrictOriginalBlobSwitching b = T.fromActualRootedCapSwitching at hS
  refine ⟨S,?_⟩
  change (S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb = T
  rw [hS]
  exact T.from_to_actual_rooted_cap_roundtrip

theorem actual_four_port_rooted_cap_distinct_set_and_mean
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) :
    N.rawDisplayedQuartets q =
        (N.actualEveryNonleafRootedCapSource b hb).rawDisplayedQuartets
          (N.actualRootedCapQuartet q b hb hinj) ∧
      N.rawQuartetMean q = (N.actualEveryNonleafRootedCapSource b hb).rawQuartetMean
          (N.actualRootedCapQuartet q b hb hinj) := by
  let F := fun S : N.Switching =>
    (S.restrictOriginalBlobSwitching b).toActualRootedCapSwitching hb
  have hfun : (fun S : N.Switching => S.resolve q) =
      (fun T : (N.actualEveryNonleafRootedCapSource b hb).Switching =>
        T.resolve (N.actualRootedCapQuartet q b hb hinj)) ∘ F := by
    funext S
    exact (S.actual_rooted_cap_resolve_eq q b hb hinj).symm
  constructor
  · unfold rawDisplayedQuartets
    rw [hfun,Nanuq.Quartet.displayed_comp_surjective F
      (N.actual_rooted_cap_switching_map_surjective b hb)]
  · unfold rawQuartetMean
    rw [hfun,Nanuq.Quartet.sourceMean_comp_surjective F
      (N.actual_rooted_cap_switching_map_surjective b hb)]
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.OriginalBlobSwitching.local_cap_oriented_quartet_lifts

#print axioms Nanuq.Source.RootedBinary.Switching.actual_rooted_cap_resolve_eq

#print axioms Nanuq.Source.RootedBinary.actual_four_port_rooted_cap_distinct_set_and_mean
