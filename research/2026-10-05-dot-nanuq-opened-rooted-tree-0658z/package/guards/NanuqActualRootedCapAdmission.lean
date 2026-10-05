import guards.NanuqActualRootedCapPaths

set_option debug.skipKernelTC false

/-! Full binary rooted LSA admission for the literal original-ID cap. The
root-blob LSA proof truncates an actual original avoiding path at its first
port exit; nonroot blobs have a fresh binary root with the incoming-port tip
as a second branch. No desired local quartet row or admission certificate
is assumed. Root-suppression/readout identification remains separate. -/
namespace Nanuq.Source.EdgeGraph
variable {A F : Type*} [Fintype F] [DecidableEq A] (G : EdgeGraph A F)

theorem dreach_avoids_distinct_sink {blocked a c : A}
    (hz : G.outDegree blocked = 0) (ha : a ≠ blocked) (hc : c ≠ blocked)
    (h : G.DReach a c) : G.AvoidReach blocked a c := by
  revert hc
  induction h with
  | refl => intro hc;exact ⟨ha,hc,.refl⟩
  | @tail u v hp hs ih =>
      intro hv
      have hu : u ≠ blocked := by
        intro heq
        obtain ⟨e,he,_⟩ := hs
        exact G.no_edge_source_of_outdegree_zero hz e (he.trans heq)
      exact ⟨ha,hv,(ih hu).2.2.tail ⟨hs,hu,hv⟩⟩
end Nanuq.Source.EdgeGraph

namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_inside_avoiding_walk_or_port (b : N.graph.Blob)
    (blocked start : N.OriginalBlobVertex b) (hne : start.val ≠ blocked.val)
    {v : V} (h : Relation.ReflTransGen
      (fun a c => N.graph.DStep a c ∧ a ≠ blocked.val ∧ c ≠ blocked.val) start.val v) :
    (∃ hv : N.graph.blobOf v = b,
      (N.actualRootedCapGraph b).AvoidReach (Sum.inl blocked) (Sum.inl start) (Sum.inl ⟨v,hv⟩)) ∨
      ∃ p : N.BlobPort b, (N.actualRootedCapGraph b).AvoidReach
        (Sum.inl blocked) (Sum.inl start) (N.actualRootedCapLeaf b p) := by
  induction h with
  | refl =>
      have hn : Sum.inl start ≠ (Sum.inl blocked : N.RootedCapVertex b) := by
        intro heq
        exact hne (congrArg Subtype.val (Sum.inl.inj heq))
      exact Or.inl ⟨start.property,hn,hn,.refl⟩
  | @tail u w hp hs ih =>
      rcases ih with ⟨hu,hav⟩ | hex
      · obtain ⟨e,he,ht⟩ := hs.1
        have hes : N.graph.blobOf (N.graph.source e) = b :=
          (congrArg N.graph.blobOf he).trans hu
        by_cases hw : N.graph.blobOf w = b
        · let f : N.OriginalBlobArc b := ⟨e,hes,by rw [ht];exact hw⟩
          have hn : Sum.inl ⟨w,hw⟩ ≠ (Sum.inl blocked : N.RootedCapVertex b) := by
            intro heq
            exact hs.2.2 (congrArg Subtype.val (Sum.inl.inj heq))
          exact Or.inl ⟨hw,hav.1,hn,hav.2.2.tail
            ⟨⟨Sum.inl f,congrArg Sum.inl (Subtype.ext he),
              congrArg Sum.inl (Subtype.ext ht)⟩,hav.2.1,hn⟩⟩
        · have het : N.graph.blobOf (N.graph.target e) ≠ b := by
            rw [ht];exact hw
          let p : N.BlobPort b :=
            ⟨⟨e,N.original_arc_leaving_blob_bridge b e hes het⟩,Or.inl hes⟩
          have hcs : (N.actualRootedCapGraph b).source (Sum.inr (Sum.inl p)) =
              Sum.inl ⟨u,hu⟩ :=
            (if_pos (show N.graph.bridgeQuotient.source p.val = b from hes)).trans
              (congrArg Sum.inl (Subtype.ext
                ((N.originalPortInner_value_outgoing b p hes).trans he)))
          have hn : N.actualRootedCapLeaf b p ≠ Sum.inl blocked := by
            intro heq;cases heq
          exact Or.inr ⟨p,hav.1,hn,hav.2.2.tail
            ⟨⟨Sum.inr (Sum.inl p),hcs,rfl⟩,hav.2.1,hn⟩⟩
      · exact Or.inr hex

theorem actual_root_blob_cap_inner_avoids_some_port (b : N.graph.Blob)
    (hb : N.NonleafBlob b) (hr : b = N.graph.blobOf N.root)
    (a : N.OriginalBlobVertex b) (ha : a.val ≠ N.root) :
    ∃ p : N.BlobPort b, (N.actualRootedCapGraph b).AvoidReach
      (Sum.inl a) (N.actualRootedCapRoot b) (N.actualRootedCapLeaf b p) := by
  obtain ⟨x,hx⟩ := N.exists_leaf_avoiding_of_ne_root ha
  let r : N.OriginalBlobVertex b := ⟨N.root,hr.symm⟩
  have h := N.actual_inside_avoiding_walk_or_port b a r hx.1 hx.2.2
  rcases h with ⟨hxblob,_⟩ | ⟨p,hp⟩
  · exact False.elim (hb x hxblob)
  · exact ⟨p,by simpa [actualRootedCapRoot,hr,r] using hp⟩

theorem actual_nonroot_cap_inner_avoids_incoming_tip (b : N.graph.Blob)
    (hr : b ≠ N.graph.blobOf N.root) (a : N.OriginalBlobVertex b) :
    (N.actualRootedCapGraph b).AvoidReach (Sum.inl a) (N.actualRootedCapRoot b)
      (N.actualRootedCapLeaf b (N.originalIncomingBlobPort b hr)) := by
  let p := N.originalIncomingBlobPort b hr
  have hp := N.originalRootedCapIncoming_outside_source b hr
  have hn : N.actualRootedCapRoot b ≠ Sum.inl a := by
    intro h
    exact hr (N.actualRootedCapRoot_inner_implies_root_blob b a h)
  have ht : N.actualRootedCapLeaf b p ≠ Sum.inl a := by intro h;cases h
  exact ⟨hn,ht,Relation.ReflTransGen.single
    ⟨⟨Sum.inr (Sum.inl p),if_neg hp,rfl⟩,hn,ht⟩⟩

theorem actual_rooted_cap_least_stable (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hc : 2 ≤ Fintype.card (N.BlobPort b)) :
    ∀ a : N.RootedCapVertex b,
      (∀ p, (N.actualRootedCapGraph b).Dominates (N.actualRootedCapRoot b) a
        (N.actualRootedCapLeaf b p)) → a = N.actualRootedCapRoot b := by
  intro a hd
  rcases a with a | (p | t)
  · by_cases hr : b = N.graph.blobOf N.root
    · by_cases ha : a.val = N.root
      · simp [actualRootedCapRoot,hr]
        exact Subtype.ext ha
      · obtain ⟨p,hp⟩ := N.actual_root_blob_cap_inner_avoids_some_port b hb hr a ha
        exact False.elim (hd p hp)
    · exact False.elim (hd (N.originalIncomingBlobPort b hr)
        (N.actual_nonroot_cap_inner_avoids_incoming_tip b hr a))
  · obtain ⟨q,hq⟩ := Fintype.exists_ne_of_one_lt_card
      (Nat.lt_of_lt_of_le (by decide : 1 < 2) hc) p
    have hn : N.actualRootedCapLeaf b q ≠ N.actualRootedCapLeaf b p := by
      intro h
      exact hq ((N.actualRootedCapLeaf b).injective h)
    exact False.elim (hd q ((N.actualRootedCapGraph b).dreach_avoids_distinct_sink
      (N.actual_rooted_cap_leaf_degrees b p).2
      (N.actualRootedCapRoot_ne_port_tip b p) hn (N.actual_rooted_cap_rooted b _)))
  · simp [actualRootedCapRoot,t.property]

noncomputable def actualRootedCapSource (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hc : 2 ≤ Fintype.card (N.BlobPort b)) :
    RootedBinary (N.RootedCapVertex b) (N.RootedCapArc b) (N.BlobPort b) where
  graph := N.actualRootedCapGraph b
  root := N.actualRootedCapRoot b
  leaf := N.actualRootedCapLeaf b
  at_least_two_taxa := hc
  root_degrees := N.actual_rooted_cap_root_degrees b
  leaf_degrees := N.actual_rooted_cap_leaf_degrees b
  internal_degrees := N.actual_rooted_cap_internal_degrees b hb
  acyclic := N.actual_rooted_cap_acyclic b
  rooted := N.actual_rooted_cap_rooted b
  least_stable := N.actual_rooted_cap_least_stable b hb hc

noncomputable def actualFourPortRootedCapSource (q : Fin 4 ↪ X) (b : N.graph.Blob)
    (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) :
    RootedBinary (N.RootedCapVertex b) (N.RootedCapArc b) (N.BlobPort b) :=
  N.actualRootedCapSource b hb (N.actual_four_port_cap_has_two_taxa q b hb hinj)
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_least_stable
#print axioms Nanuq.Source.RootedBinary.actualFourPortRootedCapSource
