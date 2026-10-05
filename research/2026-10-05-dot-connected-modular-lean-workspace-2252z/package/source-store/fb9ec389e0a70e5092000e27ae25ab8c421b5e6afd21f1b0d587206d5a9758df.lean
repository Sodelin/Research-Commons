import NanuqActualOpenedBinaryDegrees

/-! Full rooted LSA admission of the literal opened binary tree. Avoiding
original paths truncate at the first opened hybrid occurrence; the result
has at least two occurrence taxa and no hidden desired-tree assumption. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

theorem opened_avoiding_path_prefix (a : N.SkeletonVertex) (ha : a.val ≠ N.root)
    {v : V} (h : Relation.ReflTransGen
      (fun u w => N.graph.DStep u w ∧ u ≠ a.val ∧ w ≠ a.val) N.root v) :
    (∃ hv : N.SkeletonVertexPredicate v,
      (N.openedHybridGraph hleaf).AvoidReach (Sum.inl a) (Sum.inl N.rootSkeletonRoot) (Sum.inl ⟨v,hv⟩)) ∨
    ∃ t : N.OpenedTip, (N.openedHybridGraph hleaf).AvoidReach
      (Sum.inl a) (Sum.inl N.rootSkeletonRoot) (N.openedTipVertex t) := by
  have hr : Sum.inl N.rootSkeletonRoot ≠ (Sum.inl a : N.OpenedHybridVertex) := by
    intro he
    exact ha (congrArg Subtype.val (Sum.inl.inj he)).symm
  induction h with
  | refl => exact Or.inl ⟨N.root_skeleton_root_predicate,hr,hr,.refl⟩
  | @tail u w hp hs ih =>
    rcases ih with ⟨hu,hav⟩ | hex
    · obtain ⟨e,he,ht⟩ := hs.1
      have hes : N.SkeletonVertexPredicate (N.graph.source e) := by rw [he];exact hu
      by_cases hh : N.graph.IsHybrid (N.graph.target e)
      · let f : N.HybridParentOccurrence := ⟨e,hh⟩
        have hsrc : (N.openedHybridGraph hleaf).source (Sum.inr f) = Sum.inl ⟨u,hu⟩ :=
          congrArg Sum.inl (Subtype.ext he)
        have hne : N.openedTipVertex (Sum.inr f) ≠ Sum.inl a := by intro heq;cases heq
        exact Or.inr ⟨Sum.inr f,hr,hne,hav.2.2.tail
          ⟨⟨Sum.inr f,hsrc,rfl⟩,hav.2.1,hne⟩⟩
      · have hew := N.skeleton_edge_nonhybrid_target e hes hh
        have hw : N.SkeletonVertexPredicate w := by rw [← ht];exact hew
        have hne : Sum.inl ⟨w,hw⟩ ≠ (Sum.inl a : N.OpenedHybridVertex) := by
          intro heq
          exact hs.2.2 (congrArg Subtype.val (Sum.inl.inj heq))
        let f : N.SkeletonEdge := ⟨e,hes,hew⟩
        exact Or.inl ⟨hw,hr,hne,hav.2.2.tail
          ⟨⟨Sum.inl f,congrArg Sum.inl (Subtype.ext he),congrArg Sum.inl (Subtype.ext ht)⟩,
            hav.2.1,hne⟩⟩
    · exact Or.inr hex

theorem opened_inner_avoids_some_tip (a : N.SkeletonVertex) (ha : a.val ≠ N.root) :
    ∃ t : N.OpenedTip, (N.openedHybridGraph hleaf).AvoidReach
      (Sum.inl a) (Sum.inl N.rootSkeletonRoot) (N.openedTipVertex t) := by
  obtain ⟨x,hx⟩ := N.exists_leaf_avoiding_of_ne_root ha
  rcases N.opened_avoiding_path_prefix hleaf a ha hx.2.2 with ⟨hv,hvpath⟩ | hex
  · exact ⟨Sum.inl ⟨x,hv⟩,hvpath⟩
  · exact hex

theorem opened_least_stable :
    ∀ v : N.OpenedHybridVertex,
      (∀ t : N.OpenedTip, (N.openedHybridGraph hleaf).Dominates
        (Sum.inl N.rootSkeletonRoot) v (N.openedTipVertex t)) → v = Sum.inl N.rootSkeletonRoot := by
  intro v hd
  rcases v with a | e
  · by_cases ha : a.val = N.root
    · exact congrArg Sum.inl (Subtype.ext ha)
    · obtain ⟨t,ht⟩ := N.opened_inner_avoids_some_tip hleaf a ha
      exact False.elim (hd t ht)
  · let t : N.OpenedTip := Sum.inr e
    obtain ⟨u,hu⟩ := Fintype.exists_ne_of_one_lt_card
      (Nat.lt_of_lt_of_le (by decide : 1 < 2) (N.opened_at_least_two_tips hleaf)) t
    have hne : N.openedTipVertex u ≠ N.openedTipVertex t := fun h => hu (N.openedTipVertex.injective h)
    have ha : Sum.inl N.rootSkeletonRoot ≠ N.openedTipVertex t := (N.opened_tip_ne_root t).symm
    exact False.elim (hd u ((N.openedHybridGraph hleaf).dreach_avoids_distinct_sink
      (N.opened_tip_degrees hleaf t).2 ha hne (N.opened_hybrid_rooted hleaf _)))

noncomputable def actualOpenedRootedSource :
    RootedBinary N.OpenedHybridVertex N.OpenedHybridEdge N.OpenedTip where
  graph := N.openedHybridGraph hleaf
  root := Sum.inl N.rootSkeletonRoot
  leaf := N.openedTipVertex
  at_least_two_taxa := N.opened_at_least_two_tips hleaf
  root_degrees := N.opened_root_degrees hleaf
  leaf_degrees := N.opened_tip_degrees hleaf
  internal_degrees v hr hl := Or.inl (N.opened_internal_degrees hleaf v hr hl)
  acyclic := N.opened_hybrid_acyclic hleaf
  rooted := N.opened_hybrid_rooted hleaf
  least_stable := N.opened_least_stable hleaf

noncomputable def actualGalledCapOpenedRootedSource (hg : N.graph.GalledDetour)
    (b : N.graph.Blob) (hb : N.NonleafBlob b) :=
  (N.actualEveryNonleafRootedCapSource b hb).actualOpenedRootedSource
    (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actualGalledCapOpenedRootedSource
