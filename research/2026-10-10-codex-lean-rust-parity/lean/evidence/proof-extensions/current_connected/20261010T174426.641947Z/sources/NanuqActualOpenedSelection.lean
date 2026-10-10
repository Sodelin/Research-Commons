import NanuqActualOpenedRootedAdmission

/-! A real original switching chooses exactly one actual opened occurrence
of every original taxon. The selected-tip embedding is derived by its label
left inverse, not assumed as an external paired-tip selection. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X}
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

namespace Switching
variable (S : N.Switching)

noncomputable def selectedHybridParent (h : N.HybridVertex) : N.HybridParentOccurrence :=
  ⟨Classical.choose (S.hybrid_unique h.val h.property),by
    rw [(Classical.choose_spec (S.hybrid_unique h.val h.property)).1]
    exact h.property⟩

theorem selectedHybridParent_target (h : N.HybridVertex) :
    N.graph.target (S.selectedHybridParent h).val = h.val :=
  (Classical.choose_spec (S.hybrid_unique h.val h.property)).1

theorem selectedHybridParent_keep (h : N.HybridVertex) : S.keep (S.selectedHybridParent h).val :=
  (Classical.choose_spec (S.hybrid_unique h.val h.property)).2.1

noncomputable def selectedOpenedTip (x : X) : N.OpenedTip :=
  if hx : N.SkeletonVertexPredicate (N.leaf x) then Sum.inl ⟨x,hx⟩
  else Sum.inr (S.selectedHybridParent
    (Classical.choose (N.nonordinary_taxon_is_hybrid_child hleaf x hx)))

theorem selectedOpenedTip_label (x : X) :
    N.openedTipLabel hleaf (S.selectedOpenedTip hleaf x) = x := by
  unfold selectedOpenedTip
  split
  · rfl
  · rename_i hx
    let h := Classical.choose (N.nonordinary_taxon_is_hybrid_child hleaf x hx)
    have hh := Classical.choose_spec (N.nonordinary_taxon_is_hybrid_child hleaf x hx)
    change N.hybridChildTaxon hleaf
      ⟨N.graph.target (S.selectedHybridParent h).val,(S.selectedHybridParent h).property⟩ = x
    have he : (⟨N.graph.target (S.selectedHybridParent h).val,
      (S.selectedHybridParent h).property⟩ : N.HybridVertex) = h :=
      Subtype.ext (S.selectedHybridParent_target h)
    rw [he]
    exact hh

noncomputable def selectedOpenedTipEmbedding : X ↪ N.OpenedTip where
  toFun := S.selectedOpenedTip hleaf
  inj' a b he := (S.selectedOpenedTip_label hleaf a).symm.trans
    ((congrArg (N.openedTipLabel hleaf) he).trans (S.selectedOpenedTip_label hleaf b))

noncomputable def openedSelectionCollapse : N.OpenedHybridVertex → V :=
  Sum.elim Subtype.val (fun e => if S.keep e.val then
    N.leaf (N.hybridChildTaxon hleaf ⟨N.graph.target e.val,e.property⟩)
    else N.graph.source e.val)

theorem openedSelectionCollapse_selected_tip (x : X) :
    S.openedSelectionCollapse hleaf (N.openedTipVertex (S.selectedOpenedTip hleaf x)) = N.leaf x := by
  unfold selectedOpenedTip
  split
  · rfl
  · rename_i hx
    let h := Classical.choose (N.nonordinary_taxon_is_hybrid_child hleaf x hx)
    have hh := Classical.choose_spec (N.nonordinary_taxon_is_hybrid_child hleaf x hx)
    change (if S.keep (S.selectedHybridParent h).val then
      N.leaf (N.hybridChildTaxon hleaf
        ⟨N.graph.target (S.selectedHybridParent h).val,(S.selectedHybridParent h).property⟩)
      else N.graph.source (S.selectedHybridParent h).val) = N.leaf x
    rw [if_pos (S.selectedHybridParent_keep h)]
    have he : (⟨N.graph.target (S.selectedHybridParent h).val,
      (S.selectedHybridParent h).property⟩ : N.HybridVertex) = h :=
      Subtype.ext (S.selectedHybridParent_target h)
    rw [he,hh]
end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.selectedOpenedTip_label
#print axioms Nanuq.Source.RootedBinary.Switching.openedSelectionCollapse_selected_tip
