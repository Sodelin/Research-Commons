import NanuqActualOpenedSelection

/-! An actual switching maps each opened selected occurrence back to its
original taxon. Unselected stubs collapse at their own parent; selected stubs
lift through their actual hybrid and its pendant child, preserving skeleton
edge-deletion cuts. -/
namespace Nanuq.Source.RootedBinary.Switching
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

def retainedSkeletonEdge (f : N.SkeletonEdge) : S.Edge := ⟨f.val,S.ordinary f.val f.property.2.1⟩

theorem opened_edge_selection_path_without (cut : N.SkeletonEdge) (f : N.OpenedHybridEdge)
    (hf : f ≠ Sum.inl cut) :
    S.graph.ReachWithout (S.retainedSkeletonEdge cut)
      (S.openedSelectionCollapse hleaf ((N.openedHybridGraph hleaf).source f))
      (S.openedSelectionCollapse hleaf ((N.openedHybridGraph hleaf).target f)) := by
  rcases f with e | e
  · exact Relation.ReflTransGen.single ⟨S.retainedSkeletonEdge e,
      fun he => hf (congrArg Sum.inl (Subtype.ext (congrArg (fun g : S.Edge => g.val) he))),Or.inl ⟨rfl,rfl⟩⟩
  · by_cases hk : S.keep e.val
    · let h : N.HybridVertex := ⟨N.graph.target e.val,e.property⟩
      obtain ⟨c,hc,hct⟩ := N.hybridChildTaxon_spec hleaf h
      have hcOrd : ¬ N.graph.IsHybrid (N.graph.target c) := by
        intro hh
        have h1 := (N.leaf_degrees (N.hybridChildTaxon hleaf h)).1
        have h2 := hh.1
        rw [hct] at h2
        omega
      have hecut : e.val ≠ cut.val := by
        intro heq
        exact cut.property.2.1 (by rw [← heq];exact e.property)
      have hccut : c ≠ cut.val := by
        intro heq
        apply cut.property.1.1
        rw [← heq,hc]
        exact e.property
      have hp : S.graph.ReachWithout (S.retainedSkeletonEdge cut)
          (N.graph.source e.val) (N.graph.target e.val) :=
        Relation.ReflTransGen.single ⟨⟨e.val,hk⟩,
          fun heq => hecut (congrArg Subtype.val heq),Or.inl ⟨rfl,rfl⟩⟩
      have hpath : S.graph.ReachWithout (S.retainedSkeletonEdge cut)
          (N.graph.source e.val) (N.leaf (N.hybridChildTaxon hleaf h)) :=
        hp.tail ⟨⟨c,S.ordinary c hcOrd⟩,
          fun heq => hccut (congrArg Subtype.val heq),Or.inl ⟨hc,hct⟩⟩
      change S.graph.ReachWithout (S.retainedSkeletonEdge cut) (N.graph.source e.val)
        (if S.keep e.val then N.leaf (N.hybridChildTaxon hleaf h) else N.graph.source e.val)
      rw [if_pos hk]
      exact hpath
    · change S.graph.ReachWithout (S.retainedSkeletonEdge cut) (N.graph.source e.val)
        (if S.keep e.val then N.leaf (N.hybridChildTaxon hleaf
          ⟨N.graph.target e.val,e.property⟩) else N.graph.source e.val)
      rw [if_neg hk]
      exact .refl

theorem opened_cut_walk_selection (cut : N.SkeletonEdge) {a b : N.OpenedHybridVertex}
    (h : (N.openedHybridGraph hleaf).ReachWithout (Sum.inl cut) a b) :
    S.graph.ReachWithout (S.retainedSkeletonEdge cut)
      (S.openedSelectionCollapse hleaf a) (S.openedSelectionCollapse hleaf b) := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨f,hf,hinc⟩ := hs
    have hl := S.opened_edge_selection_path_without hleaf cut f hf
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact ih.trans (by rwa [hs,ht] at hl)
    · exact ih.trans (by have hr := S.graph.ureach_symm hl;rwa [hs,ht] at hr)

theorem opened_skeleton_oriented_selected (cut : N.SkeletonEdge) (a c d e : X)
    (h : (N.openedHybridGraph hleaf).OrientedQuartet (Sum.inl cut)
      (N.openedTipVertex (S.selectedOpenedTip hleaf a))
      (N.openedTipVertex (S.selectedOpenedTip hleaf c))
      (N.openedTipVertex (S.selectedOpenedTip hleaf d))
      (N.openedTipVertex (S.selectedOpenedTip hleaf e))) :
    S.graph.OrientedQuartet (S.retainedSkeletonEdge cut) (N.leaf a) (N.leaf c) (N.leaf d) (N.leaf e) := by
  refine ⟨?_,?_,?_,?_⟩
  · have hx := S.opened_cut_walk_selection hleaf cut h.1
    rw [S.openedSelectionCollapse_selected_tip hleaf a] at hx
    exact hx
  · have hx := S.opened_cut_walk_selection hleaf cut h.2.1
    rw [S.openedSelectionCollapse_selected_tip hleaf c] at hx
    exact hx
  · have hx := S.opened_cut_walk_selection hleaf cut h.2.2.1
    rw [S.openedSelectionCollapse_selected_tip hleaf d] at hx
    exact hx
  · have hx := S.opened_cut_walk_selection hleaf cut h.2.2.2
    rw [S.openedSelectionCollapse_selected_tip hleaf e] at hx
    exact hx
end Nanuq.Source.RootedBinary.Switching

#print axioms Nanuq.Source.RootedBinary.Switching.opened_skeleton_oriented_selected
