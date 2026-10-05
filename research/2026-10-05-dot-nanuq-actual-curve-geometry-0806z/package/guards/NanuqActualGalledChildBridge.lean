import guards.NanuqLeafEdgeWalkErase

set_option debug.skipKernelTC false

/-! An original hybrid child edge is a bridge under the actual ordinary
parent-detour galled predicate. This is the source-level root-skeleton gate;
no pendant-child or bridge conclusion is assumed. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem ordinary_walk_avoids_hybrid_child (e : E) (hh : N.graph.IsHybrid (N.graph.source e))
    {a b : V} (ha : a ≠ N.graph.source e) (hb : b ≠ N.graph.source e)
    (h : N.graph.UReach (fun f => ¬ N.graph.IsHybrid (N.graph.target f)) a b) :
    N.graph.UReach (fun f => ¬ N.graph.IsHybrid (N.graph.target f) ∧ f ≠ e) a b := by
  apply N.graph.allowed_walk_avoids_leaf_edge _ e (N.graph.acyclic_no_loop N.acyclic e) _ ha hb h
  intro f hf hfe
  constructor
  · intro hs
    exact hfe (N.graph.outgoing_equal_of_degree_one hh.2 f e hs rfl)
  · intro ht
    exact hf (by rw [ht];exact hh)

namespace Switching
variable {N} (S : N.Switching)

theorem ordinary_cut_walk_lifts (e : S.Edge) {a b : V}
    (h : N.graph.UReach (fun f => ¬ N.graph.IsHybrid (N.graph.target f) ∧ f ≠ e.val) a b) :
    S.graph.ReachWithout e a b := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨f,hf,hinc⟩ := hs
    exact ih.tail ⟨⟨f,S.ordinary f hf.1⟩,
      fun he => hf.2 (congrArg Subtype.val he),hinc⟩

noncomputable def retainedHybridChild (hg : N.graph.GalledDetour) (e : E)
    (hh : N.graph.IsHybrid (N.graph.source e)) : S.Edge :=
  ⟨e,S.ordinary e (N.actual_galled_hybrid_child_not_hybrid hg e hh)⟩

theorem original_other_edge_selected_detour (hg : N.graph.GalledDetour) (e : E)
    (hh : N.graph.IsHybrid (N.graph.source e)) (f : E) (hfe : f ≠ e) :
    S.graph.ReachWithout (S.retainedHybridChild hg e hh) (N.graph.source f) (N.graph.target f) := by
  by_cases hk : S.keep f
  · exact Relation.ReflTransGen.single ⟨⟨f,hk⟩,
      fun he => hfe (congrArg Subtype.val he),Or.inl ⟨rfl,rfl⟩⟩
  · have hfhy : N.graph.IsHybrid (N.graph.target f) := by
      by_contra h
      exact hk (S.ordinary f h)
    obtain ⟨g,hgT,hgK,hgU⟩ := S.hybrid_unique (N.graph.target f) hfhy
    have hfg : f ≠ g := by intro he;exact hk (he ▸ hgK)
    have hge : g ≠ e := by
      intro he
      have hno := N.actual_galled_hybrid_child_not_hybrid hg e hh
      apply hno
      rw [← he,hgT]
      exact hfhy
    have hfs : N.graph.source f ≠ N.graph.source e := by
      intro hs
      exact hfe (N.graph.outgoing_equal_of_degree_one hh.2 f e hs rfl)
    have hgs : N.graph.source g ≠ N.graph.source e := by
      intro hs
      exact hge (N.graph.outgoing_equal_of_degree_one hh.2 g e hs rfl)
    have hdet := hg (N.graph.target f) hfhy f g hfg rfl hgT
    have ho := N.graph.ureach_mono (fun _ h => h.1) hdet
    have hav := N.ordinary_walk_avoids_hybrid_child e hh hfs hgs ho
    have hl := S.ordinary_cut_walk_lifts (S.retainedHybridChild hg e hh) hav
    exact hl.tail ⟨⟨g,hgK⟩,fun he => hge (congrArg Subtype.val he),Or.inl ⟨rfl,hgT⟩⟩

theorem original_cut_walk_lifts_at_hybrid_child (hg : N.graph.GalledDetour) (e : E)
    (hh : N.graph.IsHybrid (N.graph.source e)) {a b : V}
    (h : N.graph.ReachWithout e a b) :
    S.graph.ReachWithout (S.retainedHybridChild hg e hh) a b := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨f,hf,hinc⟩ := hs
    have hd := S.original_other_edge_selected_detour hg e hh f hf
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact ih.trans (by rwa [hs,ht] at hd)
    · exact ih.trans (by have hr := S.graph.ureach_symm hd;rwa [hs,ht] at hr)
end Switching

theorem actual_galled_hybrid_child_is_bridge (hg : N.graph.GalledDetour)
    (e : E) (hh : N.graph.IsHybrid (N.graph.source e)) : N.graph.IsBridge e := by
  let S : N.Switching := Classical.choice inferInstance
  intro h
  exact S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic
    (S.retainedHybridChild hg e hh) (S.original_cut_walk_lifts_at_hybrid_child hg e hh h)
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_galled_hybrid_child_is_bridge
