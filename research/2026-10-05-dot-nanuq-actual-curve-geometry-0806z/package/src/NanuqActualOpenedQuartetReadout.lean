import NanuqActualOpenedCutProjection

/-! Actual quartet evaluation of the opened tree at the occurrence tips
selected by one original switching. Unselected stubs collapse at their own
parents; no displayed-quartet correspondence is supplied as a hypothesis. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

theorem opened_graph_no_hybrids (v : N.OpenedHybridVertex) :
    ¬ (N.openedHybridGraph hleaf).IsHybrid v := by
  intro hh
  rcases v with a | e
  · exact a.property.1 ⟨(N.opened_inner_indegree hleaf a).symm.trans hh.1,
      (N.opened_inner_outdegree hleaf a).symm.trans hh.2⟩
  · have h1 := (N.opened_new_tip_degrees hleaf e).1
    have h2 := hh.1
    omega

noncomputable def openedWholeSwitching : (N.actualOpenedRootedSource hleaf).Switching where
  keep _ := True
  ordinary _ _ := True.intro
  hybrid_unique v hv := False.elim (N.opened_graph_no_hybrids hleaf v hv)

noncomputable def openedWholeEdgeEquiv : N.OpenedHybridEdge ≃ (N.openedWholeSwitching hleaf).Edge where
  toFun e := ⟨e,True.intro⟩
  invFun e := e.val
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def openedQuartetResolve (q : Fin 4 ↪ N.OpenedTip) : Nanuq.Quartet.Resolution :=
  (N.openedWholeSwitching hleaf).resolve q

theorem openedQuartetResolve_spec (q : Fin 4 ↪ N.OpenedTip) :
    (N.openedHybridGraph hleaf).Resolves (fun i => N.openedTipVertex (q i))
      (N.openedQuartetResolve hleaf q) := by
  exact ((N.openedHybridGraph hleaf).resolves_edge_equiv_iff (N.openedWholeSwitching hleaf).graph
    (N.openedWholeEdgeEquiv hleaf) (fun _ => rfl) (fun _ => rfl) _ _).mpr
      ((N.openedWholeSwitching hleaf).resolve_spec q)

theorem opened_newtip_cut_walk_constant (e : N.HybridParentOccurrence)
    {v : N.OpenedHybridVertex}
    (h : (N.openedHybridGraph hleaf).ReachWithout (Sum.inr e) (Sum.inr e) v) : v = Sum.inr e := by
  induction h with
  | refl => rfl
  | @tail v w hp hs ih =>
    obtain ⟨f,hf,hinc⟩ := hs
    rcases f with f | f
    · rcases hinc with ⟨hs,_⟩ | ⟨_,ht⟩
      · rw [ih] at hs;cases hs
      · rw [ih] at ht;cases ht
    · rcases hinc with ⟨hs,_⟩ | ⟨_,ht⟩
      · rw [ih] at hs;cases hs
      · exact False.elim (hf (congrArg Sum.inr (Sum.inr.inj (ht.trans ih))))

namespace Switching
variable {N} (S : N.Switching)

theorem opened_newtip_oriented_selected_false (f : N.HybridParentOccurrence)
    (a c d e : X) (hde : d ≠ e)
    (h : (N.openedHybridGraph hleaf).OrientedQuartet (Sum.inr f)
      (N.openedTipVertex (S.selectedOpenedTip hleaf a))
      (N.openedTipVertex (S.selectedOpenedTip hleaf c))
      (N.openedTipVertex (S.selectedOpenedTip hleaf d))
      (N.openedTipVertex (S.selectedOpenedTip hleaf e))) : False := by
  have hd := N.opened_newtip_cut_walk_constant hleaf f h.2.2.1
  have he := N.opened_newtip_cut_walk_constant hleaf f h.2.2.2
  exact hde ((S.selectedOpenedTipEmbedding hleaf).injective
    (N.openedTipVertex.injective (hd.trans he.symm)))

theorem opened_selected_hasQuartet (a c d e : X) (hac : a ≠ c) (hde : d ≠ e)
    (h : (N.openedHybridGraph hleaf).HasQuartet
      (N.openedTipVertex (S.selectedOpenedTip hleaf a))
      (N.openedTipVertex (S.selectedOpenedTip hleaf c))
      (N.openedTipVertex (S.selectedOpenedTip hleaf d))
      (N.openedTipVertex (S.selectedOpenedTip hleaf e))) :
    S.graph.HasQuartet (N.leaf a) (N.leaf c) (N.leaf d) (N.leaf e) := by
  obtain ⟨f,hf,h | h⟩ := h
  · rcases f with f | f
    · exact ⟨S.retainedSkeletonEdge f,
        S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic _,
        Or.inl (S.opened_skeleton_oriented_selected hleaf f a c d e h)⟩
    · exact False.elim (S.opened_newtip_oriented_selected_false hleaf f a c d e hde h)
  · rcases f with f | f
    · exact ⟨S.retainedSkeletonEdge f,
        S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic _,
        Or.inr (S.opened_skeleton_oriented_selected hleaf f d e a c h)⟩
    · exact False.elim (S.opened_newtip_oriented_selected_false hleaf f d e a c hac h)

theorem opened_selected_resolves (q : Fin 4 ↪ X) (r : Nanuq.Quartet.Resolution)
    (h : (N.openedHybridGraph hleaf).Resolves
      (fun i => N.openedTipVertex (S.selectedOpenedTip hleaf (q i))) r) :
    S.graph.Resolves (fun i => N.leaf (q i)) r := by
  have hn (i j : Fin 4) (hij : i ≠ j) : q i ≠ q j := fun he => hij (q.injective he)
  cases r
  · exact S.opened_selected_hasQuartet hleaf _ _ _ _ (hn 0 1 (by decide)) (hn 2 3 (by decide)) h
  · exact S.opened_selected_hasQuartet hleaf _ _ _ _ (hn 0 2 (by decide)) (hn 1 3 (by decide)) h
  · exact S.opened_selected_hasQuartet hleaf _ _ _ _ (hn 0 3 (by decide)) (hn 1 2 (by decide)) h

theorem actual_opened_selected_resolve (q : Fin 4 ↪ X) :
    N.openedQuartetResolve hleaf (q.trans (S.selectedOpenedTipEmbedding hleaf)) = S.resolve q := by
  apply (S.resolves_iff_eq_resolve q _).mp
  exact S.opened_selected_resolves hleaf q _ (N.openedQuartetResolve_spec hleaf _)
end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.actual_opened_selected_resolve
