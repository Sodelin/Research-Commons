import guards.NanuqActualHybridChildTaxa

set_option debug.skipKernelTC false

/-! Exact original taxon labels on the opened tree: ordinary taxa occur once,
hybrid-child taxa twice, with parent EDGE occurrences kept distinct. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

abbrev OpenedTip := Sum N.OrdinaryTaxon N.HybridParentOccurrence
noncomputable instance openedTipFintype : Fintype N.OpenedTip := by
  classical
  unfold OpenedTip OrdinaryTaxon HybridParentOccurrence
  infer_instance
noncomputable instance openedTipDecidableEq : DecidableEq N.OpenedTip := Classical.decEq _

def openedTipVertex : N.OpenedTip ↪ N.OpenedHybridVertex where
  toFun := Sum.elim (fun x => Sum.inl ⟨N.leaf x.val,x.property⟩) Sum.inr
  inj' a b h := by
    rcases a with x | e <;> rcases b with y | f
    · exact congrArg Sum.inl (Subtype.ext (N.leaf.injective (congrArg Subtype.val (Sum.inl.inj h))))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Sum.inr.inj h)

noncomputable def openedTipLabel : N.OpenedTip → X :=
  Sum.elim Subtype.val (fun e => N.hybridChildTaxon hleaf ⟨N.graph.target e.val,e.property⟩)

theorem opened_ordinary_tip_fiber (x : N.OrdinaryTaxon) :
    (Finset.univ.filter (fun t : N.OpenedTip => N.openedTipLabel hleaf t = x.val)).card = 1 := by
  classical
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨Sum.inl x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,?_⟩
  intro t ht
  have he := (Finset.mem_filter.mp ht).2
  rcases t with y | e
  · exact congrArg Sum.inl (Subtype.ext he)
  · have hn := N.hybridChildTaxon_not_ordinary hleaf ⟨N.graph.target e.val,e.property⟩
    exact False.elim (hn (by rw [show N.hybridChildTaxon hleaf ⟨N.graph.target e.val,e.property⟩ = x.val from he];exact x.property))

noncomputable def openedHybridFiberEquiv (h : N.HybridVertex) :
    {t : N.OpenedTip // N.openedTipLabel hleaf t = N.hybridChildTaxon hleaf h} ≃
      {e : E // N.graph.target e = h.val} where
  toFun t := by
    rcases t with ⟨x | e,ht⟩
    · exact False.elim (N.hybridChildTaxon_not_ordinary hleaf h (by rw [← ht];exact x.property))
    · refine ⟨e.val,?_⟩
      exact congrArg Subtype.val (N.hybridChildTaxon_injective hleaf ht)
  invFun e := ⟨Sum.inr ⟨e.val,by rw [e.property];exact h.property⟩,
    congrArg (N.hybridChildTaxon hleaf) (Subtype.ext e.property)⟩
  left_inv t := by
    rcases t with ⟨x | e,ht⟩
    · exact False.elim (N.hybridChildTaxon_not_ordinary hleaf h (by rw [← ht];exact x.property))
    · rfl
  right_inv e := rfl

theorem opened_hybrid_tip_fiber (h : N.HybridVertex) :
    (Finset.univ.filter (fun t : N.OpenedTip =>
      N.openedTipLabel hleaf t = N.hybridChildTaxon hleaf h)).card = 2 := by
  rw [← Fintype.card_subtype,Fintype.card_congr (N.openedHybridFiberEquiv hleaf h)]
  have hi : (Finset.univ.filter (fun e : E => N.graph.target e = h.val)).card = 2 := h.property.1
  simpa only [← Fintype.card_subtype] using hi

theorem actual_opened_tip_multiplicity (x : X) :
    (Finset.univ.filter (fun t : N.OpenedTip => N.openedTipLabel hleaf t = x)).card =
      if N.SkeletonVertexPredicate (N.leaf x) then 1 else 2 := by
  by_cases hx : N.SkeletonVertexPredicate (N.leaf x)
  · rw [if_pos hx]
    exact N.opened_ordinary_tip_fiber hleaf ⟨x,hx⟩
  · obtain ⟨h,hh⟩ := N.nonordinary_taxon_is_hybrid_child hleaf x hx
    rw [if_neg hx,← hh]
    exact N.opened_hybrid_tip_fiber hleaf h
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_opened_tip_multiplicity
