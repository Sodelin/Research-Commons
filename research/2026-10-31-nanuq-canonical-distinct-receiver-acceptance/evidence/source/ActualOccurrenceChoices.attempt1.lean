import NanuqActualOpenedChoiceFamily

/-! UNCOMPILED source draft. A prescribed selection of occurrences of
DISTINCT original labels extends to one actual original parent choice.
No ordered-tree or geometric receiver is assumed. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X I : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e=N.leaf x)

/-- Distinct labels, not distinct parent vertices, ensure compatibility.
Parallel incoming original IDs remain separate values of each fibre. -/
theorem actual_occurrence_selection_extends
    (q : I ↪ X) (t : I → N.OpenedTip)
    (ht : ∀ i, N.openedTipLabel hleaf (t i)=q i) :
    ∃ C : N.HybridParentChoice, ∀ i, C.selectedTipEmbedding hleaf (q i)=t i := by
  classical
  let C0 : N.HybridParentChoice :=
    (Classical.choice (inferInstance : Nonempty N.Switching)).toHybridParentChoice
  let C : N.HybridParentChoice := fun h =>
    if hi : ∃ i, q i=N.hybridChildTaxon hleaf h then
      N.openedHybridFiberEquiv hleaf h
        ⟨t (Classical.choose hi), (ht _).trans (Classical.choose_spec hi)⟩
    else C0 h
  have hC (h : N.HybridVertex) (i : I)
      (hi : q i=N.hybridChildTaxon hleaf h) :
      C h=N.openedHybridFiberEquiv hleaf h ⟨t i,(ht i).trans hi⟩ := by
    have hex : ∃ j, q j=N.hybridChildTaxon hleaf h := ⟨i,hi⟩
    have he : Classical.choose hex=i :=
      q.injective ((Classical.choose_spec hex).trans hi.symm)
    dsimp [C]
    rw [dif_pos hex]
    simp only [he]
  refine ⟨C,?_⟩
  intro i
  rcases hti : t i with x | e
  · have hx : x.val=q i := by simpa only [hti,openedTipLabel] using ht i
    rw [← hx,C.selectedTip_ordinary hleaf x,hti]
  · let h : N.HybridVertex := ⟨N.graph.target e.val,e.property⟩
    have hi : q i=N.hybridChildTaxon hleaf h := by
      simpa only [hti,openedTipLabel] using (ht i).symm
    rw [hi,C.selectedTip_hybrid hleaf h]
    change ((N.openedHybridFiberEquiv hleaf h).symm (C h)).val=t i
    rw [hC h i hi,Equiv.symm_apply_apply]

#print axioms actual_occurrence_selection_extends
end Nanuq.Source.RootedBinary
