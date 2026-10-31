import ActualOccurrenceChoices

/-! UNCOMPILED exact existential occurrence readout. The original DISTINCT
set is unchanged; no frequency or occurrence multiplicity is counted. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Source.RootedBinary
open scoped Classical
open Nanuq.Quartet
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e=N.leaf x)

theorem actual_displayed_iff_occurrence_resolves (q : Fin 4 ↪ X) (r : Resolution) :
    r∈N.rawDisplayedQuartets q ↔
      ∃ t : Fin 4 ↪ N.OpenedTip,
        (∀ i, N.openedTipLabel hleaf (t i)=q i) ∧
        (N.openedHybridGraph hleaf).Resolves (fun i => N.openedTipVertex (t i)) r := by
  classical
  constructor
  · intro hr
    change r∈displayed (fun S : N.Switching => S.resolve q) at hr
    obtain ⟨S,_,hSr⟩ := Finset.mem_image.mp hr
    refine ⟨q.trans (S.selectedOpenedTipEmbedding hleaf),?_,?_⟩
    · intro i
      exact S.selectedOpenedTip_label hleaf (q i)
    · have h := N.openedQuartetResolve_spec hleaf (q.trans (S.selectedOpenedTipEmbedding hleaf))
      rw [S.actual_opened_selected_resolve hleaf q,hSr] at h
      exact h
  · rintro ⟨t,ht,hr⟩
    obtain ⟨C,hC⟩ := N.actual_occurrence_selection_extends hleaf q (fun i => t i) ht
    have hfun : (fun i => N.openedTipVertex (t i))=
        (fun i => N.openedTipVertex (C.toSwitching.selectedOpenedTip hleaf (q i))) := by
      funext i
      exact congrArg N.openedTipVertex (hC i).symm
    rw [hfun] at hr
    have hres := C.toSwitching.opened_selected_resolves hleaf q r hr
    have he := (C.toSwitching.resolves_iff_eq_resolve q r).mp hres
    change r∈displayed (fun S : N.Switching => S.resolve q)
    exact Finset.mem_image.mpr ⟨C.toSwitching,Finset.mem_univ _,he.symm⟩

#print axioms actual_displayed_iff_occurrence_resolves
end Nanuq.Source.RootedBinary
