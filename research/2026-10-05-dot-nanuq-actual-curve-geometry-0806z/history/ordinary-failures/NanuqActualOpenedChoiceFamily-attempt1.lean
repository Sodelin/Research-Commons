import NanuqActualIndependentParentChoices

/-! Exact independent occurrence selections and the original DISTINCT
quartet family/mean, evaluated on the literal opened tree. Source support
is derived before any circular contour or finite screen is used. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
open Nanuq.Quartet
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

namespace HybridParentChoice
variable {N} (C : N.HybridParentChoice)

noncomputable def selectedTipEmbedding : X ↪ N.OpenedTip := C.toSwitching.selectedOpenedTipEmbedding hleaf

theorem selectedTip_ordinary (x : N.OrdinaryTaxon) :
    C.selectedTipEmbedding hleaf x.val = Sum.inl x := by
  simp [selectedTipEmbedding,Switching.selectedOpenedTipEmbedding,Switching.selectedOpenedTip,x.property]

theorem selectedTip_hybrid (h : N.HybridVertex) :
    C.selectedTipEmbedding hleaf (N.hybridChildTaxon hleaf h) =
      Sum.inr (⟨(C h).val,by rw [(C h).property];exact h.property⟩ : N.HybridParentOccurrence) := by
  let x := N.hybridChildTaxon hleaf h
  have hx : ¬ N.SkeletonVertexPredicate (N.leaf x) := N.hybridChildTaxon_not_ordinary hleaf h
  change C.toSwitching.selectedOpenedTip hleaf x = _
  unfold Switching.selectedOpenedTip
  rw [dif_neg hx]
  have he : Classical.choose (N.nonordinary_taxon_is_hybrid_child hleaf x hx) = h :=
    N.hybridChildTaxon_injective hleaf (Classical.choose_spec (N.nonordinary_taxon_is_hybrid_child hleaf x hx))
  rw [he]
  apply congrArg Sum.inr
  apply Subtype.ext
  exact congrArg (fun D : N.HybridParentChoice => (D h).val) C.parent_choice_switching_roundtrip
end HybridParentChoice

noncomputable def actualOpenedChoiceResolve (q : Fin 4 ↪ X) (C : N.HybridParentChoice) : Resolution :=
  N.openedQuartetResolve hleaf (q.trans (C.selectedTipEmbedding hleaf))

theorem actual_opened_choice_resolve_eq (q : Fin 4 ↪ X) (C : N.HybridParentChoice) :
    N.actualOpenedChoiceResolve hleaf q C = C.toSwitching.resolve q :=
  C.toSwitching.actual_opened_selected_resolve hleaf q

theorem actual_opened_choice_distinct_family_and_mean (q : Fin 4 ↪ X) :
    N.rawDisplayedQuartets q = displayed (N.actualOpenedChoiceResolve hleaf q) ∧
      N.rawQuartetMean q = sourceMean (N.actualOpenedChoiceResolve hleaf q) := by
  let F := fun C : N.HybridParentChoice => C.toSwitching
  have hs : Function.Surjective F := (HybridParentChoice.actualSwitchingEquiv (N := N)).surjective
  have hf : N.actualOpenedChoiceResolve hleaf q = (fun S : N.Switching => S.resolve q) ∘ F := by
    funext C
    exact N.actual_opened_choice_resolve_eq hleaf q C
  constructor
  · unfold rawDisplayedQuartets
    rw [hf,displayed_comp_surjective F hs]
  · unfold rawQuartetMean
    rw [hf,sourceMean_comp_surjective F hs]

theorem actual_galled_cap_opened_family_and_mean (hg : N.graph.GalledDetour)
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) :
    N.rawDisplayedQuartets q = displayed
      ((N.actualEveryNonleafRootedCapSource b hb).actualOpenedChoiceResolve
        (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb) (N.actualRootedCapQuartet q b hb hinj)) ∧
    N.rawQuartetMean q = sourceMean
      ((N.actualEveryNonleafRootedCapSource b hb).actualOpenedChoiceResolve
        (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb) (N.actualRootedCapQuartet q b hb hinj)) := by
  have hcap := N.actual_four_port_rooted_cap_distinct_set_and_mean q b hb hinj
  have hopen := (N.actualEveryNonleafRootedCapSource b hb).actual_opened_choice_distinct_family_and_mean
    (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb) (N.actualRootedCapQuartet q b hb hinj)
  exact ⟨hcap.1.trans hopen.1,hcap.2.trans hopen.2⟩
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_opened_choice_distinct_family_and_mean
#print axioms Nanuq.Source.RootedBinary.actual_galled_cap_opened_family_and_mean
