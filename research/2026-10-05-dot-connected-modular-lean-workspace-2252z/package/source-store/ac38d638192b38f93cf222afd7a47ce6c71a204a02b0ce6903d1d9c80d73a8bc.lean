import NanuqActualOpenedQuartetReadout

/-! Every independent choice of one incoming original edge occurrence per
hybrid is exactly one actual source switching. No hidden coupling of opened
copy choices is introduced. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

abbrev HybridParentChoice := ∀ h : N.HybridVertex, {e : E // N.graph.target e = h.val}
noncomputable instance hybridVertexFintype : Fintype N.HybridVertex := by
  classical
  unfold HybridVertex
  infer_instance
noncomputable instance hybridParentChoiceFintype : Fintype N.HybridParentChoice := by
  classical
  unfold HybridParentChoice
  infer_instance

namespace HybridParentChoice
variable {N} (C : N.HybridParentChoice)

noncomputable def keep (e : E) : Prop :=
  if hh : N.graph.IsHybrid (N.graph.target e) then e = (C ⟨N.graph.target e,hh⟩).val else True

theorem keep_hybrid_iff (e : E) (hh : N.graph.IsHybrid (N.graph.target e)) :
    C.keep e ↔ e = (C ⟨N.graph.target e,hh⟩).val := by simp [keep,hh]

noncomputable def toSwitching : N.Switching where
  keep := C.keep
  ordinary e hh := by simp [keep,hh]
  hybrid_unique a ha := by
    let h : N.HybridVertex := ⟨a,ha⟩
    let e := C h
    have he : N.graph.target e.val = a := e.property
    have hh : N.graph.IsHybrid (N.graph.target e.val) := by rw [he];exact ha
    have hi : (⟨N.graph.target e.val,hh⟩ : N.HybridVertex) = h := Subtype.ext he
    refine ⟨e.val,he,?_,?_⟩
    · rw [C.keep_hybrid_iff e.val hh,hi]
    · intro f hf hk
      have hfhy : N.graph.IsHybrid (N.graph.target f) := by rw [hf];exact ha
      have hfi : (⟨N.graph.target f,hfhy⟩ : N.HybridVertex) = h := Subtype.ext hf
      have hk' := (C.keep_hybrid_iff f hfhy).mp hk
      exact hk'.trans (congrArg (fun t : N.HybridVertex => (C t).val) hfi)
end HybridParentChoice

namespace Switching
variable {N} (S : N.Switching)

noncomputable def toHybridParentChoice : N.HybridParentChoice := fun h =>
  ⟨(S.selectedHybridParent h).val,S.selectedHybridParent_target h⟩

theorem selectedHybridParent_unique (h : N.HybridVertex) (e : E)
    (he : N.graph.target e = h.val) (hk : S.keep e) : e = (S.selectedHybridParent h).val :=
  (Classical.choose_spec (S.hybrid_unique h.val h.property)).2.2 e he hk

theorem switching_parent_choice_roundtrip : S.toHybridParentChoice.toSwitching = S := by
  have hk : S.toHybridParentChoice.toSwitching.keep = S.keep := by
    funext e
    apply propext
    by_cases hh : N.graph.IsHybrid (N.graph.target e)
    · change S.toHybridParentChoice.keep e ↔ S.keep e
      rw [HybridParentChoice.keep_hybrid_iff]
      constructor
      · intro he
        rw [he]
        exact S.selectedHybridParent_keep _
      · intro he
        exact S.selectedHybridParent_unique ⟨N.graph.target e,hh⟩ e rfl he
    · change S.toHybridParentChoice.keep e ↔ S.keep e
      simp only [HybridParentChoice.keep,dif_neg hh]
      exact ⟨fun _ => S.ordinary e hh,fun _ => True.intro⟩
  generalize hT : S.toHybridParentChoice.toSwitching = T at hk ⊢
  cases T
  cases S
  cases hk
  rfl
end Switching

namespace HybridParentChoice
variable {N} (C : N.HybridParentChoice)

theorem parent_choice_switching_roundtrip : C.toSwitching.toHybridParentChoice = C := by
  funext h
  apply Subtype.ext
  let e := C.toSwitching.selectedHybridParent h
  have he := C.toSwitching.selectedHybridParent_target h
  have hk := C.toSwitching.selectedHybridParent_keep h
  change C.keep e.val at hk
  have hi : (⟨N.graph.target e.val,e.property⟩ : N.HybridVertex) = h := Subtype.ext he
  have hk' := (C.keep_hybrid_iff e.val e.property).mp hk
  change e.val = (C h).val
  exact hk'.trans (congrArg (fun t : N.HybridVertex => (C t).val) hi)

noncomputable def actualSwitchingEquiv : N.HybridParentChoice ≃ N.Switching where
  toFun C := C.toSwitching
  invFun S := S.toHybridParentChoice
  left_inv C := C.parent_choice_switching_roundtrip
  right_inv S := S.switching_parent_choice_roundtrip
end HybridParentChoice
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.HybridParentChoice.actualSwitchingEquiv
