import ContinuedArms
import NanuqFaithfulSupplierDrawing

/-! UNCOMPILED source-facing auxiliary loop. Same original edge IDs/curves;
no arbitrary rotation, order, or extra accessibility input. -/
noncomputable section
namespace Nanuq.ContinuedArms
open Set Schoenflies unitInterval
open scoped Graph

/-- Two arbitrary distinct incident edges of the SAME faithful supplier drawing
have initial germs contained in an auxiliary Jordan curve. Parallel edges are allowed. -/
theorem jordan_germs_of_isDrawing {E : Type*} {G : Graph Plane E}
    {drawing : E → ℝ → Plane} (hD : Graph.IsDrawing G drawing)
    {e₁ e₂ : E} {v w₁ w₂ : Plane} (h₁ : G.IsLink e₁ v w₁)
    (h₂ : G.IsLink e₂ v w₂) (hne : e₁ ≠ e₂) :
    ∃ (f g : ℝ → Plane) (C : Set Plane),
      ContinuousOn f I ∧ InjOn f I ∧ f '' I = Graph.edgeArc drawing e₁ ∧ f 0 = v ∧ f 1 = w₁ ∧
      ContinuousOn g I ∧ InjOn g I ∧ g '' I = Graph.edgeArc drawing e₂ ∧ g 0 = v ∧ g 1 = w₂ ∧
      IsJordanCurve C ∧ f '' Icc 0 (1/6) ∪ g '' Icc 0 (1/6) ⊆ C := by
  obtain ⟨f,hfc,hfi,hfim,hf0,hf1⟩ := hD.edge_isArcBetween h₁
  obtain ⟨g,hgc,hgi,hgim,hg0,hg1⟩ := hD.edge_isArcBetween h₂
  let f₀ := fun t : ℝ => f (t/2)
  let g₀ := fun t : ℝ => g (t/2)
  have hh : ∀ t ∈ I, t/2 ∈ I := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hf₀c : ContinuousOn f₀ I := hfc.comp (by fun_prop) hh
  have hg₀c : ContinuousOn g₀ I := hgc.comp (by fun_prop) hh
  have hf₀i : InjOn f₀ I := by
    intro t ht u hu he
    have := hfi (hh t ht) (hh u hu) he
    linarith
  have hg₀i : InjOn g₀ I := by
    intro t ht u hu he
    have := hgi (hh t ht) (hh u hu) he
    linarith
  have hzero : f₀ 0 = g₀ 0 := by simpa [f₀,g₀] using hf0.trans hg0.symm
  have hmeet : ∀ z ∈ f₀ '' I, z ∈ g₀ '' I → z = f₀ 0 := by
    rintro z ⟨t,ht,rfl⟩ ⟨u,hu,he⟩
    have he₁ : f₀ t ∈ Graph.edgeArc drawing e₁ := hfim ▸ ⟨t/2,hh t ht,rfl⟩
    have he₂ : f₀ t ∈ Graph.edgeArc drawing e₂ := hgim ▸ ⟨u/2,hh u hu,he⟩
    have hv := hD.arcs_meet_at_vertex h₁.edge_mem h₂.edge_mem hne he₁ he₂
    rcases hD.vertex_mem_edgeArc h₁ hv he₁ with hz | hz
    · simpa [f₀,hf0] using hz
    · have ht1 : t/2 = 1 := hfi (hh t ht) one_mem_I (hz.trans hf1.symm)
      linarith [ht.2]
  obtain ⟨B,_,_,hC,_⟩ := jordan_through_two_germs f₀ g₀ hf₀c hg₀c hf₀i hg₀i hzero hmeet
  refine ⟨f,g,_,hfc,hfi,hfim,hf0,hf1,hgc,hgi,hgim,hg0,hg1,hC,?_⟩
  rintro z (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
  · apply Or.inl
    apply Or.inl
    refine ⟨2*t,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    simp [f₀]
  · apply Or.inl
    apply Or.inr
    refine ⟨2*t,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    simp [g₀]

/-- Actual admitted source binding, using the already accepted full faithful
coordinate adapter. The original physical IDs e₁,e₂ are not replaced. -/
theorem actual_original_incident_germs
    {V E : Type*} {G : Nanuq.Source.EdgeGraph V E}
    (D : G1OuterLabelledMultigraphCurves.PlanarCurves G)
    {e₁ e₂ : E} {v w₁ w₂ : V} (h₁ : G.Inc e₁ v w₁)
    (h₂ : G.Inc e₂ v w₂) (hne : e₁ ≠ e₂) :
    ∃ (f g : ℝ → Plane) (C : Set Plane),
      ContinuousOn f I ∧ InjOn f I ∧
      f '' I = Graph.edgeArc (NanuqFaithfulSupplierDrawing.curve D) e₁ ∧
      f 0 = NanuqFaithfulSupplierDrawing.vertex D v ∧
      f 1 = NanuqFaithfulSupplierDrawing.vertex D w₁ ∧
      ContinuousOn g I ∧ InjOn g I ∧
      g '' I = Graph.edgeArc (NanuqFaithfulSupplierDrawing.curve D) e₂ ∧
      g 0 = NanuqFaithfulSupplierDrawing.vertex D v ∧
      g 1 = NanuqFaithfulSupplierDrawing.vertex D w₂ ∧
      IsJordanCurve C ∧ f '' Icc 0 (1/6) ∪ g '' Icc 0 (1/6) ⊆ C := by
  have he₁ : (NanuqFaithfulSupplierDrawing.graph D).IsLink e₁
      (NanuqFaithfulSupplierDrawing.vertex D v) (NanuqFaithfulSupplierDrawing.vertex D w₁) := by
    rcases h₁ with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm⟩
    · exact Or.inr ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm⟩
  have he₂ : (NanuqFaithfulSupplierDrawing.graph D).IsLink e₂
      (NanuqFaithfulSupplierDrawing.vertex D v) (NanuqFaithfulSupplierDrawing.vertex D w₂) := by
    rcases h₂ with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm⟩
    · exact Or.inr ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm⟩
  exact jordan_germs_of_isDrawing (NanuqFaithfulSupplierDrawing.isDrawing D) he₁ he₂ hne

#print axioms jordan_germs_of_isDrawing
#print axioms actual_original_incident_germs
end Nanuq.ContinuedArms
