import GeneralRegionCrosscut
import CycleArcStraightening
import AmbientTransport

set_option debug.skipKernelTC false
/-! UNCOMPILED composition candidate. The original crosscut and boundary are
arbitrary continuous simple arcs/Jordan curves. One prescribed ambient map is
used only as a proof device; every labelled component is pulled back to the
original embedding. No original polygonality, order, collar or star premise
is added. -/
namespace Nanuq.ContinuousRegionCrosscut
open Set Schoenflies unitInterval

 theorem jordan_image (H : Plane ≃ₜ Plane) {C : Set Plane}
    (hC : IsJordanCurve C) : IsJordanCurve (H '' C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  refine ⟨H ∘ f, ?_, image_comp H f I⟩
  exact ⟨H.continuous.comp_continuousOn hf.continuousOn,
    by simpa only [Function.comp_apply] using congrArg H hf.closes,
    fun a ha b hb hab => hf.injOn ha hb (H.injective hab)⟩

 theorem inside_image (H : Plane ≃ₜ Plane) (C : Set Plane) :
    H '' inside C = inside (H '' C) := by
  ext y
  obtain ⟨x,rfl⟩ := H.surjective y
  simpa only [H.injective.mem_set_image, mem_inside_iff] using
    (Nanuq.AmbientTransport.inside_predicate_iff H C x).symm

 theorem outside_image (H : Plane ≃ₜ Plane) (C : Set Plane) :
    H '' outside C = outside (H '' C) := by
  ext y
  obtain ⟨x,rfl⟩ := H.surjective y
  simpa only [H.injective.mem_set_image, mem_outside_iff] using
    (Nanuq.AmbientTransport.outside_predicate_iff H C x).symm

 theorem region_image (H : Plane ≃ₜ Plane) {C Ω : Set Plane}
    (hΩ : IsRegionOf C Ω) : IsRegionOf (H '' C) (H '' Ω) := by
  rcases hΩ with rfl | rfl
  · exact Or.inl (inside_image H C)
  · exact Or.inr (outside_image H C)

 theorem inverse_image_image (H : Plane ≃ₜ Plane) (S : Set Plane) :
    H.symm '' (H '' S) = S := by ext x; simp

/-- Arbitrary continuous crosscut in EITHER original complementary region.
The two output regions retain the supplied ORIGINAL boundary-arc labels. -/
theorem continuous_crosscut_region
    {C P A₁ A₂ Ω : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q)
    (hPC : P ∩ C = {p, q}) (hΩ : IsRegionOf C Ω)
    (hPD : P \ {p, q} ⊆ Ω) :
    ∃ V₁ V₂ : Set Plane,
      IsRegionOf (A₁ ∪ P) V₁ ∧ IsRegionOf (A₂ ∪ P) V₂ ∧
      Ω \ P = V₁ ∪ V₂ ∧ Disjoint V₁ V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧
      V₁ ≠ V₂ ∧
      (∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      closure V₁ ∩ C = A₁ ∧ closure V₂ ∩ C = A₂ := by
  have hmeet : ∀ z ∈ P, z ∈ A₁ → z = p ∨ z = q := by
    intro z hzP hzA
    have hz : z ∈ ({p,q} : Set Plane) := hPC ▸ ⟨hzP,hcut.fst_subset hzA⟩
    simpa using hz
  obtain ⟨H, -, -, -, -, hpoly⟩ :=
    Nanuq.PrescribedLoopAmbient.cycle_arc_straightening hP hcut.fst.reverse hmeet
  have hC' := jordan_image H hC
  have hcut' := hcut.image H.continuous.continuousOn H.injective.injOn
  have hP' : IsArcBetween (H '' P) (H p) (H q) :=
    hP.image_of_injOn (subset_univ P) H.continuous.continuousOn H.injective.injOn
  have hPC' : H '' P ∩ H '' C = {H p,H q} := by
    rw [← image_inter H.injective, hPC, image_pair]
  have hΩ' := region_image H hΩ
  have hPD' : (H '' P) \ {H p,H q} ⊆ H '' Ω := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hy.1
    refine mem_image_of_mem H (hPD ⟨hx,?_⟩)
    rintro (rfl | rfl)
    · exact hy.2 (by simp)
    · exact hy.2 (by simp)
  obtain ⟨W₁,W₂,hr₁,hr₂,heq,hdis,hn₁,hn₂,hne,hcomp₁,hcomp₂,hcl₁,hcl₂⟩ :=
    Nanuq.GeneralRegionCrosscut.polygonal_crosscut_region hC' hcut' hP' hpoly hPC' hΩ' hPD'
  let V₁ : Set Plane := H.symm '' W₁
  let V₂ : Set Plane := H.symm '' W₂
  have hV₁ : H '' V₁ = W₁ := by
    change H '' (H.symm '' W₁) = W₁
    exact inverse_image_image H.symm W₁
  have hV₂ : H '' V₂ = W₂ := by
    change H '' (H.symm '' W₂) = W₂
    exact inverse_image_image H.symm W₂
  have hreg₁ : IsRegionOf (A₁ ∪ P) V₁ := by
    have h := region_image H.symm hr₁
    rw [← image_union, inverse_image_image] at h
    exact h
  have hreg₂ : IsRegionOf (A₂ ∪ P) V₂ := by
    have h := region_image H.symm hr₂
    rw [← image_union, inverse_image_image] at h
    exact h
  have hdiff : H '' (Ω \ P) = (H '' Ω) \ H '' P :=
    Set.image_sdiff H.injective Ω P
  have heq' : Ω \ P = V₁ ∪ V₂ := by
    apply H.injective.image_injective
    rw [hdiff, image_union, hV₁, hV₂]
    exact heq
  have hdis' : Disjoint V₁ V₂ := by
    apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    have hy₁ : H x ∈ W₁ := hV₁ ▸ mem_image_of_mem H hx₁
    have hy₂ : H x ∈ W₂ := hV₂ ▸ mem_image_of_mem H hx₂
    exact Set.disjoint_left.mp hdis hy₁ hy₂
  have hne' : V₁ ≠ V₂ := by
    intro hh
    exact hne (hV₁.symm.trans ((congrArg (fun S => H '' S) hh).trans hV₂))
  have hc₁ : ∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁ := by
    intro z hz
    have hzD : z ∈ Ω \ P := heq'.symm ▸ (Or.inl hz : z ∈ V₁ ∪ V₂)
    have hzW : H z ∈ W₁ := hV₁ ▸ mem_image_of_mem H hz
    apply H.injective.image_injective
    rw [H.image_connectedComponentIn hzD, hdiff, hcomp₁ (H z) hzW, hV₁]
  have hc₂ : ∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂ := by
    intro z hz
    have hzD : z ∈ Ω \ P := heq'.symm ▸ (Or.inr hz : z ∈ V₁ ∪ V₂)
    have hzW : H z ∈ W₂ := hV₂ ▸ mem_image_of_mem H hz
    apply H.injective.image_injective
    rw [H.image_connectedComponentIn hzD, hdiff, hcomp₂ (H z) hzW, hV₂]
  have hcl₁' : closure V₁ ∩ C = A₁ :=
    Nanuq.AmbientTransport.closure_inter_pullback H V₁ C A₁ (by rw [hV₁]; exact hcl₁)
  have hcl₂' : closure V₂ ∩ C = A₂ :=
    Nanuq.AmbientTransport.closure_inter_pullback H V₂ C A₂ (by rw [hV₂]; exact hcl₂)
  exact ⟨V₁,V₂,hreg₁,hreg₂,heq',hdis',hn₁.image H.symm,hn₂.image H.symm,
    hne',hc₁,hc₂,hcl₁',hcl₂'⟩

#print axioms continuous_crosscut_region
end Nanuq.ContinuousRegionCrosscut
