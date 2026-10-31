import ContinuedArms
import StraightCarrier

set_option debug.skipKernelTC false
/-! UNCOMPILED part of the actual-star construction. Actual continued arms,
not an assumed local disk or cyclic order, supply the first straight carrier. -/
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval

 theorem horizontal_nonendpoint {z : Plane} (hz : z ∈ Nanuq.CornerShear.horizontal)
    (hp : z ≠ Plane.mk 2 0) (hm : z ≠ Plane.mk (-2) 0) : |z 0| < 2 := by
  change z 1 = 0 ∧ |z 0| ≤ 2 at hz
  by_contra hn
  have he : |z 0| = 2 := le_antisymm hz.2 (le_of_not_gt hn)
  rcases le_total 0 (z 0) with h | h
  · have hx : z 0 = 2 := by simpa only [abs_of_nonneg h] using he
    apply hp
    ext i
    fin_cases i <;> simp [hx,hz.1]
  · have hx : z 0 = -2 := by rw [abs_of_nonpos h] at he; linarith
    apply hm
    ext i
    fin_cases i <;> simp [hx,hz.1]

 theorem straighten_two_continued_germs
    (f g : ℝ → Plane) (hfc : ContinuousOn f I) (hgc : ContinuousOn g I)
    (hfi : InjOn f I) (hgi : InjOn g I) (h0 : f 0 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0) :
    ∃ H : Plane ≃ₜ Plane,
      H '' (f '' Icc 0 (1/3) ∪ g '' Icc 0 (1/3)) = Nanuq.CornerShear.horizontal ∧
      H (f (1/3)) = Plane.mk 2 0 ∧ H (g (1/3)) = Plane.mk (-2) 0 ∧
      (H (f 0)) 1 = 0 ∧ |(H (f 0)) 0| < 2 := by
  have haI : (1/3:ℝ) ∈ I := by norm_num
  have ha0 : (0:ℝ) < 1/3 := by norm_num
  have hIa : Icc (0:ℝ) (1/3) ⊆ I := Icc_subset_Icc le_rfl haI.2
  have hA₁ : IsArcBetween (f '' Icc 0 (1/3)) (f 0) (f (1/3)) := by
    simpa only [uIcc_of_le ha0.le] using
      isArcBetween_subarc_of_injOn_I hfc hfi zero_mem_I haI (ne_of_lt ha0)
  have hA₂ : IsArcBetween (g '' Icc 0 (1/3)) (f 0) (g (1/3)) := by
    rw [h0]
    simpa only [uIcc_of_le ha0.le] using
      isArcBetween_subarc_of_injOn_I hgc hgi zero_mem_I haI (ne_of_lt ha0)
  have hA : IsArcBetween (f '' Icc 0 (1/3) ∪ g '' Icc 0 (1/3))
      (f (1/3)) (g (1/3)) := hA₁.reverse.concatenate hA₂
    (fun z hz₁ hz₂ => hmeet z (image_mono hIa hz₁) (image_mono hIa hz₂))
  obtain ⟨B,hB,hAB,_,_⟩ := Nanuq.ContinuedArms.jordan_through_two_germs
    f g hfc hgc hfi hgi h0 hmeet
  have hmeetB : ∀ z ∈ f '' Icc 0 (1/3) ∪ g '' Icc 0 (1/3),
      z ∈ B → z = f (1/3) ∨ z = g (1/3) := by
    intro z hz hzB
    have he : z ∈ ({f (1/3),g (1/3)} : Set Plane) := hAB ▸ ⟨hz,hzB⟩
    simpa using he
  obtain ⟨H,hH,hp,hq⟩ := Nanuq.StraightCarrier.two_arc_straight_carrier hA hB.reverse hmeetB
  have hv : H (f 0) ∈ Nanuq.CornerShear.horizontal :=
    hH ▸ mem_image_of_mem H (Or.inl hA₁.left_mem)
  have hvp : H (f 0) ≠ Plane.mk 2 0 := by
    intro he
    have hh := hfi zero_mem_I haI (H.injective (he.trans hp.symm))
    norm_num at hh
  have hvq : H (f 0) ≠ Plane.mk (-2) 0 := by
    intro he
    have hh := hgi zero_mem_I haI (h0.symm.trans (H.injective (he.trans hq.symm)))
    norm_num at hh
  exact ⟨H,hH,hp,hq,hv.1,horizontal_nonendpoint hv hvp hvq⟩

#print axioms straighten_two_continued_germs
end Nanuq.ActualStar
