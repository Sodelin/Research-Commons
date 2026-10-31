import CornerShear
import CycleArcStraightening

set_option debug.skipKernelTC false
/-! UNCOMPILED same-map source adapter. Straightens the entire prescribed
first cycle arc, including its possible model corner. No star/order claim. -/
namespace Nanuq.StraightCarrier
open Set Schoenflies

theorem upperL_eq : Nanuq.CornerShear.upperL = sideTop ∪ sideLeft := by
  ext p
  simp only [Nanuq.CornerShear.upperL, Set.mem_setOf_eq, Set.mem_union,
    mem_sideTop, mem_sideLeft]

theorem two_arc_straight_carrier {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B q p)
    (hmeet : ∀ z ∈ A, z ∈ B → z = p ∨ z = q) :
    ∃ H : Plane ≃ₜ Plane,
      H '' A = Nanuq.CornerShear.horizontal ∧
      H p = Plane.mk 2 0 ∧ H q = Plane.mk (-2) 0 := by
  obtain ⟨H,hA',_,hp,hq,_⟩ :=
    Nanuq.PrescribedLoopAmbient.cycle_arc_straightening hA hB hmeet
  refine ⟨H.trans Nanuq.CornerShear.straighten, ?_, ?_, ?_⟩
  · change (Nanuq.CornerShear.straighten ∘ H) '' A = _
    rw [← Set.image_image, hA', ← upperL_eq]
    exact Nanuq.CornerShear.image_upperL
  · change Nanuq.CornerShear.straighten (H p) = _
    rw [hp]
    ext i
    fin_cases i <;> norm_num [Nanuq.CornerShear.straighten,
      Nanuq.CornerShear.forward, cornerNE]
  · change Nanuq.CornerShear.straighten (H q) = _
    rw [hq]
    ext i
    fin_cases i <;> norm_num [Nanuq.CornerShear.straighten,
      Nanuq.CornerShear.forward, cornerSW]

#print axioms two_arc_straight_carrier
end Nanuq.StraightCarrier
