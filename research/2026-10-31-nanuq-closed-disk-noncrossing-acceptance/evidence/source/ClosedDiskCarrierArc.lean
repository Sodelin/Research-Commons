import SquareCarrierArc
import ContinuousRegionCrosscut
import Schoenflies.JordanSchoenflies

/-! UNCOMPILED source draft. One ambient homeomorphism is used as a proof
device only; the returned arc and both exact endpoints are pulled back. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ClosedDiskNoncrossing
open Set Schoenflies

private theorem ambient_to_model {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ H : Plane ≃ₜ Plane, H '' C = modelCurve ∧
      H '' (C ∪ inside C) = Plane.closedSquare 0 1 := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨H,hH⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
  have hHC : H '' C = modelCurve := by
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      have he := (e ⟨x,hx⟩).property
      rw [← hH ⟨x,hx⟩] at he
      exact he
    · intro y hy
      obtain ⟨x,hxy⟩ := e.surjective ⟨y,hy⟩
      refine ⟨x.val,x.property,?_⟩
      exact (hH x).trans (congrArg Subtype.val hxy)
  refine ⟨H,hHC,?_⟩
  rw [Set.image_union,Nanuq.ContinuousRegionCrosscut.inside_image,hHC,modelCurve_union_inside]

/-- Exact-endpoint proper crosscut approximation of an ORIGINAL compact
connected carrier in the closed Jordan disk, avoiding ALL of K. This derives
accessibility using uniform compact clearance, never assumes an input collar. -/
theorem closed_disk_carrier_proper_arc
    {C P K : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hP : IsCompact P) (hPc : IsPreconnected P)
    (hK : IsCompact K) (hPK : Disjoint P K)
    (hPdisk : P ⊆ C ∪ inside C)
    (hp : p∈P) (hq : q∈P) (hpC : p∈C) (hqC : q∈C) (hpq : p≠q) :
    ∃ A : Set Plane, IsArcBetween A p q ∧ A∩C={p,q} ∧
      A \ {p,q} ⊆ inside C ∧ Disjoint A K := by
  obtain ⟨H,hHC,hHdisk⟩ := ambient_to_model hC
  have hdisj : Disjoint (H '' P) (H '' K) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x,hx,hxy⟩ ⟨z,hz,hzy⟩
    have hxz := H.injective (hxy.trans hzy.symm)
    subst z
    exact Set.disjoint_left.mp hPK hx hz
  have hPsq : H '' P ⊆ Plane.closedSquare 0 1 := by
    rw [← hHdisk]
    exact Set.image_mono hPdisk
  obtain ⟨A',hpoly,hA',hAi',hAK'⟩ := square_carrier_proper_arc
    (hP.image H.continuous) (hPc.image H H.continuous.continuousOn)
    (hK.image H.continuous) hdisj hPsq (mem_image_of_mem H hp)
    (mem_image_of_mem H hq) (fun h => hpq (H.injective h))
  let A : Set Plane := H.symm '' A'
  have hA : IsArcBetween A p q := by
    simpa only [Homeomorph.symm_apply_apply] using
      hA'.image_of_injOn (subset_univ A') H.symm.continuous.continuousOn H.symm.injective.injOn
  have hAi : A \ {p,q} ⊆ inside C := by
    rintro z ⟨⟨y,hy,hyz⟩,hzends⟩
    have hyends : y∉({H p,H q}:Set Plane) := by
      intro he
      rcases (show y = H p ∨ y = H q from by simpa using he) with he | he
      · have hz : z=p := hyz.symm.trans (by simpa only [he,Homeomorph.symm_apply_apply])
        exact hzends (by simp [hz])
      · have hz : z=q := hyz.symm.trans (by simpa only [he,Homeomorph.symm_apply_apply])
        exact hzends (by simp [hz])
    have hyin : y∈inside (H '' C) := by
      rw [hHC,inside_modelCurve]
      exact hAi' ⟨hy,hyends⟩
    rw [← Nanuq.ContinuousRegionCrosscut.inside_image H C] at hyin
    obtain ⟨w,hw,hwy⟩ := hyin
    have hyw : H.symm y=w := by
      rw [← hwy]
      exact H.symm_apply_apply w
    have hwz : w=z := hyw.symm.trans hyz
    exact hwz ▸ hw
  have hAC : A∩C={p,q} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzA,hzC⟩
      by_contra hz
      exact (hAi ⟨hzA,hz⟩).1 hzC
    · intro z hz
      rcases hz with rfl | rfl
      · exact ⟨hA.left_mem,hpC⟩
      · exact ⟨hA.right_mem,hqC⟩
  refine ⟨A,hA,hAC,hAi,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨y,hy,hyz⟩ hzK
  apply Set.disjoint_left.mp hAK' hy
  refine ⟨z,hzK,?_⟩
  rw [← hyz]
  exact H.apply_symm_apply y

#print axioms closed_disk_carrier_proper_arc
end Nanuq.ClosedDiskNoncrossing
