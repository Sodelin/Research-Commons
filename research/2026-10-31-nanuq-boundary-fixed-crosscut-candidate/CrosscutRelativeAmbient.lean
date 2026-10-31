import FixedCrosscutExtension

set_option debug.skipKernelTC false
/-! UNCOMPILED closure: derive the matching map from actual crosscut arcs.
The endpoint-matching homeomorphism is NOT an added input certificate. -/
namespace Nanuq.RelativeCrosscut
open Set Schoenflies unitInterval

 theorem matching_map_of_crosscuts {C P Q A₁ A₂ : Set Plane} {p q : Plane}
    (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hQ : IsArcBetween Q p q)
    (hPC : P ∩ C = {p,q}) (hQC : Q ∩ C = {p,q}) :
    ∃ M : Plane ≃ₜ Plane, M '' P = Q ∧ M p = p ∧ M q = q := by
  obtain ⟨f,hfc,hfi,hfim,hf0,hf1⟩ := hcut.fst
  obtain ⟨g,hgc,hgi,hgim,hg0,hg1⟩ := hP.reverse
  obtain ⟨k,hkc,hki,hkim,hk0,hk1⟩ := hQ.reverse
  have hm : f 1 = g 0 := by rw [hf1,hg0]
  have hm' : f 1 = k 0 := by rw [hf1,hk0]
  have hl : IsLoop (concatenate f g) := IsLoop.concatenate hfc hfi hgc hgi hm
    (by rw [hg1,hf0]) (by
      intro z hz hz'
      rw [hfim] at hz
      rw [hgim] at hz'
      rw [hf0,hf1]
      have he : z ∈ ({p,q} : Set Plane) := hPC ▸ ⟨hz',hcut.fst_subset hz⟩
      simpa using he)
  have hl' : IsLoop (concatenate f k) := IsLoop.concatenate hfc hfi hkc hki hm'
    (by rw [hk1,hf0]) (by
      intro z hz hz'
      rw [hfim] at hz
      rw [hkim] at hz'
      rw [hf0,hf1]
      have he : z ∈ ({p,q} : Set Plane) := hQC ▸ ⟨hz',hcut.fst_subset hz⟩
      simpa using he)
  obtain ⟨M,hparam,hsub⟩ := Nanuq.PrescribedLoopAmbient.loop_parameters hl hl'
  have him := hsub upperHalf upperHalf_subset_I
  rw [Nanuq.PrescribedLoopAmbient.image_upper_half f g hm,
    Nanuq.PrescribedLoopAmbient.image_upper_half f k hm',hgim,hkim] at him
  have hp := hparam 0 zero_mem_I
  rw [concatenate_zero,concatenate_zero,hf0] at hp
  have hq := hparam (1/2) (show (1/2:ℝ) ∈ I by norm_num)
  rw [concatenate_of_le le_rfl,concatenate_of_le le_rfl] at hq
  have hq' : M q = q := by
    have he : (2:ℝ)*(1/2)=1 := by norm_num
    simpa only [he,hf1] using hq
  exact ⟨M,him,hp,hq'⟩

/-- A continuous crosscut can be carried to another with the SAME endpoints,
fixing the entire original closed exterior pointwise. No prescribed map,
polygonality, collar or order certificate is required as input. -/
theorem crosscut_fixed_ambient {C P Q A₁ A₂ : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hQ : IsArcBetween Q p q)
    (hPC : P ∩ C = {p,q}) (hQC : Q ∩ C = {p,q})
    (hPI : P \ {p,q} ⊆ inside C) (hQI : Q \ {p,q} ⊆ inside C) :
    ∃ H : Plane ≃ₜ Plane, EqOn H id (C ∪ outside C) ∧ H '' P = Q := by
  obtain ⟨M,hMP,hMp,hMq⟩ := matching_map_of_crosscuts hcut hP hQ hPC hQC
  have hmn : IsHomeoOn M M.symm P Q := by
    refine ⟨?_,?_,M.continuous.continuousOn,M.symm.continuous.continuousOn,?_,?_⟩
    · intro z hz; rw [← hMP]; exact mem_image_of_mem M hz
    · intro z hz
      rw [← hMP] at hz
      obtain ⟨x,hx,rfl⟩ := hz
      simpa using hx
    · intro z _; exact M.symm_apply_apply z
    · intro z _; exact M.apply_symm_apply z
  have hfix : EqOn M id {p,q} := by
    rintro z (rfl | rfl)
    · exact hMp
    · exact hMq
  obtain ⟨H,hHE,hHM⟩ := bounded_crosscut_fixed_extension
    hC hcut hP hQ hPC hQC hPI hQI hmn hfix
  exact ⟨H,hHE,(Set.EqOn.image_eq hHM).trans hMP⟩

#print axioms crosscut_fixed_ambient
end Nanuq.RelativeCrosscut
