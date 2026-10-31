import HalfRectangle

set_option debug.skipKernelTC false
namespace Nanuq.ActualStar
open Set Schoenflies

 theorem crosscut_intersection_of_inside {C P : Set Plane} {p q : Plane}
    (hP : IsArcBetween P p q) (hp : p ∈ C) (hq : q ∈ C)
    (hPI : P \ {p,q} ⊆ inside C) : P ∩ C = {p,q} := by
  apply Subset.antisymm
  · intro z hz
    by_contra hn
    exact inside_subset_compl (hPI ⟨hz.1,hn⟩) hz.2
  · rintro z (rfl | rfl)
    · exact ⟨hP.left_mem,hp⟩
    · exact ⟨hP.right_mem,hq⟩

 theorem chord_inside_half {r : ℝ} (hr : 0 < r) {q : Plane}
    (hqy : 0 < q 1) (hq : max |q 0| |q 1| = r) :
    segment ℝ (0:Plane) q \ {0,q} ⊆ inside (halfBoundary r hr) := by
  intro z hz
  have hz0 : (0:Plane) ≠ z := fun h => hz.2 (Or.inl h.symm)
  have hzq : q ≠ z := fun h => hz.2 (Or.inr h.symm)
  have hzopen := mem_openSegment_of_ne_left_right hz0 hzq hz.1
  rw [openSegment_eq_image_lineMap] at hzopen
  obtain ⟨t,ht,rfl⟩ := hzopen
  apply (mem_half_inside r hr _).mpr
  have hqx : |q 0| ≤ r := (le_max_left _ _).trans_eq hq
  have hqy' : q 1 ≤ r := by
    have := (le_max_right |q 0| |q 1|).trans_eq hq
    simpa only [abs_of_pos hqy] using this
  have htr : t*r < r := mul_lt_of_lt_one_left hr ht.2
  have htx : |t*q 0| < r := by
    rw [abs_mul,abs_of_pos ht.1]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hqx ht.1.le) htr
  have hty : t*q 1 < r :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hqy' ht.1.le) htr
  have hpos : 0 < t*q 1 := mul_pos ht.1 hqy
  have hx := abs_lt.mp htx
  simpa [AffineMap.lineMap_apply] using (show
    -r < t*q 0 ∧ t*q 0 < r ∧ 0 < t*q 1 ∧ t*q 1 < r from ⟨hx.1,hx.2,hpos,hty⟩)

/-- The radius/side inequalities are the explicit intermediate output of
first-exit localization, not an additional admitted-source hypothesis. -/
theorem upper_prefix_straightening {r : ℝ} (hr : 0 < r) {q : Plane} {P : Set Plane}
    (hP : IsArcBetween P 0 q) (hqy : 0 < q 1) (hq : max |q 0| |q 1| = r)
    (hinner : ∀ z ∈ P \ {0,q}, 0 < z 1 ∧ max |z 0| |z 1| < r) :
    ∃ H : Plane ≃ₜ Plane, (∀ z : Plane, z 1 = 0 → H z = z) ∧
      H '' P = segment ℝ (0:Plane) q ∧ H q = q := by
  have hC := halfBoundary_jordan r hr
  have hpC := zero_mem_half_boundary r hr
  have hqC := mem_half_boundary_of_exit hr hqy hq
  have hpq : (0:Plane) ≠ q := by
    intro he
    have hh : q 1 = 0 := by rw [← he]; rfl
    linarith
  obtain ⟨A₁,A₂,hcut⟩ := exists_isCutPair hC hpC hqC hpq
  have hPI : P \ {0,q} ⊆ inside (halfBoundary r hr) := by
    intro z hz
    obtain ⟨hzy,hzn⟩ := hinner z hz
    have hzx : |z 0| < r := lt_of_le_of_lt (le_max_left _ _) hzn
    have hzr : z 1 < r := by
      have := lt_of_le_of_lt (le_max_right |z 0| |z 1|) hzn
      simpa only [abs_of_pos hzy] using this
    exact (mem_half_inside r hr z).mpr ⟨(abs_lt.mp hzx).1,(abs_lt.mp hzx).2,hzy,hzr⟩
  have hQ : IsArcBetween (segment ℝ (0:Plane) q) 0 q := isArcBetween_segment hpq
  have hQI := chord_inside_half hr hqy hq
  have hPC := crosscut_intersection_of_inside hP hpC hqC hPI
  have hQC := crosscut_intersection_of_inside hQ hpC hqC hQI
  obtain ⟨H,hfix,himage⟩ := Nanuq.RelativeCrosscut.crosscut_fixed_ambient
    hC hcut hP hQ hPC hQC hPI hQI
  exact ⟨H,fun z hz => hfix (horizontal_in_closed_exterior r hr hz),himage,hfix (Or.inl hqC)⟩

#print axioms upper_prefix_straightening
end Nanuq.ActualStar
