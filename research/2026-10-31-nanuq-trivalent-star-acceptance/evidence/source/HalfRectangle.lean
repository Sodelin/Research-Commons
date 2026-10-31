import CrosscutRelativeAmbient

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies

 def halfFrame (r : ℝ) (hr : 0 < r) : Plane ≃ₜ Plane where
  toFun z := Plane.mk (r * z 0) (r * (z 1 + 1) / 2)
  invFun z := Plane.mk (z 0 / r) (2 * z 1 / r - 1)
  left_inv z := by
    ext i
    fin_cases i <;> simp <;> field_simp [ne_of_gt hr] <;> ring
  right_inv z := by
    ext i
    fin_cases i <;> simp <;> field_simp [ne_of_gt hr] <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

 def halfBoundary (r : ℝ) (hr : 0 < r) : Set Plane := halfFrame r hr '' modelCurve

 theorem halfBoundary_jordan (r : ℝ) (hr : 0 < r) : IsJordanCurve (halfBoundary r hr) :=
  Nanuq.ContinuousRegionCrosscut.jordan_image (halfFrame r hr) isJordanCurve_modelCurve

 theorem homeomorph_mem_image (H : Plane ≃ₜ Plane) (S : Set Plane) (x : Plane) :
    x ∈ H '' S ↔ H.symm x ∈ S := by
  constructor
  · rintro ⟨z,hz,rfl⟩; simpa using hz
  · intro hx; exact ⟨H.symm x,hx,H.apply_symm_apply x⟩

 theorem mem_half_inside (r : ℝ) (hr : 0 < r) (x : Plane) :
    x ∈ inside (halfBoundary r hr) ↔
      -r < x 0 ∧ x 0 < r ∧ 0 < x 1 ∧ x 1 < r := by
  unfold halfBoundary
  rw [← Nanuq.ContinuousRegionCrosscut.inside_image,homeomorph_mem_image,
    inside_modelCurve,Plane.openSquare_eq_inter]
  change ((0:ℝ)-1 < x 0/r ∧ x 0/r < 0+1) ∧
    ((0:ℝ)-1 < 2*x 1/r-1 ∧ 2*x 1/r-1 < 0+1) ↔ _
  norm_num only [zero_sub,zero_add]
  have hxlo : -1 < x 0/r ↔ -r < x 0 := by rw [lt_div_iff₀ hr]; ring_nf
  have hxhi : x 0/r < 1 ↔ x 0 < r := by rw [div_lt_iff₀ hr]; ring_nf
  have hylo : -1 < 2*x 1/r-1 ↔ 0 < x 1 := by
    constructor
    · intro h
      have h' : 0 < 2*x 1/r := by linarith
      have h'' := (lt_div_iff₀ hr).mp h'
      nlinarith
    · intro h
      have h' : 0 < 2*x 1/r := (lt_div_iff₀ hr).mpr (by nlinarith)
      linarith
  have hyhi : 2*x 1/r-1 < 1 ↔ x 1 < r := by
    constructor
    · intro h
      have h' : 2*x 1/r < 2 := by linarith
      have h'' := (div_lt_iff₀ hr).mp h'
      nlinarith
    · intro h
      have h' : 2*x 1/r < 2 := (div_lt_iff₀ hr).mpr (by nlinarith)
      linarith
  rw [hxlo,hxhi,hylo,hyhi]
  tauto

 theorem zero_mem_half_boundary (r : ℝ) (hr : 0 < r) : (0 : Plane) ∈ halfBoundary r hr := by
  refine ⟨Plane.mk 0 (-1), ?_, ?_⟩
  · change max |(0:ℝ)| |(-1:ℝ)| = 1
    norm_num
  · ext i
    fin_cases i <;> norm_num [halfFrame]

 theorem mem_half_boundary_of_exit {r : ℝ} (hr : 0 < r) {x : Plane}
    (hy : 0 < x 1) (hexit : max |x 0| |x 1| = r) : x ∈ halfBoundary r hr := by
  rw [halfBoundary,homeomorph_mem_image]
  change max |x 0/r| |2*x 1/r-1| = 1
  have hx : |x 0| ≤ r := (le_max_left _ _).trans_eq hexit
  have hyr : x 1 ≤ r := by
    have := (le_max_right |x 0| |x 1|).trans_eq hexit
    simpa only [abs_of_pos hy] using this
  have hxb : |x 0/r| ≤ 1 := by
    rw [abs_div,abs_of_pos hr,div_le_iff₀ hr]
    simpa using hx
  have hdiv0 : 0 ≤ 2*x 1/r := le_of_lt ((lt_div_iff₀ hr).mpr (by nlinarith))
  have hdiv2 : 2*x 1/r ≤ 2 := (div_le_iff₀ hr).mpr (by nlinarith)
  have hyb : |2*x 1/r-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [abs_of_pos hy] at hexit
  rcases le_total |x 0| (x 1) with h | h
  · rw [max_eq_right h] at hexit
    rw [hexit]
    have he : (2:ℝ)*r/r-1 = 1 := by field_simp [ne_of_gt hr]; ring
    rw [he]
    norm_num only [abs_one]
    exact max_eq_right hxb
  · rw [max_eq_left h] at hexit
    have he : |x 0/r| = 1 := by rw [abs_div,abs_of_pos hr,hexit]; exact div_self (ne_of_gt hr)
    rw [he]
    exact max_eq_left hyb

 theorem horizontal_in_closed_exterior (r : ℝ) (hr : 0 < r) {x : Plane}
    (hy : x 1 = 0) : x ∈ halfBoundary r hr ∪ outside (halfBoundary r hr) := by
  have hn : x ∉ inside (halfBoundary r hr) := by
    intro hx
    have hh := ((mem_half_inside r hr x).mp hx).2.2.1
    simpa [hy] using hh
  by_cases hx : x ∈ halfBoundary r hr
  · exact Or.inl hx
  · exact Or.inr (mem_outside_of_notMem_union_inside (by
      intro h
      exact h.elim hx hn))

#print axioms mem_half_inside
#print axioms mem_half_boundary_of_exit
end Nanuq.ActualStar
