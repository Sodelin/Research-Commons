import TwoGermCarrier

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval

/-- Scalar injectivity is DERIVED from the whole same-plane arc, not an order premise. -/
theorem horizontal_coordinate_inj {f : ℝ → Plane} {a b : ℝ}
    (hi : InjOn f (Icc a b)) (hy : ∀ t ∈ Icc a b, f t 1 = 0) :
    InjOn (fun t => f t 0) (Icc a b) := by
  intro t ht u hu he
  apply hi ht hu
  ext i
  fin_cases i
  · exact he
  · rw [hy t ht,hy u hu]

theorem horizontal_arc_image {f : ℝ → Plane} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hi : InjOn f (Icc a b))
    (hy : ∀ t ∈ Icc a b, f t 1 = 0) :
    f '' Icc a b = segment ℝ (f a) (f b) := by
  have hsc : ContinuousOn (fun t => f t 0) (Icc a b) :=
    (show Continuous (fun z : Plane => z 0) by fun_prop).comp_continuousOn hc
  have hsi := horizontal_coordinate_inj hi hy
  have hscalar : (fun t => f t 0) '' Icc a b = segment ℝ (f a 0) (f b 0) := by
    rcases hsc.strictMonoOn_of_injOn_Icc' hab hsi with hm | hm
    · rw [segment_eq_Icc (hm.monotoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab)]
      exact hsc.image_Icc_of_monotoneOn hab hm.monotoneOn
    · rw [segment_symm,segment_eq_Icc (hm.antitoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab)]
      exact hsc.image_Icc_of_antitoneOn hab hm.antitoneOn
  have hfa : f a = Plane.mk (f a 0) 0 := by
    ext i; fin_cases i <;> simp [hy a ⟨le_rfl,hab⟩]
  have hfb : f b = Plane.mk (f b 0) 0 := by
    ext i; fin_cases i <;> simp [hy b ⟨hab,le_rfl⟩]
  ext z
  rw [hfa,hfb,mem_segment_horiz]
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨hy t ht,hscalar ▸ ⟨t,ht,rfl⟩⟩
  · rintro ⟨hzy,hzx⟩
    have hzimage : z 0 ∈ (fun t => f t 0) '' Icc a b := hscalar.symm ▸ hzx
    obtain ⟨t,ht,he⟩ := hzimage
    refine ⟨t,ht,?_⟩
    ext i
    fin_cases i
    · exact he
    · rw [hy t ht,hzy]

/-- Change only the interval parameter, preserving the exact original edge image. -/
theorem half_parameter_image (f : ℝ → Plane) :
    (fun t => f (t/2)) '' I = f '' Icc 0 (1/2) := by
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨t/2,⟨by linarith [ht.1],by linarith [ht.2]⟩,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    refine ⟨2*t,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    congr 1
    ring

end Nanuq.Pendant
