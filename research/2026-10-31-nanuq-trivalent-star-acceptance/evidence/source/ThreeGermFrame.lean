import ThirdGerm
import TwoGermCarrier

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval

 def shiftVertex (v : Plane) : Plane ≃ₜ Plane where
  toFun z := z-v
  invFun z := z+v
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

 def centeredCarrier (c : ℝ) : Set Plane := {z | z 1 = 0 ∧ |z 0+c| ≤ 2}

 theorem image_shift_horizontal {v : Plane} (hv : v 1 = 0) :
    shiftVertex v '' Nanuq.CornerShear.horizontal = centeredCarrier (v 0) := by
  ext z
  rw [homeomorph_mem_image]
  change (z 1+v 1=0 ∧ |z 0+v 0| ≤ 2) ↔ (z 1=0 ∧ |z 0+v 0| ≤ 2)
  rw [hv,add_zero]

 theorem max_coordinates_pos {z : Plane} (hz : z ≠ 0) : 0 < max |z 0| |z 1| := by
  by_contra hn
  have hle : max |z 0| |z 1| ≤ 0 := le_of_not_gt hn
  have hz0 : z 0 = 0 := abs_nonpos_iff.mp ((le_max_left _ _).trans hle)
  have hz1 : z 1 = 0 := abs_nonpos_iff.mp ((le_max_right _ _).trans hle)
  apply hz
  ext i
  fin_cases i <;> simp [hz0,hz1]

/-- Complete three-arm frame from continued injective arms. The source wrapper
below supplies these arms from ORIGINAL distinct edge IDs; no line avoidance,
collar, cyclic order, or intermediate homeomorphism is an input. -/
theorem three_continued_germ_frame (f : Fin 3 → ℝ → Plane)
    (hc : ∀ i, ContinuousOn (f i) I) (hi : ∀ i, InjOn (f i) I)
    (hzero : ∀ i, f i 0 = f 0 0)
    (hmeet : ∀ i j, i ≠ j → ∀ z ∈ f i '' I, z ∈ f j '' I → z = f 0 0) :
    ∃ (H : Plane ≃ₜ Plane) (c s : ℝ) (q : Plane),
      |c| < 2 ∧ s ∈ I ∧ 0 < s ∧ 0 < q 1 ∧ H (f 0 0) = 0 ∧
      H '' (f 0 '' Icc 0 (1/3) ∪ f 1 '' Icc 0 (1/3)) = centeredCarrier c ∧
      H '' (f 2 '' Icc 0 s) = segment ℝ (0:Plane) q ∧
      H (f 0 (1/3)) = Plane.mk (2-c) 0 ∧
      H (f 1 (1/3)) = Plane.mk (-2-c) 0 ∧ H (f 2 s) = q := by
  have h01 : (0:Fin 3) ≠ 1 := by decide
  obtain ⟨H,hHA,hp,hq,hvy,hvc⟩ := straighten_two_continued_germs
    (f 0) (f 1) (hc 0) (hc 1) (hi 0) (hi 1) (hzero 1).symm
    (hmeet 0 1 h01)
  let v := H (f 0 0)
  let c := v 0
  let K := H.trans (shiftVertex v)
  let A := f 0 '' Icc 0 (1/3) ∪ f 1 '' Icc 0 (1/3)
  have hK0 : K (f 0 0) = 0 := by change H (f 0 0)-v=0; simp [v]
  have hKA : K '' A = centeredCarrier c := by
    change (fun z => shiftVertex v (H z)) '' A = _
    rw [← Set.image_image (fun z => shiftVertex v z) (fun z => H z) A]
    rw [hHA]
    exact image_shift_horizontal hvy
  let g := fun t => K (f 2 t)
  have hgc : ContinuousOn g I := K.continuous.comp_continuousOn (hc 2)
  have hgi : InjOn g I := fun t ht u hu h => hi 2 ht hu (K.injective h)
  have hg0 : g 0 = 0 := by simpa only [g,hzero 2] using hK0
  have hg1 : g 1 ≠ 0 := by
    intro he
    have h10 : (1:ℝ)=0 := hi 2 one_mem_I zero_mem_I (K.injective (he.trans hg0.symm))
    norm_num at h10
  let b := max |g 1 0| |g 1 1|
  have hb : 0 < b := max_coordinates_pos hg1
  let r := min ((2-|c|)/2) (b/2)
  have hr : 0 < r := lt_min (by dsimp [c,v]; linarith) (by linarith)
  have hrmargin : r+|c| < 2 := by
    have hh : r ≤ (2-|c|)/2 := min_le_left _ _
    linarith
  have hrend : r ≤ max |g 1 0| |g 1 1| := by
    have hh : r ≤ b/2 := min_le_right _ _
    change r ≤ b
    linarith
  have hIa : Icc (0:ℝ) (1/3) ⊆ I := Icc_subset_Icc le_rfl (by norm_num)
  have hline : ∀ t ∈ I, 0 < t → max |g t 0| |g t 1| ≤ r → g t 1 ≠ 0 := by
    intro t ht htp hbound hy
    have hx : |g t 0| ≤ r := (le_max_left _ _).trans hbound
    have hxin : |g t 0+c| ≤ 2 := le_of_lt (lt_of_le_of_lt
      (abs_add_le (g t 0) c) (by linarith))
    have hgin : g t ∈ centeredCarrier c := ⟨hy,hxin⟩
    have him : g t ∈ K '' A := hKA.symm ▸ hgin
    obtain ⟨z,hz,hzK⟩ := him
    have hzEq : z = f 2 t := K.injective hzK
    rw [hzEq] at hz
    have hft : f 2 t = f 0 0 := by
      rcases hz with hz | hz
      · exact hmeet 0 2 (by decide) _ (image_mono hIa hz) ⟨t,ht,rfl⟩
      · exact hmeet 1 2 (by decide) _ (image_mono hIa hz) ⟨t,ht,rfl⟩
    have ht0 : t=0 := hi 2 ht zero_mem_I (hft.trans (hzero 2).symm)
    linarith
  obtain ⟨s,R,q,hs,hsp,hqy,hRline,hRimage,hRend⟩ := line_preserving_third_germ
    g hgc hgi hg0 hr hrend hline
  have hRcarrier : R '' centeredCarrier c = centeredCarrier c := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hRline x hx.1]
      exact hx
    · intro hz
      exact ⟨z,hz,hRline z hz.1⟩
  refine ⟨K.trans R,c,s,q,hvc,hs,hsp,hqy,?_,?_,?_,?_,?_,?_⟩
  · change R (K (f 0 0)) = 0
    rw [hK0,hRline 0 (by simp)]
  · change (fun z => R (K z)) '' A = _
    rw [← Set.image_image (fun z => R z) (fun z => K z) A,hKA,hRcarrier]
  · change (fun z => R (K z)) '' (f 2 '' Icc 0 s) = _
    rw [← Set.image_image (fun z => R z) (fun z => K z) (f 2 '' Icc 0 s)]
    have hgi' : K '' (f 2 '' Icc 0 s) = g '' Icc 0 s :=
      Set.image_image (fun z => K z) (f 2) (Icc 0 s)
    rw [hgi']
    exact hRimage
  · have hKp : K (f 0 (1/3)) = Plane.mk (2-c) 0 := by
      change H (f 0 (1/3))-v = _
      rw [hp]
      ext i
      fin_cases i <;> simp [c,v,hvy]
    change R (K (f 0 (1/3))) = _
    rw [hKp,hRline _ (by simp)]
  · have hKq : K (f 1 (1/3)) = Plane.mk (-2-c) 0 := by
      change H (f 1 (1/3))-v = _
      rw [hq]
      ext i
      fin_cases i <;> simp [c,v,hvy]
    change R (K (f 1 (1/3))) = _
    rw [hKq,hRline _ (by simp)]
  · exact hRend

#print axioms three_continued_germ_frame
end Nanuq.ActualStar
