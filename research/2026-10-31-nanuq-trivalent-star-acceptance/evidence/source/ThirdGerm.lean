import HalfCrosscut
import SquareFirstExit

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval

 def reflectY : Plane ≃ₜ Plane where
  toFun z := Plane.mk (z 0) (-z 1)
  invFun z := Plane.mk (z 0) (-z 1)
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

 theorem straighten_upper_first_prefix (f : ℝ → Plane) (hf : ContinuousOn f I)
    (hi : InjOn f I) (h0 : f 0 = 0) {r s : ℝ} (hr : 0 < r)
    (hs : s ∈ I) (hsp : 0 < s) (he : max |f s 0| |f s 1| = r)
    (hbefore : ∀ t ∈ Icc 0 s, t < s → max |f t 0| |f t 1| < r)
    (hy : ∀ t ∈ Ioc 0 s, 0 < f t 1) :
    ∃ H : Plane ≃ₜ Plane, (∀ z : Plane, z 1 = 0 → H z = z) ∧
      H '' (f '' Icc 0 s) = segment ℝ (0:Plane) (f s) ∧ H (f s) = f s := by
  have hP : IsArcBetween (f '' Icc 0 s) 0 (f s) := by
    simpa only [h0,uIcc_of_le hsp.le] using
      isArcBetween_subarc_of_injOn_I hf hi zero_mem_I hs (ne_of_lt hsp)
  apply upper_prefix_straightening hr hP (hy s ⟨hsp,le_rfl⟩) he
  intro z hz
  obtain ⟨t,ht,rfl⟩ := hz.1
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro he
    apply hz.2
    left
    simpa only [← he,h0]
  have hts : t < s := by
    apply lt_of_le_of_ne ht.2
    intro he
    apply hz.2
    right
    simp [he]
  exact ⟨hy t ⟨ht0,ht.2⟩,hbefore t ht hts⟩

/-- The no-line-hit premise is an explicit intermediate consequence of the
actual first carrier and original distinct-edge incidence; source joins must derive it. -/
theorem line_preserving_third_germ (f : ℝ → Plane) (hf : ContinuousOn f I)
    (hi : InjOn f I) (h0 : f 0 = 0) {r : ℝ} (hr : 0 < r)
    (hend : r ≤ max |f 1 0| |f 1 1|)
    (hline : ∀ t ∈ I, 0 < t → max |f t 0| |f t 1| ≤ r → f t 1 ≠ 0) :
    ∃ (s : ℝ) (H : Plane ≃ₜ Plane) (q : Plane),
      s ∈ I ∧ 0 < s ∧ 0 < q 1 ∧
      (∀ z : Plane, z 1 = 0 → H z = z) ∧
      H '' (f '' Icc 0 s) = segment ℝ (0:Plane) q ∧ H (f s) = q := by
  obtain ⟨s,hs,hsp,he,hbefore⟩ := square_first_exit f hf h0 hr hend
  have hsub : Icc (0:ℝ) s ⊆ I := Icc_subset_Icc le_rfl hs.2
  have hbound : ∀ t ∈ Icc 0 s, max |f t 0| |f t 1| ≤ r := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with h | rfl
    · exact (hbefore t ht h).le
    · exact he.le
  have hyne : ∀ t ∈ Ioc 0 s, f t 1 ≠ 0 := fun t ht =>
    hline t (hsub ⟨ht.1.le,ht.2⟩) ht.1 (hbound t ⟨ht.1.le,ht.2⟩)
  have hyc : ContinuousOn (fun t => f t 1) (Icc 0 s) := by
    exact (show Continuous (fun z : Plane => z 1) by fun_prop).comp_continuousOn (hf.mono hsub)
  rcases sign_on_punctured_interval (fun t => f t 1) hsp hyc hyne with hy | hy
  · obtain ⟨H,hH,himage,hend⟩ := straighten_upper_first_prefix f hf hi h0 hr hs hsp he hbefore hy
    exact ⟨s,H,f s,hs,hsp,hy s ⟨hsp,le_rfl⟩,hH,himage,hend⟩
  · let g := fun t => reflectY (f t)
    have hgc : ContinuousOn g I := reflectY.continuous.comp_continuousOn hf
    have hgi : InjOn g I := fun t ht u hu h => hi ht hu (reflectY.injective h)
    have hg0 : g 0 = 0 := by simp [g,h0,reflectY]
    have hge : max |g s 0| |g s 1| = r := by simpa [g,reflectY] using he
    have hgb : ∀ t ∈ Icc 0 s, t < s → max |g t 0| |g t 1| < r := by
      intro t ht hts; simpa [g,reflectY] using hbefore t ht hts
    have hgy : ∀ t ∈ Ioc 0 s, 0 < g t 1 := by
      intro t ht; simpa [g,reflectY] using neg_pos.mpr (hy t ht)
    obtain ⟨H,hH,himage,hend⟩ := straighten_upper_first_prefix g hgc hgi hg0 hr hs hsp hge hgb hgy
    refine ⟨s,reflectY.trans H,g s,hs,hsp,hgy s ⟨hsp,le_rfl⟩,?_,?_,?_⟩
    · intro z hz
      have hez : reflectY z = z := by ext i; fin_cases i <;> simp [reflectY,hz]
      change H (reflectY z) = z
      rw [hez,hH z hz]
    · change (fun z => H (reflectY z)) '' (f '' Icc 0 s) = _
      rw [← Set.image_image (fun z => H z) (fun z => reflectY z) (f '' Icc 0 s)]
      have hgimage : reflectY '' (f '' Icc 0 s) = g '' Icc 0 s :=
        Set.image_image (fun z => reflectY z) f (Icc 0 s)
      rw [hgimage]
      exact himage
    · exact hend

#print axioms line_preserving_third_germ
end Nanuq.ActualStar
