import Schoenflies.Graph.VertexSquares
import Mathlib.Topology.Order.IntermediateValue

set_option debug.skipKernelTC false
/-! UNCOMPILED compact first exit and side selection; no finite-crossing
or metric-circle-once premise is used. -/
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval

 theorem square_first_exit (f : ℝ → Plane) (hf : ContinuousOn f I)
    (hzero : f 0 = 0) {r : ℝ} (hr : 0 < r)
    (hend : r ≤ max |f 1 0| |f 1 1|) :
    ∃ s ∈ I, 0 < s ∧ max |f s 0| |f s 1| = r ∧
      ∀ t ∈ Icc 0 s, t < s → max |f t 0| |f t 1| < r := by
  let a : Plane → ℝ := fun z => max |z 0| |z 1|
  have hac : Continuous a := by unfold a; fun_prop
  have hclosed : IsClosed {z : Plane | r ≤ a z} := isClosed_le continuous_const hac
  obtain ⟨s,hs,_,hsC,hfirst⟩ := exists_first_mem hf hclosed one_mem_I hend
  have hspos : 0 < s := by
    apply lt_of_le_of_ne hs.1
    intro he
    have hh : r ≤ (0:ℝ) := by simpa [← he,hzero,a] using hsC
    linarith
  have hsub : Icc (0:ℝ) s ⊆ I := Icc_subset_Icc le_rfl hs.2
  have hc : ContinuousOn (a ∘ f) (Icc 0 s) := (hac.comp_continuousOn hf).mono hsub
  have ha0 : (a ∘ f) 0 = 0 := by simp [Function.comp_apply,hzero,a]
  obtain ⟨u,hu,hue⟩ := intermediate_value_Icc hs.1 hc
    (show r ∈ Icc ((a ∘ f) 0) ((a ∘ f) s) from ⟨by rw [ha0]; exact hr.le,hsC⟩)
  have hsu : s ≤ u := by
    by_contra hn
    have huC : f u ∈ {z : Plane | r ≤ a z} := by
      change r ≤ (a ∘ f) u
      rw [hue]
    exact hfirst u (hsub hu) (lt_of_not_ge hn) huC
  have hus : u = s := le_antisymm hu.2 hsu
  have hse : a (f s) = r := by simpa only [hus,Function.comp_apply] using hue
  refine ⟨s,hs,hspos,hse,?_⟩
  intro t ht hts
  exact lt_of_not_ge (hfirst t (hsub ht) hts)

 theorem sign_on_punctured_interval (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hf : ContinuousOn f (Icc 0 s)) (hne : ∀ t ∈ Ioc 0 s, f t ≠ 0) :
    (∀ t ∈ Ioc 0 s, 0 < f t) ∨ (∀ t ∈ Ioc 0 s, f t < 0) := by
  rcases lt_or_gt_of_ne (hne s ⟨hs,le_rfl⟩) with hneg | hpos
  · right
    intro t ht
    by_contra hn
    have hft : 0 ≤ f t := le_of_not_gt hn
    have hsub : Icc t s ⊆ Icc (0:ℝ) s := Icc_subset_Icc ht.1.le le_rfl
    obtain ⟨u,hu,hue⟩ := intermediate_value_Icc' ht.2 (hf.mono hsub)
      (show (0:ℝ) ∈ Icc (f s) (f t) from ⟨hneg.le,hft⟩)
    exact hne u ⟨lt_of_lt_of_le ht.1 hu.1,hu.2⟩ hue
  · left
    intro t ht
    by_contra hn
    have hft : f t ≤ 0 := le_of_not_gt hn
    have hsub : Icc t s ⊆ Icc (0:ℝ) s := Icc_subset_Icc ht.1.le le_rfl
    obtain ⟨u,hu,hue⟩ := intermediate_value_Icc ht.2 (hf.mono hsub)
      (show (0:ℝ) ∈ Icc (f t) (f s) from ⟨hft,hpos.le⟩)
    exact hne u ⟨lt_of_lt_of_le ht.1 hu.1,hu.2⟩ hue

#print axioms square_first_exit
#print axioms sign_on_punctured_interval
end Nanuq.ActualStar
