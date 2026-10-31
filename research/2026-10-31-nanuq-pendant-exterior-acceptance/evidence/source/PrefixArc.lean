import Schoenflies.Curve
import Mathlib.Tactic

/-! UNCOMPILED interval restriction of the SAME original parametrization. -/
namespace Nanuq.Pendant
open Set Schoenflies unitInterval

theorem prefix_isArcBetween (f : ℝ → Plane) (hc : ContinuousOn f I) (hi : InjOn f I)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    IsArcBetween (f '' Icc 0 t) (f 0) (f t) := by
  let g : ℝ → Plane := fun u => f (t*u)
  have htu : ∀ u∈I, t*u∈Icc 0 t := by
    intro u hu
    exact ⟨mul_nonneg ht.le hu.1,by nlinarith [hu.2]⟩
  have hI : Icc (0:ℝ) t ⊆ I := Icc_subset_Icc le_rfl ht1
  have hg : ContinuousOn g I := hc.comp (by fun_prop) (fun u hu => hI (htu u hu))
  have hgi : InjOn g I := by
    intro u hu v hv heq
    have hh := hi (hI (htu u hu)) (hI (htu v hv)) heq
    nlinarith
  refine ⟨g,hg,hgi,?_,by simp [g],by simp [g]⟩
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨t*u,htu u hu,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    refine ⟨v/t,⟨div_nonneg hv.1 ht.le,?_⟩,?_⟩
    · apply (div_le_iff₀ ht).mpr
      simpa using hv.2
    · change f (t*(v/t))=f v
      congr 1
      field_simp [ht.ne']

#print axioms prefix_isArcBetween
end Nanuq.Pendant
