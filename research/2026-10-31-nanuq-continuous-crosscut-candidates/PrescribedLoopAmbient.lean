import Schoenflies.JordanSchoenflies

set_option debug.skipKernelTC false
/-! UNCOMPILED own-source adapter. Uses the qualified supplier's parameter-
matching boundary homeomorphism and its relative ambient extension. This is
not an arbitrary redrawing and does not invent an order on a source graph. -/
namespace Nanuq.PrescribedLoopAmbient
open Set Schoenflies unitInterval

/-- One ambient map realizes EVERY prescribed boundary parameter and subarc. -/
theorem loop_parameters {f g : ℝ → Plane} (hf : IsLoop f) (hg : IsLoop g) :
    ∃ H : Plane ≃ₜ Plane,
      (∀ t ∈ I, H (f t) = g t) ∧
      (∀ T : Set ℝ, T ⊆ I → H '' (f '' T) = g '' T) := by
  obtain ⟨e, he⟩ := hf.exists_homeomorph hg
  obtain ⟨H, hH⟩ := jordan_schoenflies_of_homeomorph
    (show IsJordanCurve (f '' I) from ⟨f, hf, rfl⟩)
    (show IsJordanCurve (g '' I) from ⟨g, hg, rfl⟩) e
  have hp : ∀ t ∈ I, H (f t) = g t := by
    intro t ht
    exact (hH ⟨f t, mem_image_of_mem f ht⟩).trans (he t ht)
  refine ⟨H, hp, ?_⟩
  intro T hT
  ext z
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (hp t (hT ht)).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨f t, mem_image_of_mem f ht, hp t (hT ht)⟩

#print axioms loop_parameters
end Nanuq.PrescribedLoopAmbient
