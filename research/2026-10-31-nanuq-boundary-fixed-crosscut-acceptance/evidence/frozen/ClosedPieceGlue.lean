import Schoenflies.JordanSchoenflies

set_option debug.skipKernelTC false
/-! UNCOMPILED source helper for the actual relative crosscut construction.
Both forward AND inverse overlap agreement are proved obligations, not omitted. -/
namespace Nanuq.RelativeCrosscut
open Set Schoenflies

 theorem paste_eq_second {S₁ S₂ : Set Plane} {f₁ f₂ : Plane → Plane}
    (h : EqOn f₁ f₂ (S₁ ∩ S₂)) : EqOn (paste S₁ f₁ f₂) f₂ S₂ := by
  intro x hx
  by_cases hx₁ : x ∈ S₁
  · rw [paste_of_mem hx₁]
    exact h ⟨hx₁,hx⟩
  · exact paste_of_notMem hx₁

/-- Two closed restricted homeomorphisms glue when both directions agree on overlaps.
No disjointness, polygonality or implicit matching of regions is assumed. -/
theorem glue_two_closed
    {S₁ S₂ T₁ T₂ : Set Plane} {f₁ g₁ f₂ g₂ : Plane → Plane}
    (hs₁ : IsClosed S₁) (hs₂ : IsClosed S₂)
    (ht₁ : IsClosed T₁) (ht₂ : IsClosed T₂)
    (h₁ : IsHomeoOn f₁ g₁ S₁ T₁) (h₂ : IsHomeoOn f₂ g₂ S₂ T₂)
    (hf : EqOn f₁ f₂ (S₁ ∩ S₂)) (hg : EqOn g₁ g₂ (T₁ ∩ T₂)) :
    IsHomeoOn (paste S₁ f₁ f₂) (paste T₁ g₁ g₂) (S₁ ∪ S₂) (T₁ ∪ T₂) := by
  have hF₁ : EqOn (paste S₁ f₁ f₂) f₁ S₁ := fun _ hx => paste_of_mem hx
  have hF₂ := paste_eq_second hf
  have hG₁ : EqOn (paste T₁ g₁ g₂) g₁ T₁ := fun _ hx => paste_of_mem hx
  have hG₂ := paste_eq_second hg
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [hF₁ hx]; exact Or.inl (h₁.mapsTo hx)
    · rw [hF₂ hx]; exact Or.inr (h₂.mapsTo hx)
  · intro x hx
    rcases hx with hx | hx
    · rw [hG₁ hx]; exact Or.inl (h₁.mapsTo_inv hx)
    · rw [hG₂ hx]; exact Or.inr (h₂.mapsTo_inv hx)
  · exact Plane.continuousOn_union_of_isClosed hs₁ hs₂
      (h₁.continuousOn.congr hF₁) (h₂.continuousOn.congr hF₂)
  · exact Plane.continuousOn_union_of_isClosed ht₁ ht₂
      (h₁.continuousOn_inv.congr hG₁) (h₂.continuousOn_inv.congr hG₂)
  · intro x hx
    rcases hx with hx | hx
    · rw [hF₁ hx,hG₁ (h₁.mapsTo hx),h₁.invOn.1 hx]
    · rw [hF₂ hx,hG₂ (h₂.mapsTo hx),h₂.invOn.1 hx]
  · intro x hx
    rcases hx with hx | hx
    · rw [hG₁ hx,hF₁ (h₁.mapsTo_inv hx),h₁.invOn.2 hx]
    · rw [hG₂ hx,hF₂ (h₂.mapsTo_inv hx),h₂.invOn.2 hx]

#print axioms glue_two_closed
end Nanuq.RelativeCrosscut
