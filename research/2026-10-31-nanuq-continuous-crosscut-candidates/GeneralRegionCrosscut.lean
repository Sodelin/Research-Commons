import Schoenflies.JordanClosed

set_option debug.skipKernelTC false
/-! UNCOMPILED own-source composition candidate. This uses the qualified supplier
without changing its declarations. The boundary C may be nonpolygonal; the
crosscut P is genuinely polygonal. Both original inside and outside regions
are covered. The subsequent prescribed-map continuous-source adapter remains
separate, as do bridges, vertex stars, and the actual NANUQ contour/order. -/
namespace Nanuq.GeneralRegionCrosscut
open Set Schoenflies

/-- Two labelled components of an arbitrary complementary region, not just inside C. -/
theorem polygonal_crosscut_region
    {C P A₁ A₂ Ω : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hpoly : IsPolygonal P)
    (hPC : P ∩ C = {p, q}) (hΩ : IsRegionOf C Ω)
    (hPD : P \ {p, q} ⊆ Ω) :
    ∃ V₁ V₂ : Set Plane,
      IsRegionOf (A₁ ∪ P) V₁ ∧ IsRegionOf (A₂ ∪ P) V₂ ∧
      Ω \ P = V₁ ∪ V₂ ∧ Disjoint V₁ V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧
      V₁ ≠ V₂ ∧
      (∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      closure V₁ ∩ C = A₁ ∧ closure V₂ ∩ C = A₂ := by
  have hsep := jordan_curve_theorem hC
  have hpC : p ∈ C := hcut.fst_subset hcut.fst.left_mem
  have hqC : q ∈ C := hcut.fst_subset hcut.fst.right_mem
  have hmeet : ∀ (A : Set Plane), A ⊆ C → ∀ z ∈ A, z ∈ P → z = p ∨ z = q := by
    intro A hAC z hz hzP
    have h : z ∈ ({p, q} : Set Plane) := hPC ▸ ⟨hzP, hAC hz⟩
    simpa using h
  have hJ₁ := jordan_curve_theorem
    (isJordanCurve_union hcut.fst hP (hmeet A₁ hcut.fst_subset))
  have hJ₂ := jordan_curve_theorem
    (isJordanCurve_union hcut.snd hP (hmeet A₂ hcut.snd_subset))
  obtain ⟨Ω', hp⟩ : ∃ Ω', IsRegionPair C Ω Ω' := by
    rcases hΩ with h | h
    · exact ⟨outside C, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨inside C, Or.inr ⟨h, rfl⟩⟩
  have hd : ∀ A : Set Plane, A ⊆ C → Disjoint Ω' (A ∪ P) := by
    intro A hAC
    apply Set.disjoint_left.mpr
    intro z hz hzAP
    have hzC : z ∉ C := hp.right.subset_compl hz
    rcases hzAP with hzA | hzP
    · exact hzC (hAC hzA)
    · have hzp : z ∉ ({p, q} : Set Plane) := by
        rintro (rfl | rfl)
        exacts [hzC hpC, hzC hqC]
      exact Set.disjoint_left.mp hp.disjoint (hPD ⟨hzP, hzp⟩) hz
  obtain ⟨W₁, V₁, hp₁, hsub₁⟩ := hJ₁.exists_isRegionPair_subset
    (hp.right.isConnected hsep).isPreconnected (hp.right.isConnected hsep).nonempty
    (hd A₁ hcut.fst_subset)
  obtain ⟨W₂, V₂, hp₂, hsub₂⟩ := hJ₂.exists_isRegionPair_subset
    (hp.right.isConnected hsep).isPreconnected (hp.right.isConnected hsep).nonempty
    (hd A₂ hcut.snd_subset)
  have hPC₁ : P ∩ C ⊆ A₁ := by
    rw [hPC]
    intro z hz
    rcases hz with rfl | hz
    · exact hcut.fst.left_mem
    · have : z = q := hz
      subst z
      exact hcut.fst.right_mem
  have hPC₂ : P ∩ C ⊆ A₂ := by
    rw [hPC]
    intro z hz
    rcases hz with rfl | hz
    · exact hcut.snd.left_mem
    · have : z = q := hz
      subst z
      exact hcut.snd.right_mem
  obtain ⟨hv₁, hv₂, hne, hcl₁, hcl₂⟩ := crosscut_cells hsep hJ₁ hJ₂
    hcut.fst_subset hcut.snd_subset hPC₁ hPC₂ hcut.ne hp hp₁ hsub₁ hp₂ hsub₂
  have hn₁ := (hp₁.right.isConnected hJ₁).nonempty
  have hn₂ := (hp₂.right.isConnected hJ₂).nonempty
  obtain ⟨v₁, h₁⟩ := hn₁
  obtain ⟨v₂, h₂⟩ := hn₂
  have hcomp : connectedComponentIn (Ω \ P) v₁ ≠ connectedComponentIn (Ω \ P) v₂ := by
    rwa [hv₁.2 v₁ h₁, hv₂.2 v₂ h₂]
  have hex := crosscut_components_exhaust_of_isPolygonal (hp.left.isOpen hsep)
    (hp.left.isConnected hsep).isPreconnected hP hpoly
    (fun h => hp.left.subset_compl h hpC) (fun h => hp.left.subset_compl h hqC)
    hPD (hv₁.1 h₁) (hv₂.1 h₂) hcomp
  have heq : Ω \ P = V₁ ∪ V₂ := by
    apply Set.Subset.antisymm
    · intro z hz
      have hc := hex z hz
      rwa [hv₁.2 v₁ h₁, hv₂.2 v₂ h₂] at hc
    · exact Set.union_subset hv₁.1 hv₂.1
  have hdis : Disjoint V₁ V₂ := Set.disjoint_left.mpr fun z hz₁ hz₂ =>
    hne ((hv₁.2 z hz₁).symm.trans (hv₂.2 z hz₂))
  exact ⟨V₁, V₂, hp₁.right, hp₂.right, heq, hdis, ⟨v₁,h₁⟩, ⟨v₂,h₂⟩,
    hne, hv₁.2, hv₂.2, hcl₁, hcl₂⟩

#print axioms polygonal_crosscut_region
end Nanuq.GeneralRegionCrosscut
