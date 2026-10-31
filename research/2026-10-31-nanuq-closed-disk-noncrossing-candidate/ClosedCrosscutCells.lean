import ContinuousRegionCrosscut

/-! UNCOMPILED source draft. A proper continuous crosscut separates even
boundary-touching connected subsets of the CLOSED Jordan disk. This is not
yet the approximation of an arbitrary original cut carrier. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ClosedDiskNoncrossing
open Set Schoenflies

/-- Exact closed-cell identities. The endpoint set belongs to P, not to a
removed untracked collar. Both labelled boundary arcs are retained. -/
theorem proper_crosscut_closed_cells
    {C P A₁ A₂ : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hPC : P ∩ C = {p,q})
    (hPD : P \ {p,q} ⊆ inside C) :
    ∃ F₁ F₂ : Set Plane, IsClosed F₁ ∧ IsClosed F₂ ∧
      F₁ ∪ F₂ = C ∪ inside C ∧ F₁ ∩ F₂ = P ∧
      F₁ ∩ C = A₁ ∧ F₂ ∩ C = A₂ := by
  obtain ⟨V₁,V₂,hV₁,hV₂,hcover,hdisj,hn₁,hn₂,hne,hcomp₁,hcomp₂,hcl₁,hcl₂⟩ :=
    Nanuq.ContinuousRegionCrosscut.continuous_crosscut_region
      hC hcut hP hPC (Or.inl rfl) hPD
  have hmeet : ∀ A : Set Plane, A ⊆ C → ∀ z ∈ A, z ∈ P → z=p ∨ z=q := by
    intro A hA z hz hzP
    have hh : z ∈ ({p,q}:Set Plane) := hPC ▸ ⟨hzP,hA hz⟩
    simpa using hh
  have hj₁ := jordan_curve_theorem (isJordanCurve_union hcut.fst hP
    (hmeet A₁ hcut.fst_subset))
  have hj₂ := jordan_curve_theorem (isJordanCurve_union hcut.snd hP
    (hmeet A₂ hcut.snd_subset))
  have hf₁ := hV₁.closure_eq hj₁
  have hf₂ := hV₂.closure_eq hj₂
  have hends : ({p,q}:Set Plane) ⊆ P := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hP.left_mem
    · exact hP.right_mem
  have hPdisk : P ⊆ C ∪ inside C := by
    intro z hz
    by_cases he : z ∈ ({p,q}:Set Plane)
    · left
      have he' : z ∈ P ∩ C := hPC.symm ▸ he
      exact he'.2
    · exact Or.inr (hPD ⟨hz,he⟩)
  have hv : ∀ z, (z∈V₁ ∨ z∈V₂) ↔ z∈inside C ∧ z∉P := by
    intro z
    rw [← Set.mem_union,← hcover]
    rfl
  have ha : ∀ z, (z∈A₁ ∨ z∈A₂) ↔ z∈C := by
    intro z
    rw [← Set.mem_union,hcut.union_eq]
  have hab : ∀ z, z∈A₁ → z∈A₂ → z∈P := by
    intro z hz₁ hz₂
    exact hends (hcut.inter_eq ▸ ⟨hz₁,hz₂⟩)
  refine ⟨closure V₁,closure V₂,isClosed_closure,isClosed_closure,?_,?_,hcl₁,hcl₂⟩
  · rw [hf₁,hf₂]
    ext z
    have hvz := hv z
    have haz := ha z
    have hpz := @hPdisk z
    simp only [Set.mem_union]
    aesop
  · rw [hf₁,hf₂]
    ext z
    have hvz := hv z
    have haz := ha z
    have habz := hab z
    have hd : ¬(z∈V₁ ∧ z∈V₂) := fun h => Set.disjoint_left.mp hdisj h.1 h.2
    have hi : z∈inside C → z∉C := fun h => h.1
    simp only [Set.mem_inter_iff,Set.mem_union]
    aesop

/-- A connected subset of the CLOSED disk cannot meet the two opposite
boundary arcs while avoiding the ENTIRE proper crosscut, endpoints included.
No strict-interior premise on Q, path parametrization, or second approximation. -/
theorem proper_crosscut_blocks_connected
    {C P Q A₁ A₂ : Set Plane} {p q r s : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hPC : P ∩ C = {p,q})
    (hPD : P \ {p,q} ⊆ inside C)
    (hQ : IsPreconnected Q) (hQdisk : Q ⊆ C ∪ inside C)
    (hdisj : Disjoint Q P) (hrQ : r∈Q) (hsQ : s∈Q)
    (hr : r∈A₁) (hs : s∈A₂) : False := by
  obtain ⟨F₁,F₂,hclosed₁,hclosed₂,hunion,hinter,hboundary₁,hboundary₂⟩ :=
    proper_crosscut_closed_cells hC hcut hP hPC hPD
  have hrF : r∈F₁ := (hboundary₁.symm ▸ hr : r∈F₁∩C).1
  have hsF : s∈F₂ := (hboundary₂.symm ▸ hs : s∈F₂∩C).1
  have hsub : Q ⊆ F₁∪F₂ := hunion.symm ▸ hQdisk
  obtain ⟨z,hzQ,hzF⟩ := isPreconnected_closed_iff.mp hQ F₁ F₂
    hclosed₁ hclosed₂ hsub ⟨r,hrQ,hrF⟩ ⟨s,hsQ,hsF⟩
  exact Set.disjoint_left.mp hdisj hzQ (hinter ▸ hzF)

#print axioms proper_crosscut_closed_cells
#print axioms proper_crosscut_blocks_connected
end Nanuq.ClosedDiskNoncrossing
