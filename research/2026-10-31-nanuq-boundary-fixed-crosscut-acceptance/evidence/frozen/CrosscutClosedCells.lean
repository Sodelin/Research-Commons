import ContinuousRegionCrosscut
import ClosedPieceGlue

set_option debug.skipKernelTC false
/-! UNCOMPILED derivation of closed cells from the actual bounded-region
crosscut theorem, not an assumed cell/order certificate. -/
namespace Nanuq.RelativeCrosscut
open Set Schoenflies

 theorem closed_crosscut_cells {C P A₁ A₂ : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hPC : P ∩ C = {p,q})
    (hPI : P \ {p,q} ⊆ inside C) :
    IsJordanCurve (A₁ ∪ P) ∧ IsJordanCurve (A₂ ∪ P) ∧
    ((A₁ ∪ P) ∪ inside (A₁ ∪ P)) ∪ ((A₂ ∪ P) ∪ inside (A₂ ∪ P)) = C ∪ inside C ∧
    ((A₁ ∪ P) ∪ inside (A₁ ∪ P)) ∩ ((A₂ ∪ P) ∪ inside (A₂ ∪ P)) = P ∧
    ((A₁ ∪ P) ∪ inside (A₁ ∪ P)) ∩ (C ∪ outside C) = A₁ ∧
    ((A₂ ∪ P) ∪ inside (A₂ ∪ P)) ∩ (C ∪ outside C) = A₂ := by
  have hmeet₁ : ∀ z ∈ A₁, z ∈ P → z = p ∨ z = q := by
    intro z hzA hzP
    have hz : z ∈ ({p,q} : Set Plane) := hPC ▸ ⟨hzP,hcut.fst_subset hzA⟩
    simpa using hz
  have hmeet₂ : ∀ z ∈ A₂, z ∈ P → z = p ∨ z = q := by
    intro z hzA hzP
    have hz : z ∈ ({p,q} : Set Plane) := hPC ▸ ⟨hzP,hcut.snd_subset hzA⟩
    simpa using hz
  have hc₁ := IsJordanCurve.of_two_arcs hcut.fst hP.reverse hmeet₁
  have hc₂ := IsJordanCurve.of_two_arcs hcut.snd hP.reverse hmeet₂
  obtain ⟨V₁,V₂,hr₁,hr₂,heq,hdis,_,_,_,_,_,hcl₁,hcl₂⟩ :=
    Nanuq.ContinuousRegionCrosscut.continuous_crosscut_region
      hC hcut hP hPC (IsRegionOf.inside C) hPI
  have hV₁ : V₁ ⊆ inside C \ P := fun z hz => heq.symm ▸ (Or.inl hz : z ∈ V₁ ∪ V₂)
  have hV₂ : V₂ ⊆ inside C \ P := fun z hz => heq.symm ▸ (Or.inr hz : z ∈ V₁ ∪ V₂)
  have hb := (jordan_curve_theorem hC).isBounded_inside
  have hv₁ : V₁ = inside (A₁ ∪ P) := by
    rcases hr₁ with h | h
    · exact h
    · exfalso
      apply (jordan_curve_theorem hc₁).not_isBounded_outside
      rw [← h]
      exact hb.subset (fun z hz => (hV₁ hz).1)
  have hv₂ : V₂ = inside (A₂ ∪ P) := by
    rcases hr₂ with h | h
    · exact h
    · exfalso
      apply (jordan_curve_theorem hc₂).not_isBounded_outside
      rw [← h]
      exact hb.subset (fun z hz => (hV₂ hz).1)
  subst V₁; subst V₂
  have hPsub : P ⊆ C ∪ inside C := by
    intro z hz
    by_cases hpq : z ∈ ({p,q} : Set Plane)
    · exact Or.inl ((hPC.symm ▸ hpq : z ∈ P ∩ C).2)
    · exact Or.inr (hPI ⟨hz,hpq⟩)
  have hD₁sub : (A₁ ∪ P) ∪ inside (A₁ ∪ P) ⊆ C ∪ inside C := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl (hcut.fst_subset hz)
    · exact hPsub hz
    · exact Or.inr (hV₁ hz).1
  have hD₂sub : (A₂ ∪ P) ∪ inside (A₂ ∪ P) ⊆ C ∪ inside C := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl (hcut.snd_subset hz)
    · exact hPsub hz
    · exact Or.inr (hV₂ hz).1
  have hcover : ((A₁ ∪ P) ∪ inside (A₁ ∪ P)) ∪
      ((A₂ ∪ P) ∪ inside (A₂ ∪ P)) = C ∪ inside C := by
    apply Subset.antisymm (union_subset hD₁sub hD₂sub)
    rintro z (hz | hz)
    · have hz' : z ∈ A₁ ∪ A₂ := hcut.union_eq.symm ▸ hz
      rcases hz' with hz' | hz'
      · exact Or.inl (Or.inl (Or.inl hz'))
      · exact Or.inr (Or.inl (Or.inl hz'))
    · by_cases hzP : z ∈ P
      · exact Or.inl (Or.inl (Or.inr hzP))
      · have hz' : z ∈ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := heq ▸ ⟨hz,hzP⟩
        exact hz'.imp Or.inr Or.inr
  have hinter : ((A₁ ∪ P) ∪ inside (A₁ ∪ P)) ∩
      ((A₂ ∪ P) ∪ inside (A₂ ∪ P)) = P := by
    apply Subset.antisymm
    · rintro z ⟨(hzA | hzP) | hzI, (hzB | hzP') | hzJ⟩
      · have hz : z ∈ ({p,q} : Set Plane) := hcut.inter_eq ▸ ⟨hzA,hzB⟩
        exact (hPC.symm ▸ hz : z ∈ P ∩ C).1
      · exact hzP'
      · exact False.elim (inside_subset_compl (hV₂ hzJ).1 (hcut.fst_subset hzA))
      · exact hzP
      · exact hzP
      · exact hzP
      · exact False.elim (inside_subset_compl (hV₁ hzI).1 (hcut.snd_subset hzB))
      · exact False.elim ((hV₁ hzI).2 hzP')
      · exact False.elim (Set.disjoint_left.mp hdis hzI hzJ)
    · intro z hz; exact ⟨Or.inl (Or.inr hz),Or.inl (Or.inr hz)⟩
  have hclosure₁ : closure (inside (A₁ ∪ P)) = (A₁ ∪ P) ∪ inside (A₁ ∪ P) := by
    rw [(IsRegionOf.inside (A₁ ∪ P)).closure_eq (jordan_curve_theorem hc₁), union_comm]
  have hclosure₂ : closure (inside (A₂ ∪ P)) = (A₂ ∪ P) ∪ inside (A₂ ∪ P) := by
    rw [(IsRegionOf.inside (A₂ ∪ P)).closure_eq (jordan_curve_theorem hc₂), union_comm]
  rw [hclosure₁] at hcl₁
  rw [hclosure₂] at hcl₂
  have hout : Disjoint (C ∪ inside C) (outside C) :=
    disjoint_union_left.mpr ⟨disjoint_curve_outside C, disjoint_inside_outside⟩
  have hE₁ : ((A₁ ∪ P) ∪ inside (A₁ ∪ P)) ∩ (C ∪ outside C) = A₁ := by
    rw [inter_union, hcl₁, (hout.mono_left hD₁sub).inter_eq, union_empty]
  have hE₂ : ((A₂ ∪ P) ∪ inside (A₂ ∪ P)) ∩ (C ∪ outside C) = A₂ := by
    rw [inter_union, hcl₂, (hout.mono_left hD₂sub).inter_eq, union_empty]
  exact ⟨hc₁,hc₂,hcover,hinter,hE₁,hE₂⟩

#print axioms closed_crosscut_cells
end Nanuq.RelativeCrosscut
