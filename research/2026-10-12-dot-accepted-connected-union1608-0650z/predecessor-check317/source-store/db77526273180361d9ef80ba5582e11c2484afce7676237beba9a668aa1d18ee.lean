import G5OneIntersectionCase
import G5ThreeGroupKernel

/-! Complete same-two-position case, using ONE coupled group selector. -/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

theorem has_iff_of_same_two (p q : Fin 2 → α) (hs : sameTwoPositions p q) (e : α) :
    hasPosition p e ↔ hasPosition q e := by
  simp only [hasPosition, Fin.exists_fin_two]
  unfold sameTwoPositions at hs
  grind

theorem pairCount_eq_of_same_two (p q c : Fin 2 → α) (hs : sameTwoPositions p q) :
    pairCount p c = pairCount q c := by
  unfold sameTwoPositions at hs
  rcases hs with hs | hs
  · simp_all [pairCount]
  · simp_all [pairCount]
    omega

theorem quartetSupport_iff_three_of_same_two (p q c d : Fin 2 → α)
    (hs : sameTwoPositions p q) :
    quartetSupport p q c d ↔ threeGroupWitness p c d := by
  constructor
  · rintro (⟨e,⟨kg,hg⟩,_,⟨kc,hc⟩,⟨kd,hd⟩⟩ | ⟨e,⟨kc,hc⟩,⟨kd,hd⟩,⟨kg,hg⟩,_⟩)
    · exact ⟨kg,kc,kd, by simpa [hg] using Ne.symm hc,
        by simpa [hg] using Ne.symm hd⟩
    · exact ⟨kg,kc,kd, by simpa [hc] using hg, by simpa [hd] using hg⟩
  · rintro ⟨kg,kc,kd,hc,hd⟩
    refine Or.inl ⟨p kg, ⟨kg,rfl⟩, ?_, ⟨kc,Ne.symm hc⟩, ⟨kd,Ne.symm hd⟩⟩
    exact (has_iff_of_same_two p q hs (p kg)).mp ⟨kg,rfl⟩

theorem two_zero_no_cross_four_iff (p q c d : Fin 2 → α)
    (hu : pairCount p q = 2) (hv : pairCount c d = 0)
    (hnpc : pairCount p c ≠ 4) (hnpd : pairCount p d ≠ 4)
    (hnqc : pairCount q c ≠ 4) (hnqd : pairCount q d ≠ 4) :
    ¬quartetSupport p q c d ↔
      pairCount p c = 2 ∧ pairCount p d = 2 ∧
      pairCount q c = 2 ∧ pairCount q d = 2 := by
  by_cases hp : p 0 = p 1
  · have hn : quartetSupport p q c d := by
      by_contra hh
      have hpos : 0 < pairCount p q := by omega
      rcases (pairCount_pos_iff p q).mp hpos with ⟨e,hpe,hqe⟩
      have hpeC : concentratedAt p e := by
        rcases hpe with ⟨k,hk⟩
        intro l; fin_cases k <;> fin_cases l <;> grind
      have hside : ¬sideSupport p q c d := fun h => hh (Or.inl h)
      rcases obstruction_of_no_side p q c d e hpe hqe hside with hc | hd
      · exact hnpc (four_of_concentrated p c e hpeC hc)
      · exact hnpd (four_of_concentrated p d e hpeC hd)
    have hcnot : pairCount p c ≠ 2 ∨ pairCount p d ≠ 2 := by
      by_contra! h
      simp only [pairCount_two_iff] at h
      rcases h with ⟨hc,hd⟩
      rcases hc with hc | hc | hc <;> rcases hd with hd | hd | hd <;>
        simp_all [pairCount_zero_iff] <;> grind (splits := 16)
    constructor
    · intro hh; exact False.elim (hh hn)
    · intro hh
      rcases hcnot with hc | hd
      · exact False.elim (hc hh.1)
      · exact False.elim (hd hh.2.1)
  · by_cases hq : q 0 = q 1
    · have hn : quartetSupport p q c d := by
        by_contra hh
        have hpos : 0 < pairCount p q := by omega
        rcases (pairCount_pos_iff p q).mp hpos with ⟨e,hpe,hqe⟩
        have hqeC : concentratedAt q e := by
          rcases hqe with ⟨k,hk⟩
          intro l; fin_cases k <;> fin_cases l <;> grind
        have hside : ¬sideSupport p q c d := fun h => hh (Or.inl h)
        rcases obstruction_of_no_side p q c d e hpe hqe hside with hc | hd
        · exact hnqc (four_of_concentrated q c e hqeC hc)
        · exact hnqd (four_of_concentrated q d e hqeC hd)
      have hcnot : pairCount q c ≠ 2 ∨ pairCount q d ≠ 2 := by
        by_contra! h
        simp only [pairCount_two_iff] at h
        rcases h with ⟨hc,hd⟩
        rcases hc with hc | hc | hc <;> rcases hd with hd | hd | hd <;>
          simp_all [pairCount_zero_iff] <;> grind (splits := 16)
      constructor
      · intro hh; exact False.elim (hh hn)
      · intro hh
        rcases hcnot with hc | hd
        · exact False.elim (hc hh.2.2.1)
        · exact False.elim (hd hh.2.2.2)
    · have hs : sameTwoPositions p q := by
        rw [pairCount_two_iff] at hu
        simp_all
      rw [quartetSupport_iff_three_of_same_two p q c d hs, threeGroup_absence_iff]
      rw [← pairCount_eq_of_same_two p q c hs, ← pairCount_eq_of_same_two p q d hs]
      simp_all

#print axioms quartetSupport_iff_three_of_same_two
#print axioms two_zero_no_cross_four_iff
end GProgram.G5.QuartetKernel
