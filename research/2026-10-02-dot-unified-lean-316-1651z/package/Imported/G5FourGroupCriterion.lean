import G5TwoIntersectionCase

/-!
# The complete six-pair-moment quartet criterion on arbitrary populations

Contributor: dot, 2026-10-02. This is the raw all-position statement behind
Bell(8), with no finite-alphabet enumeration or source-output equality field.
The proof uses actual pair support classifications proved in G5PairMomentCases.
Original source-to-moment probabilities and safe chronology remain separate.
-/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

def absenceCases (p : Fin 4 → Fin 2 → α) : Prop :=
  (pairCount (p 0) (p 1) = 0 ∧ pairCount (p 2) (p 3) = 0) ∨
  (pairCount (p 0) (p 2) = 4 ∨ pairCount (p 0) (p 3) = 4 ∨
   pairCount (p 1) (p 2) = 4 ∨ pairCount (p 1) (p 3) = 4) ∨
  (pairCount (p 0) (p 1) = 1 ∧ pairCount (p 2) (p 3) = 0 ∧
   ((pairCount (p 0) (p 2) = 2 ∧ pairCount (p 1) (p 2) = 2) ∨
    (pairCount (p 0) (p 3) = 2 ∧ pairCount (p 1) (p 3) = 2))) ∨
  (pairCount (p 0) (p 1) = 0 ∧ pairCount (p 2) (p 3) = 1 ∧
   ((pairCount (p 0) (p 2) = 2 ∧ pairCount (p 0) (p 3) = 2) ∨
    (pairCount (p 1) (p 2) = 2 ∧ pairCount (p 1) (p 3) = 2))) ∨
  (((pairCount (p 0) (p 1) = 0 ∧ pairCount (p 2) (p 3) = 2) ∨
    (pairCount (p 0) (p 1) = 2 ∧ pairCount (p 2) (p 3) = 0)) ∧
   pairCount (p 0) (p 2) = 2 ∧ pairCount (p 0) (p 3) = 2 ∧
   pairCount (p 1) (p 2) = 2 ∧ pairCount (p 1) (p 3) = 2)

theorem pairCount_comm (p q : Fin 2 → α) : pairCount p q = pairCount q p := by
  unfold pairCount
  simp only [eq_comm]
  omega

theorem pairCount_values (p q : Fin 2 → α) :
    pairCount p q = 0 ∨ pairCount p q = 1 ∨ pairCount p q = 2 ∨ pairCount p q = 4 := by
  unfold pairCount
  split_ifs <;> simp_all <;> grind

theorem support_exchange (p q c d : Fin 2 → α) :
    quartetSupport p q c d ↔ quartetSupport c d p q := or_comm

theorem support_iff_selector (p : Fin 4 → Fin 2 → α) :
    quartetSupport (p 0) (p 1) (p 2) (p 3) ↔ selectorWitness p := by
  rw [selectorWitness_iff_blockWitness]
  simp only [quartetSupport, sideSupport, blockWitness, blockCount_pos_iff,
    blockCount_lt_two_iff, hasPosition, avoidsPosition, exists_or]

theorem cross_four_blocks (p q c d : Fin 2 → α)
    (h : pairCount p c = 4 ∨ pairCount p d = 4 ∨ pairCount q c = 4 ∨ pairCount q d = 4) :
    ¬quartetSupport p q c d := by
  simp only [pairCount_four_iff] at h
  simp only [quartetSupport, sideSupport, hasPosition, avoidsPosition, Fin.exists_fin_two]
  rcases h with h | h | h | h <;> grind (splits := 16)

theorem four_without_cross_has_witness (p q c d : Fin 2 → α)
    (hu : pairCount p q = 4)
    (hpc : pairCount p c ≠ 4) (hpd : pairCount p d ≠ 4) :
    quartetSupport p q c d := by
  by_contra hn
  have hpos : 0 < pairCount p q := by omega
  rcases (pairCount_pos_iff p q).mp hpos with ⟨e,hp,hq⟩
  rw [pairCount_four_iff] at hu
  have hpC : concentratedAt p e := by
    rcases hp with ⟨k,hk⟩
    intro l; fin_cases k <;> fin_cases l <;> grind
  have hside : ¬sideSupport p q c d := fun h => hn (Or.inl h)
  rcases obstruction_of_no_side p q c d e hp hq hside with hc | hd
  · exact hpc (four_of_concentrated p c e hpC hc)
  · exact hpd (four_of_concentrated p d e hpC hd)

theorem zero_side_absence (p q c d : Fin 2 → α) (hv : pairCount c d = 0)
    (hpc : pairCount p c ≠ 4) (hpd : pairCount p d ≠ 4)
    (hqc : pairCount q c ≠ 4) (hqd : pairCount q d ≠ 4) :
    ¬quartetSupport p q c d ↔
      pairCount p q = 0 ∨
      (pairCount p q = 1 ∧ ((pairCount p c = 2 ∧ pairCount q c = 2) ∨
                             (pairCount p d = 2 ∧ pairCount q d = 2))) ∨
      (pairCount p q = 2 ∧ pairCount p c = 2 ∧ pairCount p d = 2 ∧
        pairCount q c = 2 ∧ pairCount q d = 2) := by
  rcases pairCount_values p q with hu | hu | hu | hu
  · have hn : ¬quartetSupport p q c d := by
      rintro (h | h)
      · exact no_side_of_pairCount_zero p q c d hu h
      · exact no_side_of_pairCount_zero c d p q hv h
    simp_all
  · rw [one_zero_no_quartet_iff p q c d hu hv]
    simp [hu]
  · rw [two_zero_no_cross_four_iff p q c d hu hv hpc hpd hqc hqd]
    simp [hu]
  · have hh := four_without_cross_has_witness p q c d hu hpc hpd
    simp_all

theorem selector_absence_iff_six_moments (p : Fin 4 → Fin 2 → α) :
    ¬selectorWitness p ↔ absenceCases p := by
  rw [← support_iff_selector]
  by_cases hc : pairCount (p 0) (p 2) = 4 ∨ pairCount (p 0) (p 3) = 4 ∨
    pairCount (p 1) (p 2) = 4 ∨ pairCount (p 1) (p 3) = 4
  · have hh := cross_four_blocks (p 0) (p 1) (p 2) (p 3) hc
    simp [absenceCases, hc, hh]
  · simp only [not_or] at hc
    have hpc := hc.1
    have hpd := hc.2.1
    have hqc := hc.2.2.1
    have hqd := hc.2.2.2
    by_cases hv : pairCount (p 2) (p 3) = 0
    · rw [zero_side_absence (p 0) (p 1) (p 2) (p 3) hv hpc hpd hqc hqd]
      simp [absenceCases, hv, hpc, hpd, hqc, hqd]
    · by_cases hu : pairCount (p 0) (p 1) = 0
      · rw [support_exchange]
        rw [zero_side_absence (p 2) (p 3) (p 0) (p 1) hu]
        · simp [absenceCases, hu, hv, hpc, hpd, hqc, hqd, pairCount_comm]
          tauto
        all_goals simpa [pairCount_comm] using (by assumption)
      · have hposu : 0 < pairCount (p 0) (p 1) := Nat.pos_of_ne_zero hu
        have hposv : 0 < pairCount (p 2) (p 3) := Nat.pos_of_ne_zero hv
        have hw : quartetSupport (p 0) (p 1) (p 2) (p 3) := by
          by_contra hn
          rcases both_positive_no_quartet_forces_cross_four
            (p 0) (p 1) (p 2) (p 3) hposu hposv hn with h | h | h | h
          · exact hpc h
          · exact hpd h
          · exact hqc h
          · exact hqd h
        simp [absenceCases, hu, hv, hpc, hpd, hqc, hqd, hw]

theorem selectorWitness_iff_of_pairCounts {β : Type*} [DecidableEq β]
    (p : Fin 4 → Fin 2 → α) (q : Fin 4 → Fin 2 → β)
    (h : ∀ i j, pairCount (p i) (p j) = pairCount (q i) (q j)) :
    selectorWitness p ↔ selectorWitness q := by
  apply not_iff_not.mp
  rw [selector_absence_iff_six_moments, selector_absence_iff_six_moments]
  simp only [absenceCases, h]

#print axioms selector_absence_iff_six_moments
#print axioms selectorWitness_iff_of_pairCounts
end GProgram.G5.QuartetKernel
