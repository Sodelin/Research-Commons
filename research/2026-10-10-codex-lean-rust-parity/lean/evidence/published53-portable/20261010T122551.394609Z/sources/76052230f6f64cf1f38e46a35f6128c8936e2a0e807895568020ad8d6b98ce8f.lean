import G5FairMomentQuartetTransport

/-!
# Actual common selector semantics after sure-group contraction

Contributor: dot, 2026-10-02. Original labels in one group use ONE selector.
These theorems prove the exact one/two/three/four-group interfaces directly;
they do not replace repeated original labels by independent samples.
Original graph persistence and observation-driven grouping remain separate.
-/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

def quartetAt (p : Fin 4 → α) : Prop :=
  (p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3) ∨
  (p 2 = p 3 ∧ p 2 ≠ p 0 ∧ p 2 ≠ p 1)

def groupSelected {r : Nat} (pos : Fin r → Fin 2 → α)
    (owner : Fin 4 → Fin r) (choice : Fin r → Fin 2) : Fin 4 → α :=
  fun label => pos (owner label) (choice (owner label))

def coupledQuartetWitness {r : Nat} (pos : Fin r → Fin 2 → α)
    (owner : Fin 4 → Fin r) : Prop :=
  ∃ choice : Fin r → Fin 2, quartetAt (groupSelected pos owner choice)

theorem cross_group_identification_blocks {r : Nat}
    (pos : Fin r → Fin 2 → α) (owner : Fin 4 → Fin r)
    (h : owner 0 = owner 2 ∨ owner 0 = owner 3 ∨
         owner 1 = owner 2 ∨ owner 1 = owner 3) :
    ¬coupledQuartetWitness pos owner := by
  rintro ⟨choice, hw⟩
  simp only [quartetAt, groupSelected] at hw
  rcases h with h | h | h | h <;> rcases hw with hw | hw <;> grind

def ownersTwo : Fin 4 → Fin 2 := ![0,0,1,1]
def ownersThree : Fin 4 → Fin 3 := ![0,0,1,2]

theorem two_coupled_iff_distinct_selectors (pos : Fin 2 → Fin 2 → α) :
    coupledQuartetWitness pos ownersTwo ↔
      ∃ kg kh : Fin 2, pos 0 kg ≠ pos 1 kh := by
  constructor
  · rintro ⟨choice, hw⟩
    have hh :
        (pos 0 (choice 0) = pos 0 (choice 0) ∧
         pos 0 (choice 0) ≠ pos 1 (choice 1) ∧
         pos 0 (choice 0) ≠ pos 1 (choice 1)) ∨
        (pos 1 (choice 1) = pos 1 (choice 1) ∧
         pos 1 (choice 1) ≠ pos 0 (choice 0) ∧
         pos 1 (choice 1) ≠ pos 0 (choice 0)) := by
      simpa [quartetAt, groupSelected, ownersTwo] using hw
    rcases hh with hh | hh
    · exact ⟨choice 0,choice 1,hh.2.1⟩
    · exact ⟨choice 0,choice 1,Ne.symm hh.2.1⟩
  · rintro ⟨kg,kh,h⟩
    refine ⟨![kg,kh],?_⟩
    simpa [quartetAt, groupSelected, ownersTwo] using
      (Or.inl h : pos 0 kg ≠ pos 1 kh ∨ pos 1 kh ≠ pos 0 kg)

theorem distinct_selectors_iff_count_lt_four (p q : Fin 2 → α) :
    (∃ k l : Fin 2, p k ≠ q l) ↔ pairCount p q < 4 := by
  simp only [Fin.exists_fin_two, pairCount]
  split_ifs <;> simp_all <;> grind

theorem two_coupled_iff_count_lt_four (pos : Fin 2 → Fin 2 → α) :
    coupledQuartetWitness pos ownersTwo ↔ pairCount (pos 0) (pos 1) < 4 := by
  rw [two_coupled_iff_distinct_selectors, distinct_selectors_iff_count_lt_four]

theorem three_coupled_iff_threeGroupWitness (pos : Fin 3 → Fin 2 → α) :
    coupledQuartetWitness pos ownersThree ↔
      threeGroupWitness (pos 0) (pos 1) (pos 2) := by
  constructor
  · rintro ⟨choice,hw⟩
    have hh :
        (pos 0 (choice 0) = pos 0 (choice 0) ∧
         pos 0 (choice 0) ≠ pos 1 (choice 1) ∧
         pos 0 (choice 0) ≠ pos 2 (choice 2)) ∨
        (pos 1 (choice 1) = pos 2 (choice 2) ∧
         pos 1 (choice 1) ≠ pos 0 (choice 0) ∧
         pos 1 (choice 1) ≠ pos 0 (choice 0)) := by
      simpa [quartetAt,groupSelected,ownersThree] using hw
    rcases hh with hh | hh
    · exact ⟨choice 0,choice 1,choice 2,hh.2.1,hh.2.2⟩
    · refine ⟨choice 0,choice 1,choice 2,Ne.symm hh.2.1,?_⟩
      rw [←hh.1]
      exact Ne.symm hh.2.1
  · rintro ⟨kg,kh,ki,hgh,hgi⟩
    refine ⟨![kg,kh,ki],?_⟩
    simpa [quartetAt,groupSelected,ownersThree] using Or.inl
      (show pos 0 kg = pos 0 kg ∧ pos 0 kg ≠ pos 1 kh ∧ pos 0 kg ≠ pos 2 ki
       from ⟨rfl,hgh,hgi⟩)

theorem four_coupled_iff_selectorWitness (pos : Fin 4 → Fin 2 → α) :
    coupledQuartetWitness pos id ↔ selectorWitness pos := by
  constructor
  · rintro ⟨choice,hw⟩
    exact ⟨choice 0,choice 1,choice 2,choice 3,hw⟩
  · rintro ⟨ka,kb,kc,kd,hw⟩
    refine ⟨![ka,kb,kc,kd],?_⟩
    simpa [quartetAt,groupSelected] using hw

#print axioms cross_group_identification_blocks
#print axioms two_coupled_iff_count_lt_four
#print axioms three_coupled_iff_threeGroupWitness
#print axioms four_coupled_iff_selectorWitness
end GProgram.G5.QuartetKernel
