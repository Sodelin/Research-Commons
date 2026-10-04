import G5FourGroupSupportCases

/-! The genuine one-common-population case in the six-moment Q criterion. -/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

theorem two_of_split_and_concentrated (p c : Fin 2 → α) (e : α)
    (hp : p 0 ≠ p 1) (hc : concentratedAt c e) (he : hasPosition p e) :
    pairCount p c = 2 := by
  rw [pairCount_two_iff]
  refine Or.inr (Or.inl ⟨(hc 0).trans (hc 1).symm, hp, ?_⟩)
  rcases he with ⟨k, hk⟩
  fin_cases k
  · exact Or.inl ((hc 0).trans hk.symm)
  · exact Or.inr ((hc 0).trans hk.symm)

theorem unique_shared_of_count_one (p q : Fin 2 → α)
    (h : pairCount p q = 1) (e f : α)
    (hpe : hasPosition p e) (hqe : hasPosition q e)
    (hpf : hasPosition p f) (hqf : hasPosition q f) : e = f := by
  rw [pairCount_one_iff] at h
  simp only [hasPosition, Fin.exists_fin_two] at hpe hqe hpf hqf
  unfold sameTwoPositions at h
  grind (splits := 16)

theorem double_two_against_one_forces_concentration (p q c : Fin 2 → α)
    (hu : pairCount p q = 1) (hpc : pairCount p c = 2) (hqc : pairCount q c = 2) :
    ∃ e, concentratedAt c e ∧ hasPosition p e ∧ hasPosition q e := by
  have hpq := pairCount_one_split p q hu
  rw [pairCount_two_iff] at hpc hqc
  by_cases hc : c 0 = c 1
  · refine ⟨c 0, ?_, ?_, ?_⟩
    · intro k; fin_cases k
      · rfl
      · exact hc.symm
    · simp only [hasPosition, Fin.exists_fin_two]
      grind
    · simp only [hasPosition, Fin.exists_fin_two]
      grind
  · rw [pairCount_one_iff] at hu
    unfold sameTwoPositions at hu hpc hqc
    grind (splits := 16)

theorem no_side_of_pairCount_zero (p q c d : Fin 2 → α)
    (h : pairCount p q = 0) : ¬sideSupport p q c d := by
  rintro ⟨e, hp, hq, _, _⟩
  have hh := (pairCount_pos_iff p q).mpr ⟨e, hp, hq⟩
  omega

theorem one_zero_no_quartet_iff (p q c d : Fin 2 → α)
    (hu : pairCount p q = 1) (hv : pairCount c d = 0) :
    ¬quartetSupport p q c d ↔
      (pairCount p c = 2 ∧ pairCount q c = 2) ∨
      (pairCount p d = 2 ∧ pairCount q d = 2) := by
  constructor
  · intro hn
    have hpq := pairCount_one_split p q hu
    have hpos : 0 < pairCount p q := by omega
    rcases (pairCount_pos_iff p q).mp hpos with ⟨e, hp, hq⟩
    have hside : ¬sideSupport p q c d := fun hh => hn (Or.inl hh)
    rcases obstruction_of_no_side p q c d e hp hq hside with hc | hd
    · exact Or.inl ⟨two_of_split_and_concentrated p c e hpq.1 hc hp,
        two_of_split_and_concentrated q c e hpq.2 hc hq⟩
    · exact Or.inr ⟨two_of_split_and_concentrated p d e hpq.1 hd hp,
        two_of_split_and_concentrated q d e hpq.2 hd hq⟩
  · intro hh
    have hcd : ¬sideSupport c d p q := no_side_of_pairCount_zero c d p q hv
    rcases hh with ⟨hpc,hqc⟩ | ⟨hpd,hqd⟩
    · rcases double_two_against_one_forces_concentration p q c hu hpc hqc with ⟨e,hc,hp,hq⟩
      rintro (⟨f,hpf,hqf,⟨k,hk⟩,_⟩ | hother)
      · have hef := unique_shared_of_count_one p q hu e f hp hq hpf hqf
        exact hk ((hc k).trans hef)
      · exact hcd hother
    · rcases double_two_against_one_forces_concentration p q d hu hpd hqd with ⟨e,hd,hp,hq⟩
      rintro (⟨f,hpf,hqf,_,⟨k,hk⟩⟩ | hother)
      · have hef := unique_shared_of_count_one p q hu e f hp hq hpf hqf
        exact hk ((hd k).trans hef)
      · exact hcd hother

#print axioms unique_shared_of_count_one
#print axioms double_two_against_one_forces_concentration
#print axioms one_zero_no_quartet_iff
end GProgram.G5.QuartetKernel
