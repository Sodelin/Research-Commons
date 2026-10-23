import G5PairMomentCases

/-! Source-independent support lemmas for the complete four-group criterion.
Proofs use actual possible binary route positions, never an output equality. -/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

def hasPosition (p : Fin 2 → α) (e : α) : Prop := ∃ k, p k = e

def avoidsPosition (p : Fin 2 → α) (e : α) : Prop := ∃ k, p k ≠ e

def concentratedAt (p : Fin 2 → α) (e : α) : Prop := ∀ k, p k = e

def sideSupport (p q c d : Fin 2 → α) : Prop :=
  ∃ e, hasPosition p e ∧ hasPosition q e ∧ avoidsPosition c e ∧ avoidsPosition d e

def quartetSupport (p q c d : Fin 2 → α) : Prop :=
  sideSupport p q c d ∨ sideSupport c d p q

theorem not_concentrated_iff_avoids (p : Fin 2 → α) (e : α) :
    ¬concentratedAt p e ↔ avoidsPosition p e := by
  simp only [concentratedAt, avoidsPosition, not_forall]

theorem pairCount_pos_iff (p q : Fin 2 → α) :
    0 < pairCount p q ↔ ∃ e, hasPosition p e ∧ hasPosition q e := by
  simp only [pairCount, hasPosition, Fin.exists_fin_two]
  split_ifs <;> simp_all <;> grind

theorem four_of_concentrated (p q : Fin 2 → α) (e : α)
    (hp : concentratedAt p e) (hq : concentratedAt q e) : pairCount p q = 4 := by
  rw [pairCount_four_iff]
  exact ⟨(hp 0).trans (hp 1).symm, (hq 0).trans (hq 1).symm,
    (hp 0).trans (hq 0).symm⟩

theorem obstruction_of_no_side (p q c d : Fin 2 → α) (e : α)
    (hp : hasPosition p e) (hq : hasPosition q e) (hn : ¬sideSupport p q c d) :
    concentratedAt c e ∨ concentratedAt d e := by
  classical
  by_contra! h
  exact hn ⟨e, hp, hq, (not_concentrated_iff_avoids c e).mp h.1,
    (not_concentrated_iff_avoids d e).mp h.2⟩

theorem sideBlocked_of_common_concentration (p q c d : Fin 2 → α) (e : α)
    (hp : concentratedAt p e) (hc : concentratedAt c e) : ¬quartetSupport p q c d := by
  rintro (⟨f, ⟨k, hk⟩, _, ⟨l, hl⟩, _⟩ | ⟨f, ⟨l, hl⟩, _, ⟨k, hk⟩, _⟩)
  · have hf : f = e := hk.symm.trans (hp k)
    exact hl ((hc l).trans hf.symm)
  · have hf : f = e := hl.symm.trans (hc l)
    exact hk ((hp k).trans hf.symm)

theorem both_positive_no_quartet_forces_cross_four (p q c d : Fin 2 → α)
    (hpq : 0 < pairCount p q) (hcd : 0 < pairCount c d)
    (hn : ¬quartetSupport p q c d) :
    pairCount p c = 4 ∨ pairCount p d = 4 ∨ pairCount q c = 4 ∨ pairCount q d = 4 := by
  rcases (pairCount_pos_iff p q).mp hpq with ⟨e, hp, hq⟩
  have hnA : ¬sideSupport p q c d := fun h => hn (Or.inl h)
  have hnC : ¬sideSupport c d p q := fun h => hn (Or.inr h)
  rcases obstruction_of_no_side p q c d e hp hq hnA with hc | hd
  · rcases (pairCount_pos_iff c d).mp hcd with ⟨f, ⟨kc, hcf⟩, ⟨kd, hdf⟩⟩
    have hfe : f = e := hcf.symm.trans (hc kc)
    have hde : hasPosition d e := ⟨kd, hdf.trans hfe⟩
    rcases obstruction_of_no_side c d p q e ⟨0, hc 0⟩ hde hnC with hpe | hqe
    · exact Or.inl (four_of_concentrated p c e hpe hc)
    · exact Or.inr (Or.inr (Or.inl (four_of_concentrated q c e hqe hc)))
  · rcases (pairCount_pos_iff c d).mp hcd with ⟨f, ⟨kc, hcf⟩, ⟨kd, hdf⟩⟩
    have hfe : f = e := hdf.symm.trans (hd kd)
    have hce : hasPosition c e := ⟨kc, hcf.trans hfe⟩
    rcases obstruction_of_no_side c d p q e hce ⟨0, hd 0⟩ hnC with hpe | hqe
    · exact Or.inr (Or.inl (four_of_concentrated p d e hpe hd))
    · exact Or.inr (Or.inr (Or.inr (four_of_concentrated q d e hqe hd)))

#print axioms pairCount_pos_iff
#print axioms obstruction_of_no_side
#print axioms both_positive_no_quartet_forces_cross_four
end GProgram.G5.QuartetKernel
