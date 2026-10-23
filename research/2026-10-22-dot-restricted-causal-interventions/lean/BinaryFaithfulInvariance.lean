import BinarySelectedProbabilityLaw

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The remaining D6 quantifier join: all augmented conditioning assignments
are reduced to their original-variable restriction, with the indicator
coordinate irrelevant to the cell definition. Faithfulness of the actual
single-indicator law therefore gives exact graphical equivalence for the
selected baseline-versus-replacement conditional-law comparison.
The probabilities compared are the finite cylinder ratios, not assumed
oracle coordinates or unconditional post-selection indicator weights.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : Type v} [Fintype T] [DecidableEq T]

theorem cylinder_mass_condition_congr (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (C : Finset V) («first» second : Assignment V)
    (agree : ∀ v ∈ C, «first» v = second v) :
    cylinderMass D θ C «first» = cylinderMass D θ C second := by
  unfold cylinderMass
  apply Finset.sum_congr rfl
  intro w _
  have matching : Matches C «first» w ↔ Matches C second w := by
    constructor
    · intro h v member
      exact (h v member).trans (agree v member)
    · intro h v member
      exact (h v member).trans (agree v member).symm
  rw [matching]

theorem cell_mass_condition_congr (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (x y : V) (C : Finset V) («first» second : Assignment V)
    (agree : ∀ v ∈ C, «first» v = second v) :
    cellMass D θ x y C «first» = cellMass D θ x y C second := by
  funext a b
  apply cylinder_mass_condition_congr
  intro v member
  by_cases atX : v = x
  · simp only [cellAssignment, if_pos atX]
  · by_cases atY : v = y
    · simp only [cellAssignment, if_neg atX, if_pos atY]
    · have inC : v ∈ C := by
        rcases Finset.mem_insert.mp member with same | member
        · exact (atX same).elim
        · rcases Finset.mem_insert.mp member with same | inC
          · exact (atY same).elim
          · exact inC
      simp only [cellAssignment, if_neg atX, if_neg atY]
      exact agree v inC

theorem lifted_selection_matches (S : Finset V) (c : Assignment (Option V)) :
    Matches (liftedSelection S) (fun _ => true) c ↔
      Matches S (fun _ => true) (fun v => c (some v)) := by
  constructor
  · intro h v member
    exact h (some v) (Finset.mem_image.mpr ⟨v, member, rfl⟩)
  · intro h v member
    obtain ⟨old, inS, same⟩ := Finset.mem_image.mp member
    subst v
    exact h old inS

theorem indicator_ci_quantifier_restriction (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (S C : Finset V) (x : V) :
    SelectedBinaryCI (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t)
      (liftedSelection S) none (some x) (C.image some) ↔
    (∀ c : Assignment V, Matches S (fun _ => true) c →
      BinaryMassIndependent (indicatorCellMass D target t θ x C c)) := by
  constructor
  · intro independent c selected
    exact independent (withIndicator false c)
      ((lifted_selection_matches S (withIndicator false c)).mpr selected)
  · intro independent c selected
    let restriction : Assignment V := fun v => c (some v)
    have selectedRestriction := (lifted_selection_matches S c).mp selected
    have sameCells := cell_mass_condition_congr (AddIndicator D (target t))
      (θ ∘ singleIndicatorCoordinate D target t) none (some x) (C.image some)
      c (withIndicator false restriction) (by
        intro v member
        obtain ⟨old, _, same⟩ := Finset.mem_image.mp member
        subst v
        rfl)
    rw [sameCells]
    exact independent restriction selectedRestriction

def SelectedRegimeInvariant (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (S C : Finset V) (x : V) : Prop :=
  ∀ c : Assignment V, Matches S (fun _ => true) c → ∀ b,
    regimeConditionalMass D target t θ x C c false b =
      regimeConditionalMass D target t θ x C c true b

theorem faithful_selected_invariance_iff (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (positive : ∀ k, 0 < θ k ∧ θ k < 1)
    (S C : Finset V) (contains : S ⊆ C) (x : V) (outside : x ∉ C)
    (faithful : SelectedBinaryFaithful (AddIndicator D (target t))
      (θ ∘ singleIndicatorCoordinate D target t) (liftedSelection S)) :
    SelectedRegimeInvariant D target t θ S C x ↔
      ¬ ActiveConnection (arrowGraph (AddIndicator D (target t)))
        (fun v => v ∈ C.image some) none (some x) := by
  have noneOutside : (none : Option V) ∉ C.image some := by simp
  have someOutside : some x ∉ C.image some := by simpa using outside
  have liftedContains : liftedSelection S ⊆ C.image some := by
    intro v member
    obtain ⟨old, inS, same⟩ := Finset.mem_image.mp member
    exact Finset.mem_image.mpr ⟨old, contains inS, same⟩
  exact (selected_indicator_independent_iff_invariant D target t θ positive x C S contains outside).symm.trans
    ((indicator_ci_quantifier_restriction D target t θ S C x).symm.trans
      (faithful none (some x) (C.image some) (by simp) noneOutside someOutside liftedContains))

end RestrictedCausal.ProbabilitySource.BinaryCPT
