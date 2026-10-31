import BinarySelectedProbabilityLaw

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Observable interpretation of the selected-law query contract. Adding the
fixed selection coordinates to a conditioning set changes no selected-law
CI. The regime conditional ratios are also proved to be ratios in the
actual normalized selected law. No latent variable is conditioned on by
the original observed query adapter; all are summed out in lawCylinder.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open SelectedWalk

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : Type v} [Fintype T] [DecidableEq T]

theorem law_cylinder_condition_congr (law : FiniteBinaryLaw V) (B : Finset V)
    («first» second : Assignment V) (agree : ∀ v ∈ B, «first» v = second v) :
    lawCylinder law B «first» = lawCylinder law B second := by
  unfold lawCylinder
  apply Finset.sum_congr rfl
  intro w _
  have matching : Matches B «first» w ↔ Matches B second w := by
    constructor
    · intro h v member; exact (h v member).trans (agree v member)
    · intro h v member; exact (h v member).trans (agree v member).symm
  exact ite_cond_congr (propext matching)

theorem selected_cylinder_remove_selection (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) (S B : Finset V) (c : Assignment V)
    (selected : Matches S (fun _ => true) c) :
    lawCylinder (selectedBinaryLaw D acyclic θ positive S) B c =
      lawCylinder (selectedBinaryLaw D acyclic θ positive S) (B \ S) c := by
  classical
  unfold lawCylinder
  apply Finset.sum_congr rfl
  intro w _
  by_cases event : Matches S (fun _ => true) w
  · have matching : Matches B c w ↔ Matches (B \ S) c w := by
      constructor
      · intro h v member; exact h v (Finset.mem_sdiff.mp member).1
      · intro h v inB
        by_cases inS : v ∈ S
        · exact (event v inS).trans (selected v inS).symm
        · exact h v (Finset.mem_sdiff.mpr ⟨inB, inS⟩)
    exact ite_cond_congr (propext matching)
  · have zero : (selectedBinaryLaw D acyclic θ positive S).mass w = 0 := by
      simp only [selectedBinaryLaw, if_neg event]
    rw [zero]
    simp only [ite_self]

theorem selected_cell_remove_selection (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) (S C : Finset V) (contains : S ⊆ C)
    (x y : V) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (c : Assignment V) (selected : Matches S (fun _ => true) c) :
    lawCell (selectedBinaryLaw D acyclic θ positive S) x y C c =
      lawCell (selectedBinaryLaw D acyclic θ positive S) x y (C \ S) c := by
  have xNotS : x ∉ S := fun member => xOutside (contains member)
  have yNotS : y ∉ S := fun member => yOutside (contains member)
  have conditions : insert x (insert y C) \ S = insert x (insert y (C \ S)) := by
    ext v
    by_cases atX : v = x
    · subst v; simp [xNotS]
    · by_cases atY : v = y
      · subst v; simp [yNotS]
      · simp only [Finset.mem_sdiff, Finset.mem_insert, atX, atY, false_or]
  funext a b
  unfold lawCell
  rw [selected_cylinder_remove_selection D acyclic θ positive S _ _
    ((selected_cell_assignment_iff S C contains x y xOutside yOutside c a b).mpr selected), conditions]

/-- Conditioning on constant selected flags is redundant. Thus the
baseline query in the physical adapter is an observed-only selected CI,
not an extra experiment revealing hidden selection values. -/
theorem selected_law_ci_remove_selection (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) (S C : Finset V) (contains : S ⊆ C)
    (x y : V) (xOutside : x ∉ C) (yOutside : y ∉ C) :
    LawConditionalIndependent (selectedBinaryLaw D acyclic θ positive S) x y C ↔
      LawConditionalIndependent (selectedBinaryLaw D acyclic θ positive S) x y (C \ S) := by
  constructor
  · intro independent c
    let chosen := clampCondition S (fun _ => true) c
    have selected : Matches S (fun _ => true) chosen := by
      intro s member; simp only [chosen, clampCondition, if_pos member]
    have actual := independent chosen
    rw [selected_cell_remove_selection D acyclic θ positive S C contains x y xOutside yOutside
      chosen selected] at actual
    have sameCells : lawCell (selectedBinaryLaw D acyclic θ positive S) x y (C \ S) chosen =
        lawCell (selectedBinaryLaw D acyclic θ positive S) x y (C \ S) c := by
      funext a b
      apply law_cylinder_condition_congr
      intro vertex member
      by_cases atX : vertex = x
      · simp only [cellAssignment, if_pos atX]
      · by_cases atY : vertex = y
        · simp only [cellAssignment, if_neg atX, if_pos atY]
        · have retained : vertex ∈ C \ S := by
            simpa only [Finset.mem_insert, atX, atY, false_or] using member
          have outside := (Finset.mem_sdiff.mp retained).2
          simp only [cellAssignment, if_neg atX, if_neg atY, chosen, clampCondition, if_neg outside]
    rw [sameCells] at actual
    exact actual
  · intro independent c
    by_cases selected : Matches S (fun _ => true) c
    · rw [selected_cell_remove_selection D acyclic θ positive S C contains x y xOutside yOutside c selected]
      exact independent c
    · have allZero : lawCell (selectedBinaryLaw D acyclic θ positive S) x y C c = fun _ _ => 0 := by
        funext a b
        exact incompatible_selected_law_cylinder D acyclic θ positive S _
          (fun s member => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (contains member))) _
          (fun h => selected ((selected_cell_assignment_iff S C contains x y xOutside yOutside c a b).mp h))
      rw [allZero]
      intro a b
      simp only [mul_zero, zero_mul, add_zero]

theorem regime_conditional_is_selected_law_ratio (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (positive : ∀ k, 0 < θ k ∧ θ k < 1)
    (S C : Finset V) (contains : S ⊆ C) (x : V) (outside : x ∉ C)
    (c : Assignment V) (selected : Matches S (fun _ => true) c) (i b : Bool) :
    regimeConditionalMass D target t θ x C c i b =
      lawCylinder (selectedBinaryLaw D acyclic (θ ∘ regimeCoordinate D target t i)
          (fun k => positive _) S) (insert x C) (pointAssignment x c b) /
        lawCylinder (selectedBinaryLaw D acyclic (θ ∘ regimeCoordinate D target t i)
          (fun k => positive _) S) C c := by
  have selectedPoint : Matches S (fun _ => true) (pointAssignment x c b) := by
    intro s member
    have different : s ≠ x := by intro same; subst s; exact outside (contains member)
    simp only [pointAssignment, if_neg different]
    exact selected s member
  rw [selected_law_cylinder D acyclic (θ ∘ regimeCoordinate D target t i) (fun k => positive _) S (insert x C)
      (fun s member => Finset.mem_insert_of_mem (contains member)) _ selectedPoint,
    selected_law_cylinder D acyclic (θ ∘ regimeCoordinate D target t i) (fun k => positive _) S C contains c selected]
  let z := cylinderMass D (θ ∘ regimeCoordinate D target t i) S (fun _ => true)
  have nonzero : z ≠ 0 := ne_of_gt (cylinder_mass_pos D _ (fun k => positive _) S (fun _ => true))
  let numerator := cylinderMass D (θ ∘ regimeCoordinate D target t i) (insert x C) (pointAssignment x c b)
  let denominator := cylinderMass D (θ ∘ regimeCoordinate D target t i) C c
  change numerator / denominator = (numerator / z) / (denominator / z)
  have scaled : (numerator / z) / (denominator / z) = (z⁻¹ * numerator) / (z⁻¹ * denominator) := by
    congr 1 <;> rw [div_eq_mul_inv, mul_comm]
  rw [scaled]
  exact (mul_div_mul_left numerator denominator (inv_ne_zero nonzero)).symm

end RestrictedCausal.ProbabilitySource.BinaryCPT
