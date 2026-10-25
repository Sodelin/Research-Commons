import BinaryCommonFaithfulSource
import Mathlib.Algebra.BigOperators.Field

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Finite rational probability laws and their actual conditioning on S=1.
The law has nonnegative masses and total mass one, with positive original
CPT products and positive selection probability derived in the bodies.
Selected conditional independence uses its actual cell marginal sums,
including zero-mass incompatible selection slices. It is proved equivalent
to the previous unnormalized original-cell formulation, not identified
with it by a new oracle definition.

Pinned API: Mathlib/Algebra/BigOperators/Field.lean at
0df444a360eaa60ab8c11dca51a86af692955474, blob
f9f0df582b7ef695526ee9c0d6909e01013c02aa (Finset.sum_div).
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

structure FiniteBinaryLaw (V : Type u) [Fintype V] where
  mass : Assignment V → ℚ
  nonnegative : ∀ w, 0 ≤ mass w
  normalized : (∑ w, mass w) = 1

noncomputable def originalBinaryLaw (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) : FiniteBinaryLaw V where
  mass := jointMass D θ
  nonnegative w := (joint_mass_pos D θ positive w).le
  normalized := binary_dag_product_normalized D acyclic θ

noncomputable def selectedBinaryLaw (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) (S : Finset V) : FiniteBinaryLaw V where
  mass w := if Matches S (fun _ => true) w then
    jointMass D θ w / cylinderMass D θ S (fun _ => true) else 0
  nonnegative w := by
    split_ifs
    · exact (div_pos (joint_mass_pos D θ positive w)
        (cylinder_mass_pos D θ positive S (fun _ => true))).le
    · exact le_refl _
  normalized := by
    classical
    have scaled : (∑ w : Assignment V, if Matches S (fun _ => true) w then
        jointMass D θ w / cylinderMass D θ S (fun _ => true) else 0) =
        cylinderMass D θ S (fun _ => true) / cylinderMass D θ S (fun _ => true) := by
      unfold cylinderMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      by_cases matching : Matches S (fun _ => true) w <;> simp only [matching, if_pos, if_neg, zero_div]
    exact scaled.trans (div_self (ne_of_gt (cylinder_mass_pos D θ positive S (fun _ => true))))

def lawCylinder (law : FiniteBinaryLaw V) (B : Finset V) (c : Assignment V) : ℚ :=
  ∑ w : Assignment V, if Matches B c w then law.mass w else 0

def lawCell (law : FiniteBinaryLaw V) (x y : V) (C : Finset V) (c : Assignment V) : Bool → Bool → ℚ :=
  fun a b => lawCylinder law (insert x (insert y C)) (cellAssignment x y c a b)

def LawConditionalIndependent (law : FiniteBinaryLaw V) (x y : V) (C : Finset V) : Prop :=
  ∀ c : Assignment V, BinaryMassIndependent (lawCell law x y C c)

theorem selected_law_cylinder (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) (S B : Finset V) (contains : S ⊆ B)
    (c : Assignment V) (selected : Matches S (fun _ => true) c) :
    lawCylinder (selectedBinaryLaw D acyclic θ positive S) B c =
      cylinderMass D θ B c / cylinderMass D θ S (fun _ => true) := by
  classical
  unfold lawCylinder cylinderMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  by_cases matching : Matches B c w
  · have event : Matches S (fun _ => true) w :=
      fun s member => (matching s (contains member)).trans (selected s member)
    simp only [if_pos matching, selectedBinaryLaw, if_pos event]
  · simp only [if_neg matching, zero_div]

theorem incompatible_selected_law_cylinder (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) (S B : Finset V) (contains : S ⊆ B)
    (c : Assignment V) (incompatible : ¬ Matches S (fun _ => true) c) :
    lawCylinder (selectedBinaryLaw D acyclic θ positive S) B c = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro w _
  by_cases matching : Matches B c w
  · have outsideEvent : ¬ Matches S (fun _ => true) w := by
      intro selected
      exact incompatible (fun s member => (matching s (contains member)).symm.trans (selected s member))
    simp only [if_pos matching, selectedBinaryLaw, if_neg outsideEvent]
  · simp only [if_neg matching]

theorem cell_assignment_condition_agreement (x y : V) (C : Finset V) (c : Assignment V)
    (a b : Bool) (xOutside : x ∉ C) (yOutside : y ∉ C) :
    Matches C c (cellAssignment x y c a b) := by
  intro v member
  have notX : v ≠ x := by intro same; subst v; exact xOutside member
  have notY : v ≠ y := by intro same; subst v; exact yOutside member
  simp only [cellAssignment, if_neg notX, if_neg notY]

theorem selected_cell_assignment_iff (S C : Finset V) (contains : S ⊆ C) (x y : V)
    (xOutside : x ∉ C) (yOutside : y ∉ C) (c : Assignment V) (a b : Bool) :
    Matches S (fun _ => true) (cellAssignment x y c a b) ↔ Matches S (fun _ => true) c := by
  have agreement := cell_assignment_condition_agreement x y C c a b xOutside yOutside
  constructor
  · intro selected s member
    exact (agreement s (contains member)).symm.trans (selected s member)
  · intro selected s member
    exact (agreement s (contains member)).trans (selected s member)

theorem binary_determinant_scaled (mass : Bool → Bool → ℚ) (k : ℚ) :
    binaryDeterminant (fun a b => k * mass a b) = k * k * binaryDeterminant mass := by
  unfold binaryDeterminant
  ring

theorem binary_independence_scaled_iff (mass : Bool → Bool → ℚ) (k : ℚ) (nonzero : k ≠ 0) :
    BinaryMassIndependent (fun a b => k * mass a b) ↔ BinaryMassIndependent mass := by
  rw [binary_independent_iff_determinant, binary_independent_iff_determinant,
    binary_determinant_scaled]
  simp only [mul_eq_zero, nonzero, false_or]

/-- CI in the actual normalized selected law, with every conditioning
assignment quantified, is precisely the original-mass selected-slice CI. -/
theorem selected_law_ci_iff (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (positive : ∀ k, 0 < θ k ∧ θ k < 1) (S C : Finset V) (contains : S ⊆ C)
    (x y : V) (xOutside : x ∉ C) (yOutside : y ∉ C) :
    LawConditionalIndependent (selectedBinaryLaw D acyclic θ positive S) x y C ↔
      SelectedBinaryCI D θ S x y C := by
  have contained : S ⊆ insert x (insert y C) :=
    fun s member => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (contains member))
  have normalizer : cylinderMass D θ S (fun _ => true) ≠ 0 :=
    ne_of_gt (cylinder_mass_pos D θ positive S (fun _ => true))
  have selectedCells : ∀ c, Matches S (fun _ => true) c →
      lawCell (selectedBinaryLaw D acyclic θ positive S) x y C c =
        fun a b => (cylinderMass D θ S (fun _ => true))⁻¹ * cellMass D θ x y C c a b := by
    intro c selected
    funext a b
    unfold lawCell
    rw [selected_law_cylinder D acyclic θ positive S _ contained _
      ((selected_cell_assignment_iff S C contains x y xOutside yOutside c a b).mpr selected)]
    change cellMass D θ x y C c a b / _ = _
    rw [div_eq_mul_inv, mul_comm]
  constructor
  · intro independent c selected
    have atSlice := independent c
    rw [selectedCells c selected] at atSlice
    exact (binary_independence_scaled_iff _ _ (inv_ne_zero normalizer)).mp atSlice
  · intro independent c
    by_cases selected : Matches S (fun _ => true) c
    · rw [selectedCells c selected]
      exact (binary_independence_scaled_iff _ _ (inv_ne_zero normalizer)).mpr (independent c selected)
    · have zeroCells : lawCell (selectedBinaryLaw D acyclic θ positive S) x y C c =
          fun _ _ => 0 := by
        funext a b
        exact incompatible_selected_law_cylinder D acyclic θ positive S _ contained _
          (fun h => selected ((selected_cell_assignment_iff S C contains x y xOutside yOutside c a b).mp h))
      rw [zeroCells]
      intro a b
      simp only [mul_zero, zero_mul, add_zero]

end RestrictedCausal.ProbabilitySource.BinaryCPT
