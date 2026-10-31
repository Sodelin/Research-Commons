import RationalPolynomialAvoidance
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Concrete binary parent-local CPT coordinates, full product masses, cylinder
marginals and two-by-two CI-minor polynomials. This is the algebraic interface
for D1/D2, not an assumed faithfulness oracle. DAG normalization, global
Markov soundness and the active-path witness construction remain separate.
Classical attribution: Meek (1995), Section 6.3 and binary atomic completeness.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Exactly one Bernoulli parameter for each vertex and parent assignment. -/
abbrev Coordinate (edge : V → V → Prop) :=
  (v : V) × ({p : V // edge p v} → Bool)

abbrev Assignment (V : Type u) := V → Bool

def row (edge : V → V → Prop) (w : Assignment V) (v : V) : Coordinate edge :=
  ⟨v, fun p => w p.val⟩

def bernoulliPolynomial {σ : Type*} (i : σ) (b : Bool) : MvPolynomial σ ℚ :=
  if b then MvPolynomial.X i else 1 - MvPolynomial.X i

def bernoulliMass {σ : Type*} (θ : σ → ℚ) (i : σ) (b : Bool) : ℚ :=
  if b then θ i else 1 - θ i

theorem eval_bernoulli {σ : Type*} (θ : σ → ℚ) (i : σ) (b : Bool) :
    MvPolynomial.eval θ (bernoulliPolynomial i b) = bernoulliMass θ i b := by
  cases b <;> simp [bernoulliPolynomial, bernoulliMass]

theorem bernoulli_mass_normalized {σ : Type*} (θ : σ → ℚ) (i : σ) :
    bernoulliMass θ i false + bernoulliMass θ i true = 1 := by
  simp [bernoulliMass]

theorem bernoulli_mass_pos {σ : Type*} (θ : σ → ℚ)
    (positive : ∀ i, 0 < θ i ∧ θ i < 1) (i : σ) (b : Bool) :
    0 < bernoulliMass θ i b := by
  cases b with
  | false => exact sub_pos.mpr (positive i).2
  | true => exact (positive i).1

def jointPolynomial (edge : V → V → Prop) (w : Assignment V) :
    MvPolynomial (Coordinate edge) ℚ :=
  ∏ v, bernoulliPolynomial (row edge w v) (w v)

def jointMass (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (w : Assignment V) : ℚ :=
  ∏ v, bernoulliMass θ (row edge w v) (w v)

theorem eval_joint (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (w : Assignment V) :
    MvPolynomial.eval θ (jointPolynomial edge w) = jointMass edge θ w := by
  simp only [jointPolynomial, jointMass, MvPolynomial.eval_prod, eval_bernoulli]

theorem joint_mass_pos (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (positive : ∀ i, 0 < θ i ∧ θ i < 1) (w : Assignment V) :
    0 < jointMass edge θ w :=
  Finset.prod_pos (fun v _ => bernoulli_mass_pos θ positive (row edge w v) (w v))

def Matches (C : Finset V) (c w : Assignment V) : Prop :=
  ∀ v ∈ C, w v = c v

instance matchesDecidable (C : Finset V) (c w : Assignment V) :
    Decidable (Matches C c w) := inferInstanceAs (Decidable (∀ v ∈ C, w v = c v))

def cylinderPolynomial (edge : V → V → Prop) (C : Finset V) (c : Assignment V) :
    MvPolynomial (Coordinate edge) ℚ :=
  ∑ w : Assignment V, if Matches C c w then jointPolynomial edge w else 0

def cylinderMass (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (C : Finset V) (c : Assignment V) : ℚ :=
  ∑ w : Assignment V, if Matches C c w then jointMass edge θ w else 0

theorem eval_cylinder (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (C : Finset V) (c : Assignment V) :
    MvPolynomial.eval θ (cylinderPolynomial edge C c) = cylinderMass edge θ C c := by
  unfold cylinderPolynomial cylinderMass
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases matching : Matches C c w
  · simp only [if_pos matching, eval_joint]
  · simp only [if_neg matching, map_zero]

theorem cylinder_mass_pos (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (positive : ∀ i, 0 < θ i ∧ θ i < 1) (C : Finset V) (c : Assignment V) :
    0 < cylinderMass edge θ C c := by
  unfold cylinderMass
  apply Finset.sum_pos'
  · intro w _
    by_cases matching : Matches C c w
    · simpa only [if_pos matching] using (joint_mass_pos edge θ positive w).le
    · simp only [if_neg matching, le_refl]
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    have matching : Matches C c c := fun _ _ => rfl
    simpa only [if_pos matching] using joint_mass_pos edge θ positive c

def cellAssignment (x y : V) (c : Assignment V) (a b : Bool) : Assignment V :=
  fun v => if v = x then a else if v = y then b else c v

def cellPolynomial (edge : V → V → Prop) (x y : V) (C : Finset V)
    (c : Assignment V) (a b : Bool) : MvPolynomial (Coordinate edge) ℚ :=
  cylinderPolynomial edge (insert x (insert y C)) (cellAssignment x y c a b)

def cellMass (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (x y : V) (C : Finset V) (c : Assignment V) (a b : Bool) : ℚ :=
  cylinderMass edge θ (insert x (insert y C)) (cellAssignment x y c a b)

theorem eval_cell (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (x y : V) (C : Finset V) (c : Assignment V) (a b : Bool) :
    MvPolynomial.eval θ (cellPolynomial edge x y C c a b) =
      cellMass edge θ x y C c a b :=
  eval_cylinder edge θ _ _

/-- Intended CI interpretation requires x ≠ y and x,y outside C.
The polynomial itself is defined on every input, without an oracle premise. -/
def minorPolynomial (edge : V → V → Prop) (x y : V) (C : Finset V)
    (c : Assignment V) : MvPolynomial (Coordinate edge) ℚ :=
  cellPolynomial edge x y C c false false * cellPolynomial edge x y C c true true -
    cellPolynomial edge x y C c false true * cellPolynomial edge x y C c true false

theorem eval_minor (edge : V → V → Prop) (θ : Coordinate edge → ℚ)
    (x y : V) (C : Finset V) (c : Assignment V) :
    MvPolynomial.eval θ (minorPolynomial edge x y C c) =
      cellMass edge θ x y C c false false * cellMass edge θ x y C c true true -
        cellMass edge θ x y C c false true * cellMass edge θ x y C c true false := by
  simp only [minorPolynomial, map_sub, map_mul, eval_cell]

end RestrictedCausal.ProbabilitySource.BinaryCPT
