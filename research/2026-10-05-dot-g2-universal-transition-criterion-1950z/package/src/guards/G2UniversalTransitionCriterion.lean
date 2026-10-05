import UnifiedLean.Source.MatrixProjectionExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option debug.skipKernelTC false

/-!
Original G2 universal transition criterion, necessity direction.
Contributor: dot (OpenAI), 2026-10-05.
Classical differentiation of semigroup identities at zero. This is an operator
criterion at the universal initial-state/transition-test interface, not an
inference from a single endpoint observation and not source realizability.
-/
namespace GProgram.G2.UniversalTransitionCriterion
set_option backward.isDefEq.respectTransparency false
open NormedSpace Matrix
open scoped Matrix.Norms.Operator NNReal

lemma commute_of_nonnegative_exp_commute {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (Q P : A)
    (h : ∀ t : ℝ, 0 ≤ t → exp (t • Q) * P = P * exp (t • Q)) :
    Q * P = P * Q := by
  have hd : HasDerivAt (fun t : ℝ => exp (t • Q)) Q 0 := by
    simpa using (hasDerivAt_exp_smul_const Q (0 : ℝ))
  have hl := (hd.mul_const P).hasDerivWithinAt (s := Set.Ici (0 : ℝ))
  have hr := (hd.const_mul P).hasDerivWithinAt (s := Set.Ici (0 : ℝ))
  have hr' : HasDerivWithinAt (fun t : ℝ => exp (t • Q) * P)
      (P * Q) (Set.Ici (0 : ℝ)) 0 :=
    hr.congr (fun t ht => h t ht) (h 0 le_rfl)
  exact ContinuousLinearMap.toSpanSingleton_inj.mp ((uniqueDiffOn_Ici (0 : ℝ)).eq (by simp) hl hr')

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
open UnifiedLean.Source.MatrixProjectionExponential

/-- Nonnegative durations suffice for the necessary generator identity. -/
theorem generator_intertwining_of_nonnegative_time
    (Q : Matrix I I ℝ) (R : Matrix J J ℝ) (P : Matrix I J ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → exp (t • Q) * P = P * exp (t • R)) :
    Q * P = P * R := by
  let D : Matrix (I ⊕ J) (I ⊕ J) ℝ := fromBlocks Q 0 0 R
  let C : Matrix (I ⊕ J) (I ⊕ J) ℝ := fromBlocks 0 P 0 0
  have hc : D * C = C * D := by
    apply commute_of_nonnegative_exp_commute
    intro t ht
    have he : exp (t • D) = fromBlocks (exp (t • Q)) 0 0 (exp (t • R)) := by
      rw [show t • D = fromBlocks (t • Q) 0 0 (t • R) by simp [D, fromBlocks_smul]]
      exact exp_fromBlocks_diagonal _ _
    rw [he]
    simp only [C, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [h t ht]
  have hp := congrArg Matrix.toBlocks₁₂ hc
  simpa only [D, C, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, toBlocks_fromBlocks₁₂] using hp

/-- Exact iff for every nonnegative-duration universal transition test. -/
theorem generator_iff_nonnegative_time
    (Q : Matrix I I ℝ) (R : Matrix J J ℝ) (P : Matrix I J ℝ) :
    Q * P = P * R ↔ ∀ t : ℝ, 0 ≤ t → exp (t • Q) * P = P * exp (t • R) := by
  constructor
  · intro h t _
    exact rectangular_scaled_exp_intertwining Q R P h t
  · exact generator_intertwining_of_nonnegative_time Q R P

/-- Universal operator-test alphabet. Physical source chronology is a separate
restriction on words, not permission to repeat an original hybrid event. -/
abbrev TestStep (Pulse : Type*) := ℝ≥0 ⊕ Pulse

noncomputable def stepMatrix {Pulse : Type*} (Q : Matrix I I ℝ)
    (R : Pulse → Matrix I I ℝ) : TestStep Pulse → Matrix I I ℝ
  | .inl t => exp ((t : ℝ) • Q)
  | .inr a => R a

noncomputable def programMatrix {Pulse : Type*} (Q : Matrix I I ℝ)
    (R : Pulse → Matrix I I ℝ) : List (TestStep Pulse) → Matrix I I ℝ
  | [] => 1
  | s :: w => stepMatrix Q R s * programMatrix Q R w

/-- Full original universal operator criterion: local generator and pulse
identities are equivalent to every finite transition program identity. -/
theorem generator_and_pulses_iff_all_programs {Pulse : Type*}
    (Q : Matrix I I ℝ) (Q' : Matrix J J ℝ)
    (R : Pulse → Matrix I I ℝ) (R' : Pulse → Matrix J J ℝ)
    (P : Matrix I J ℝ) :
    (Q * P = P * Q' ∧ ∀ a, R a * P = P * R' a) ↔
      ∀ w : List (TestStep Pulse), programMatrix Q R w * P = P * programMatrix Q' R' w := by
  constructor
  · rintro ⟨hg, hp⟩ w
    induction w with
    | nil => simp [programMatrix]
    | cons s w ih =>
      apply rectangular_product_intertwining _ _ _ _ P _ ih
      cases s with
      | inl t => exact rectangular_scaled_exp_intertwining Q Q' P hg t
      | inr a => exact hp a
  · intro hw
    constructor
    · apply generator_intertwining_of_nonnegative_time Q Q' P
      intro t ht
      have hh := hw [Sum.inl (⟨t, ht⟩ : ℝ≥0)]
      simp only [programMatrix, stepMatrix, Matrix.mul_one] at hh
      change exp (t • Q) * P = P * exp (t • Q') at hh
      exact hh
    · intro a
      simpa [programMatrix, stepMatrix] using hw [Sum.inr a]

omit [DecidableEq I] [DecidableEq J] in
/-- Point initial states and selected-state indicator tests determine the
entire transition identity; one selected endpoint is not enough. -/
theorem universal_rows_iff_matrix_identity (A : Matrix I I ℝ)
    (B : Matrix J J ℝ) (P : Matrix I J ℝ) :
    (∀ i j, (A * P) i j = (P * B) i j) ↔ A * P = P * B := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrArg (fun M => M i j) h

#print axioms generator_iff_nonnegative_time
#print axioms generator_and_pulses_iff_all_programs
#print axioms universal_rows_iff_matrix_identity
end GProgram.G2.UniversalTransitionCriterion
