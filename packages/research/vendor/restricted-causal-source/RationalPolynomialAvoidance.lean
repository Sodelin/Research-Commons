import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Interval.Set.Infinite

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration, compilation, or execution.

The rational avoidance part of D5, using mathlib's polynomial extensionality
on boxes with infinite sides. The polynomial family must already be nonzero.
This file does NOT prove that causal CI minors are nonzero, construct a
faithful binary DAG model, or discharge the shared-mechanism adapter.

The algebra is classical. The imported box-extensionality result is by
mathlib contributors, not a new faithfulness theorem.
-/

namespace RestrictedCausal.ProbabilitySource

open scoped BigOperators

universe u v

/-- A nonzero rational polynomial has a nonzero value in the positive
rational unit cube. No enumeration or evaluated witness is claimed. -/
theorem exists_positive_rational_eval_ne_zero {σ : Type u}
    (p : MvPolynomial σ ℚ) (hp : p ≠ 0) :
    ∃ θ : σ → ℚ, (∀ j, 0 < θ j ∧ θ j < 1) ∧
      MvPolynomial.eval θ p ≠ 0 := by
  classical
  have hex : ∃ θ ∈ Set.pi Set.univ (fun _ : σ => Set.Ioo (0 : ℚ) 1),
      MvPolynomial.eval θ p ≠ 0 := by
    by_contra none
    apply hp
    apply MvPolynomial.funext_set (fun _ : σ => Set.Ioo (0 : ℚ) 1)
      (fun _ => Set.Ioo_infinite (show (0 : ℚ) < 1 from zero_lt_one))
    intro θ hθ
    have hz : MvPolynomial.eval θ p = 0 := by
      by_contra nonzero
      exact none ⟨θ, hθ, nonzero⟩
    simpa only [map_zero] using hz
  obtain ⟨θ, hθ, hne⟩ := hex
  exact ⟨θ, fun j => hθ j (Set.mem_univ j), hne⟩

/-- One positive rational parameter point avoids every member of a supplied
finite family of nonzero rational polynomials. The same θ serves all i. -/
theorem exists_common_positive_rational_point {σ : Type u} {I : Type v}
    [Fintype I] (p : I → MvPolynomial σ ℚ) (hp : ∀ i, p i ≠ 0) :
    ∃ θ : σ → ℚ, (∀ j, 0 < θ j ∧ θ j < 1) ∧
      ∀ i, MvPolynomial.eval θ (p i) ≠ 0 := by
  classical
  have hprod : (∏ i, p i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  obtain ⟨θ, positive, nonzero⟩ :=
    exists_positive_rational_eval_ne_zero (∏ i, p i) hprod
  refine ⟨θ, positive, ?_⟩
  have evaluated : (∏ i, MvPolynomial.eval θ (p i)) ≠ 0 := by
    simpa only [MvPolynomial.eval_prod] using nonzero
  exact fun i => (Finset.prod_ne_zero_iff.mp evaluated) i (Finset.mem_univ i)

/-- A witness can be anywhere in rational parameter space, including a
boundary point with some deterministic coordinates. Positivity is needed
at the FINAL common point, not at each separate nonvanishing witness.
This does not assert that a causal CI minor is nonzero at an all-Boolean
CPT corner: such a finite-DAG law is a point mass and all its minors vanish. -/
theorem exists_common_positive_point_of_separate_witnesses
    {σ : Type u} {I : Type v} [Fintype I]
    (p : I → MvPolynomial σ ℚ)
    (witness : ∀ i, ∃ θ : σ → ℚ, MvPolynomial.eval θ (p i) ≠ 0) :
    ∃ θ : σ → ℚ, (∀ j, 0 < θ j ∧ θ j < 1) ∧
      ∀ i, MvPolynomial.eval θ (p i) ≠ 0 := by
  apply exists_common_positive_rational_point p
  intro i zeroPolynomial
  obtain ⟨θ, nonzero⟩ := witness i
  apply nonzero
  rw [zeroPolynomial, map_zero]

end RestrictedCausal.ProbabilitySource
