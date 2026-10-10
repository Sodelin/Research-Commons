import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite exponential right-germ identification, with unknown rates

New proof contribution: dot's active source-assumption-first Lean lane,
2026-10-02. A finite exponential sum's coefficients are uniquely determined
on ANY right interval [0, epsilon), without a supplied event grid, derivative
oracle, or global common rate. The proof takes finitely many equally spaced
samples strictly within that interval and proves the resulting Vandermonde
matrix nonsingular. Rates can be arbitrary distinct real numbers.

For the G5 terminal-hybrid source argument, union the two finite rate sets,
append zero coefficients at missing rates, and include the zero exponent.
Equality of survival right germs then implies equality of its constant term.
That term equals not-yet-met routing mass only after the source-specific
permanent-pair-meeting and positive-current-rate argument; no such source
interpretation is assumed or proved by this algebraic/analytic module.
-/

namespace GProgram.G5.ExponentialGerm

open scoped BigOperators
open Matrix

noncomputable def expSum {n : ℕ} (rate coeff : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin n, coeff i * Real.exp (rate i * s)

/-- Finite nonzero-step exponential samples have full-rank coefficient map. -/
theorem coefficient_zero_of_grid {n : ℕ} (rate coeff : Fin n → ℝ)
    (hrate : Function.Injective rate) {step : ℝ} (hstep : step ≠ 0)
    (h : ∀ j : Fin n, expSum rate coeff (step * (j.val : ℝ)) = 0) :
    coeff = 0 := by
  have hnodes : Function.Injective (fun i : Fin n => Real.exp (rate i * step)) := by
    intro i j hij
    exact hrate (mul_right_cancel₀ hstep (Real.exp_injective hij))
  apply Matrix.eq_zero_of_vecMul_eq_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)
  funext j
  change (∑ i : Fin n, coeff i * Real.exp (rate i * step) ^ j.val) = 0
  convert h j using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- An entire right germ identifies ALL coefficients, not just a derivative
at one supplied order. The sample step is constructed inside the interval. -/
theorem coefficients_eq_of_right_germ {n : ℕ} (rate c d : Fin n → ℝ)
    (hrate : Function.Injective rate) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → expSum rate c s = expSum rate d s) : c = d := by
  let step : ℝ := ε / ((n + 1 : ℕ) : ℝ)
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hstep : 0 < step := div_pos hε hn
  have hzero : c - d = 0 := by
    apply coefficient_zero_of_grid rate (c - d) hrate hstep.ne'
    intro j
    have hj : (j.val : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.lt_trans j.isLt (Nat.lt_succ_self n))
    have hlt : step * (j.val : ℝ) < ε := by
      calc
        step * (j.val : ℝ) < step * ((n + 1 : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_left hj hstep
        _ = ε := div_mul_cancel₀ ε hn.ne'
    have heq := h (step * (j.val : ℝ)) (mul_nonneg hstep.le (Nat.cast_nonneg _)) hlt
    simpa only [expSum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
      using heq
  exact sub_eq_zero.mp hzero

/-- In particular the exponent-zero coefficient is observable. No numerical
values of the other positive/negative exponents need be supplied to the
comparison. Their finite union is only a proof-level common presentation. -/
theorem constant_coefficient_eq_of_right_germ {n : ℕ} (rate c d : Fin n → ℝ)
    (hrate : Function.Injective rate) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → expSum rate c s = expSum rate d s)
    (zeroIndex : Fin n) (_hz : rate zeroIndex = 0) : c zeroIndex = d zeroIndex := by
  exact congrFun (coefficients_eq_of_right_germ rate c d hrate hε h) zeroIndex

#print axioms coefficient_zero_of_grid
#print axioms coefficients_eq_of_right_germ
#print axioms constant_coefficient_eq_of_right_germ

end GProgram.G5.ExponentialGerm
