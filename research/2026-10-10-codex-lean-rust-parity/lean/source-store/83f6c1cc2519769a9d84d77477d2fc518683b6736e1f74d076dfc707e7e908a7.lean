import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite moment/order certificate for the G3 all-factor obstruction

This is the exact finite algebraic interface supplied by the G3 source worker.
Uniform log-factor bounds and biological closure/source attainment remain
separate source-reviewed estimates, not axioms inserted here.
-/

namespace GProgram.G3.MomentBarrier

open scoped BigOperators

theorem exact_double_sum {n : Nat} (p : Fin n → ℝ) :
    (∑ i, ∑ j, p i*p j*(p i-p j)^2) =
      2*((∑ i, p i)*(∑ i, (p i)^3)-(∑ i, (p i)^2)^2) := by
  have hterm : ∀ i j, p i*p j*(p i-p j)^2 =
      (p i)^3*p j+p i*(p j)^3-2*(p i)^2*(p j)^2 := by intro i j; ring
  simp_rw [hterm,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem finite_moment_inequality {n : Nat} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i, (p i)^2)^2 ≤ (∑ i, p i)*(∑ i, (p i)^3) := by
  have hnonneg : 0 ≤ ∑ i, ∑ j, p i*p j*(p i-p j)^2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (hp i) (hp j)) (sq_nonneg _)
  rw [exact_double_sum] at hnonneg
  nlinarith

theorem coupled_barrier_minimal {P Q T U d B0 B1 g K C : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hd : 0 < d) (hB1 : 0 ≤ B1)
    (hPQ : d*P ≤ B0*Q) (hTP : g*T ≤ B1*P^2)
    (hQT : Q^2 ≤ U*T) (hUC : U ≤ K*C)
    (hgap : B1*B0^2*K*C < d^2*g) : T = 0 ∧ P = 0 := by
  have hsq : d^2*P^2 ≤ B0^2*Q^2 := by
    have hh := mul_self_le_mul_self (mul_nonneg hd.le hP) hPQ
    nlinarith only [hh]
  have h1 : d^2*g*T ≤ d^2*B1*P^2 := by
    have hh := mul_le_mul_of_nonneg_left hTP (sq_nonneg d)
    nlinarith only [hh]
  have h2 : d^2*B1*P^2 ≤ B1*B0^2*Q^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq hB1
    nlinarith only [hh]
  have h3 : B1*B0^2*Q^2 ≤ B1*B0^2*U*T := by
    have hh := mul_le_mul_of_nonneg_left hQT (mul_nonneg hB1 (sq_nonneg B0))
    nlinarith only [hh]
  have h4 : B1*B0^2*U*T ≤ B1*B0^2*K*C*T := by
    have hh := mul_le_mul_of_nonneg_left hUC
      (mul_nonneg (mul_nonneg hB1 (sq_nonneg B0)) hT)
    nlinarith only [hh]
  have hbound := h1.trans (h2.trans (h3.trans h4))
  have ht : T = 0 := by
    by_contra hne
    have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hne)
    have hstrict := mul_lt_mul_of_pos_right hgap hpos
    exact not_lt_of_ge hbound hstrict
  have hq : Q = 0 := by rw [ht,mul_zero] at hQT; nlinarith
  have hp0 : P = 0 := by rw [hq,mul_zero] at hPQ; nlinarith
  exact ⟨ht,hp0⟩

/-- Source-facing positive-constant wrapper; the helper above shows which
    hypotheses the finite scalar step actually requires. -/
theorem coupled_barrier {P Q T U d B0 B1 g K C : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hd : 0 < d) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hg : 0 < g) (hK : 0 < K) (hC : 0 < C)
    (hPQ : d*P ≤ B0*Q) (hTP : g*T ≤ B1*P^2)
    (hQT : Q^2 ≤ U*T) (hUC : U ≤ K*C)
    (hgap : B1*B0^2*K*C < d^2*g) : T = 0 ∧ P = 0 := by
  exact coupled_barrier_minimal hP hT hd hB1.le hPQ hTP hQT hUC hgap

#print axioms coupled_barrier_minimal
#print axioms exact_double_sum
#print axioms finite_moment_inequality
#print axioms coupled_barrier

end GProgram.G3.MomentBarrier
