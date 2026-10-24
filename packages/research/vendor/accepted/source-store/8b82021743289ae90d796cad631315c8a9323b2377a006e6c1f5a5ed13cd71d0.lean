import G3BernoulliCriticalNumerators
import G3AllResidueNormalIdentities
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Genuine p-polynomial coefficient of the cap-seven critical numerator.
Its nonzero leading coefficient on 0<q<1 excludes strict vertical curves.
No Sylvester resultant or finite-critical-locus assertion is assumed. -/
noncomputable section
namespace GProgram.G3.AllResidue
open scoped BigOperators
open Polynomial

def probabilityPolynomial (n : ℕ) (q : ℝ) : Polynomial ℝ :=
  C 1 + C (q^n-1)*X

def criticalProbabilityPolynomial (c : Fin 6 → ℝ) (exponent : Fin 6 → ℕ)
    (q : ℝ) : Polynomial ℝ :=
  ∑ i, C (c i*(1-q^(exponent i))) *
    ∏ j ∈ Finset.univ.erase i, probabilityPolynomial (exponent j) q

theorem probability_polynomial_degree_le (n : ℕ) (q : ℝ) :
    (probabilityPolynomial n q).natDegree ≤ 1 := by
  unfold probabilityPolynomial
  apply natDegree_add_le_of_degree_le
  · simp
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le

theorem probability_polynomial_coeff_one (n : ℕ) (q : ℝ) :
    (probabilityPolynomial n q).coeff 1 = q^n-1 := by
  simp only [probabilityPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X_one]
  norm_num

theorem probability_polynomial_eval (n : ℕ) (p q : ℝ) :
    (probabilityPolynomial n q).eval p = bernoulliFactor n p q := by
  simp [probabilityPolynomial,bernoulliFactor]
  ring

theorem critical_probability_eval (c : Fin 6 → ℝ) (exponent : Fin 6 → ℕ)
    (p q : ℝ) :
    (criticalProbabilityPolynomial c exponent q).eval p =
      pCriticalNumerator c exponent p q := by
  simp only [criticalProbabilityPolynomial,pCriticalNumerator,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, probability_polynomial_eval]

theorem critical_probability_coeff_five (c : Fin 6 → ℝ)
    (exponent : Fin 6 → ℕ) (q : ℝ) :
    (criticalProbabilityPolynomial c exponent q).coeff 5 =
      -(∑ i, c i) * ∏ i, (1-q^(exponent i)) := by
  have hcard (i : Fin 6) : (Finset.univ.erase i).card = 5 := by simp
  have hprod (i : Fin 6) :
      (∏ j ∈ Finset.univ.erase i, probabilityPolynomial (exponent j) q).coeff 5 =
        ∏ j ∈ Finset.univ.erase i, (q^(exponent j)-1) := by
    have hc := Polynomial.coeff_prod_of_natDegree_le
      (s := Finset.univ.erase i) (fun j => probabilityPolynomial (exponent j) q) 1
      (fun j _ => probability_polynomial_degree_le _ _)
    simpa only [hcard, Nat.mul_one, probability_polynomial_coeff_one] using hc
  have hneg (i : Fin 6) :
      (∏ j ∈ Finset.univ.erase i, (q^(exponent j)-1)) =
        -(∏ j ∈ Finset.univ.erase i, (1-q^(exponent j))) := by
    simp_rw [show ∀ j : Fin 6, q^(exponent j)-1 = -(1-q^(exponent j)) by intro j; ring]
    rw [Finset.prod_neg, hcard]
    norm_num
  unfold criticalProbabilityPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, hprod, hneg]
  have hterm (i : Fin 6) :
      c i*(1-q^(exponent i)) * -(∏ j ∈ Finset.univ.erase i, (1-q^(exponent j))) =
        -(c i * ∏ j, (1-q^(exponent j))) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (1-q^(exponent j)))
      (Finset.mem_univ i)]
    ring
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

def capSevenExponent (i : Fin 6) : ℕ := match i.val with
  | 0 => 1 | 1 => 3 | 2 => 6 | 3 => 10 | 4 => 15 | _ => 21

def normalWeight (r : ℝ) (i : Fin 6) : ℝ := match i.val with
  | 0 => normalB0 r | 1 => normalB1 r | 2 => normalB2 r
  | 3 => normalB3 r | 4 => normalB4 r | _ => normalB5 r

theorem normal_weight_sum (r : ℝ) : ∑ i, normalWeight r i = normalMass r := by
  simpa [Fin.sum_univ_succ,normalWeight,add_assoc] using normal_sum r

theorem cap_seven_exponent_ne_zero (i : Fin 6) : capSevenExponent i ≠ 0 := by
  fin_cases i <;> simp [capSevenExponent]

theorem strict_q_loss_product_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < ∏ i, (1-q^(capSevenExponent i)) := by
  apply Finset.prod_pos
  intro i _
  exact sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (cap_seven_exponent_ne_zero i))

theorem normal_probability_coeff_five_ne_zero {r q : ℝ}
    (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) :
    (criticalProbabilityPolynomial (normalWeight r) capSevenExponent q).coeff 5 ≠ 0 := by
  rw [critical_probability_coeff_five,normal_weight_sum]
  exact mul_ne_zero (neg_ne_zero.mpr (normal_mass_ne_zero hr))
    (ne_of_gt (strict_q_loss_product_pos hq0 hq1))

theorem normal_probability_polynomial_ne_zero {r q : ℝ}
    (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) :
    criticalProbabilityPolynomial (normalWeight r) capSevenExponent q ≠ 0 := by
  intro h
  have hc := normal_probability_coeff_five_ne_zero hr hq0 hq1
  apply hc
  rw [h]
  simp

theorem no_strict_vertical_critical_line {r q : ℝ}
    (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ (∀ p : ℝ, pCriticalNumerator (normalWeight r) capSevenExponent p q = 0) := by
  intro hall
  have hz : criticalProbabilityPolynomial (normalWeight r) capSevenExponent q = 0 := by
    apply Polynomial.funext
    intro p
    rw [critical_probability_eval, hall p]
    simp
  exact normal_probability_polynomial_ne_zero hr hq0 hq1 hz

#print axioms critical_probability_eval
#print axioms critical_probability_coeff_five
#print axioms normal_weight_sum
#print axioms normal_probability_coeff_five_ne_zero
#print axioms normal_probability_polynomial_ne_zero
#print axioms no_strict_vertical_critical_line
end GProgram.G3.AllResidue
