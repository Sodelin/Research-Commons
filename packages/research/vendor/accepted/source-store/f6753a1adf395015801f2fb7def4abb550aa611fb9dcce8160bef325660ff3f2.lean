import G3BernoulliDerivatives
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-! Exact finite cleared critical equations of the actual Bernoulli log
response. Strict-domain denominator/p factors are proved nonzero. -/
noncomputable section
namespace GProgram.G3.AllResidue
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceDenominator (exponent : ι → ℕ) (p q : ℝ) : ℝ :=
  ∏ i, bernoulliFactor (exponent i) p q

def weightedPResponse (c : ι → ℝ) (exponent : ι → ℕ) (p q : ℝ) : ℝ :=
  ∑ i, c i * ((1-q^(exponent i))/bernoulliFactor (exponent i) p q)

def weightedQResponse (c : ι → ℝ) (exponent : ι → ℕ) (p q : ℝ) : ℝ :=
  ∑ i, c i * ((-p*(exponent i : ℝ)*q^(exponent i-1))/
    bernoulliFactor (exponent i) p q)

def pCriticalNumerator (c : ι → ℝ) (exponent : ι → ℕ) (p q : ℝ) : ℝ :=
  ∑ i, c i*(1-q^(exponent i))*
    ∏ j ∈ Finset.univ.erase i, bernoulliFactor (exponent j) p q

def qCriticalNumerator (c : ι → ℝ) (exponent : ι → ℕ) (p q : ℝ) : ℝ :=
  ∑ i, c i*(exponent i : ℝ)*q^(exponent i-1)*
    ∏ j ∈ Finset.univ.erase i, bernoulliFactor (exponent j) p q

theorem source_denominator_pos (exponent : ι → ℕ) {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    0 < sourceDenominator exponent p q := by
  unfold sourceDenominator
  apply Finset.prod_pos
  intro i _
  exact bernoulli_factor_pos hp0 hp1 hq0

theorem clear_p_response (c : ι → ℝ) (exponent : ι → ℕ) {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    sourceDenominator exponent p q * weightedPResponse c exponent p q =
      pCriticalNumerator c exponent p q := by
  unfold sourceDenominator weightedPResponse pCriticalNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hne : bernoulliFactor (exponent i) p q ≠ 0 :=
    ne_of_gt (bernoulli_factor_pos hp0 hp1 hq0)
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => bernoulliFactor (exponent j) p q) (Finset.mem_univ i)]
  field_simp
  <;> ring

theorem clear_q_response (c : ι → ℝ) (exponent : ι → ℕ) {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    sourceDenominator exponent p q * weightedQResponse c exponent p q =
      -p*qCriticalNumerator c exponent p q := by
  unfold sourceDenominator weightedQResponse qCriticalNumerator
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hne : bernoulliFactor (exponent i) p q ≠ 0 :=
    ne_of_gt (bernoulli_factor_pos hp0 hp1 hq0)
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => bernoulliFactor (exponent j) p q) (Finset.mem_univ i)]
  field_simp
  <;> ring

theorem p_response_zero_iff (c : ι → ℝ) (exponent : ι → ℕ) {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    weightedPResponse c exponent p q = 0 ↔ pCriticalNumerator c exponent p q = 0 := by
  have hD := source_denominator_pos exponent hp0 hp1 hq0
  have hc := clear_p_response c exponent hp0 hp1 hq0
  constructor
  · intro h; rw [h,mul_zero] at hc; exact hc.symm
  · intro h; rw [h] at hc; exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt hD)

theorem q_response_zero_iff (c : ι → ℝ) (exponent : ι → ℕ) {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    weightedQResponse c exponent p q = 0 ↔ qCriticalNumerator c exponent p q = 0 := by
  have hD := source_denominator_pos exponent hp0 hp1 hq0
  have hc := clear_q_response c exponent hp0 hp1 hq0
  constructor
  · intro h
    rw [h,mul_zero] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left (neg_ne_zero.mpr (ne_of_gt hp0))
  · intro h
    rw [h,mul_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt hD)

#print axioms source_denominator_pos
#print axioms clear_p_response
#print axioms clear_q_response
#print axioms p_response_zero_iff
#print axioms q_response_zero_iff
end GProgram.G3.AllResidue
