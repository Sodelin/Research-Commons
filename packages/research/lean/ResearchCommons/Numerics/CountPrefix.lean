import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
Formal integration of the OLD exact normalized Poisson-prefix contract.
The original arbitrary-precision Rust engine is reused unchanged. These are
scalar approximation results, not biological-source admission, a source
model, a physical-clock compiler or universal Rust implementation refinement.
The geometric remainder bound is the EXISTING Complex.exp_bound'.
-/

noncomputable section
namespace ResearchCommons.Numerics.CountPrefix
open scoped BigOperators

def poissonTerm (a : ℝ) (n : ℕ) : ℝ := a ^ n / (n.factorial : ℝ)
def prefixSum (a : ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1), poissonTerm a j
def upper (a : ℝ) (k : ℕ) : ℝ := prefixSum a k + 2 * poissonTerm a (k + 1)
def deficit (a : ℝ) (k : ℕ) : ℝ := 2 * poissonTerm a (k + 1) / upper a k
def lostMass (a : ℝ) (k : ℕ) : ℝ := 1 - prefixSum a k / Real.exp a

theorem term_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : 0 ≤ poissonTerm a n := by
  exact div_nonneg (pow_nonneg ha _) (Nat.cast_nonneg _)

theorem prefix_pos (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : 0 < prefixSum a k := by
  have hzero : 0 ∈ Finset.range (k + 1) := by simp
  have hterm : (1 : ℝ) = poissonTerm a 0 := by simp [poissonTerm]
  have hsum : (1 : ℝ) ≤ prefixSum a k := by
    rw [hterm]
    exact Finset.single_le_sum (fun j _ => term_nonneg a ha j) hzero
  exact lt_of_lt_of_le (by norm_num) hsum

theorem prefix_le_exp (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    prefixSum a k ≤ Real.exp a := by
  simpa only [prefixSum, poissonTerm] using Real.sum_le_exp_of_nonneg ha (k + 1)

theorem exp_le_upper (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (geometric : 2 * a ≤ (k + 2 : ℕ)) :
    Real.exp a ≤ upper a k := by
  have hden : (0 : ℝ) < ((k + 1).succ : ℕ) := by positivity
  have hratio : a / (((k + 1).succ : ℕ) : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).2
    push_cast at geometric ⊢
    linarith
  have hcomplex : ‖(a : ℂ)‖ / (((k + 1).succ : ℕ) : ℝ) ≤ 1 / 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using hratio
  have hbound := Complex.exp_bound' (x := (a : ℂ)) (n := k + 1) hcomplex
  have hreal :
      |Real.exp a - ∑ j ∈ Finset.range (k + 1), a ^ j / (j.factorial : ℝ)| ≤
        |a| ^ (k + 1) / ((k + 1).factorial : ℝ) * 2 := by
    convert hbound using 1 <;> norm_cast
  have herr : Real.exp a - prefixSum a k ≤ 2 * poissonTerm a (k + 1) := by
    have h := le_trans (le_abs_self _) hreal
    simpa only [prefixSum, poissonTerm, abs_of_nonneg ha, mul_comm] using h
  unfold upper
  linarith

theorem normalized_prefix_sum (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), poissonTerm a j / prefixSum a k) = 1 := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (prefix_pos a ha k))

theorem lostMass_nonneg (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    0 ≤ lostMass a k := by
  have h : prefixSum a k / Real.exp a ≤ 1 := by
    apply (div_le_iff₀ (Real.exp_pos a)).2
    simpa using prefix_le_exp a ha k
  unfold lostMass
  linarith

theorem lostMass_le_deficit (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (geometric : 2 * a ≤ (k + 2 : ℕ)) :
    lostMass a k ≤ deficit a k := by
  have hS := prefix_pos a ha k
  have hT := term_nonneg a ha (k + 1)
  have hU : 0 < upper a k := by unfold upper; linarith
  have hE := Real.exp_pos a
  have hbound := exp_le_upper a ha k geometric
  have hproduct : 0 ≤ prefixSum a k * (upper a k - Real.exp a) :=
    mul_nonneg hS.le (sub_nonneg.mpr hbound)
  unfold deficit
  apply (le_div_iff₀ hU).2
  unfold lostMass
  have heq :
      (1 - prefixSum a k / Real.exp a) * upper a k =
        ((Real.exp a - prefixSum a k) * upper a k) / Real.exp a := by
    field_simp [ne_of_gt hE] <;> ring
  rw [heq]
  apply (div_le_iff₀ hE).2
  have htotal : upper a k = prefixSum a k + 2 * poissonTerm a (k + 1) := rfl
  nlinarith

theorem certified_error (a epsilon : ℝ) (k : ℕ) (ha : 0 ≤ a)
    (geometric : 2 * a ≤ (k + 2 : ℕ)) (accuracy : deficit a k ≤ epsilon) :
    0 ≤ lostMass a k ∧ lostMass a k ≤ epsilon :=
  ⟨lostMass_nonneg a ha k, (lostMass_le_deficit a ha k geometric).trans accuracy⟩

end ResearchCommons.Numerics.CountPrefix
