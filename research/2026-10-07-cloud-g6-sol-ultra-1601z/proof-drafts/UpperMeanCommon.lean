import UnifiedLean.G6.MeanEnclosure

/-!
UNCHECKED additive draft, CLOUD-G6-SOL-ULTRA-20261007, 2026-10-07.
Finite polynomial and common-count witnesses for UPPER-MEAN-COMMON-HISTORY.md.
The normalized reference uses actual a, while residual coefficients use b.
No executable enclosure oracle, rate-bank perturbation or full program theorem
is supplied by this file. Existing providers are read-only.
-/
namespace UnifiedLean.G6.UpperMeanCommon
open UnifiedLean.G6.SourcePrefix UnifiedLean.G6.TaylorCertificate
open UnifiedLean.G6.ResidualPrefix UnifiedLean.G6.Conditioning
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
open scoped BigOperators NNReal

lemma pow_succ_difference_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    b ^ (n + 1) - a ^ (n + 1) ≤ (b - a) * (n + 1) * b ^ n := by
  have hb : 0 ≤ b := ha.trans hab
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := pow_le_pow_left₀ ha hab (n + 1)
    calc
      b ^ (n + 1 + 1) - a ^ (n + 1 + 1) =
          b * (b ^ (n + 1) - a ^ (n + 1)) + (b - a) * a ^ (n + 1) := by
            rw [pow_succ b (n + 1), pow_succ a (n + 1)]
            ring
      _ ≤ b * ((b - a) * (n + 1) * b ^ n) + (b - a) * b ^ (n + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left ih hb) (mul_le_mul_of_nonneg_left hp hd)
      _ = (b - a) * ((n + 1 : ℕ) + 1) * b ^ (n + 1) := by
        push_cast
        rw [pow_succ]
        ring

lemma taylorTerm_difference_succ_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (n : ℕ) :
    taylorTerm b (n + 1) - taylorTerm a (n + 1) ≤
      (b - a) * taylorTerm b n := by
  have h := div_le_div_of_nonneg_right (pow_succ_difference_le a b ha hab n)
    (show (0 : ℝ) ≤ (n + 1).factorial by positivity)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  calc
    taylorTerm b (n + 1) - taylorTerm a (n + 1) =
        (b ^ (n + 1) - a ^ (n + 1)) / (n + 1).factorial := by
          simp only [taylorTerm, sub_div]
    _ ≤ ((b - a) * (n + 1) * b ^ n) / (n + 1).factorial := h
    _ = (b - a) * taylorTerm b n := by
      simp only [taylorTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [hn, hf]
      <;> ring

lemma taylorPrefix_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (K : ℕ) :
    taylorPrefix a K ≤ taylorPrefix b K := by
  apply Finset.sum_le_sum
  intro k hk
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab k) (by positivity)

lemma taylorPrefix_difference_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (K : ℕ) :
    taylorPrefix b K - taylorPrefix a K ≤ (b - a) * taylorPrefix b K := by
  have hb : 0 ≤ b := ha.trans hab
  have hsum : (∑ k ∈ Finset.range K, taylorTerm b k) ≤ taylorPrefix b K := by
    unfold taylorPrefix
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (taylorTerm_nonneg hb K)
  have hshift : taylorPrefix b K - taylorPrefix a K =
      ∑ k ∈ Finset.range K, (taylorTerm b (k + 1) - taylorTerm a (k + 1)) := by
    unfold taylorPrefix
    rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
    simp only [taylorTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      sub_self, add_zero]
  rw [hshift]
  calc
    (∑ k ∈ Finset.range K, (taylorTerm b (k + 1) - taylorTerm a (k + 1))) ≤
        ∑ k ∈ Finset.range K, (b - a) * taylorTerm b k :=
      Finset.sum_le_sum (fun k _ => taylorTerm_difference_succ_le a b ha hab k)
    _ = (b - a) * ∑ k ∈ Finset.range K, taylorTerm b k := by rw [Finset.mul_sum]
    _ ≤ (b - a) * taylorPrefix b K :=
      mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hab)

noncomputable def upperDenominator (b : ℝ≥0) (K : ℕ) : ℝ :=
  taylorPrefix (b : ℝ) K + 2 * taylorTerm (b : ℝ) (K + 1)

noncomputable def upperCommonMass (a b : ℝ≥0) (K : ℕ) : ℝ :=
  taylorPrefix (a : ℝ) K / upperDenominator b K

lemma upperDenominator_pos (b : ℝ≥0) (K : ℕ) : 0 < upperDenominator b K := by
  have hS := taylorPrefix_pos b K
  have hT := taylorTerm_nonneg b.coe_nonneg (K + 1)
  unfold upperDenominator
  linarith

lemma upperCommonMass_bounds (a b : ℝ≥0) (hab : a ≤ b) (K : ℕ) :
    0 < upperCommonMass a b K ∧ upperCommonMass a b K ≤ 1 := by
  have hS := taylorPrefix_mono (a : ℝ) b a.coe_nonneg (by exact_mod_cast hab) K
  have hT := taylorTerm_nonneg b.coe_nonneg (K + 1)
  constructor
  · exact div_pos (taylorPrefix_pos a K) (upperDenominator_pos b K)
  · apply (div_le_one (upperDenominator_pos b K)).mpr
    dsimp [upperDenominator]
    linarith

lemma upperCommonMass_le_prefixMass (a b : ℝ≥0) (hab : a ≤ b) (K : ℕ)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2) :
    upperCommonMass a b K ≤ prefixMass a K := by
  have he : Real.exp (a : ℝ) ≤ upperDenominator b K :=
    (Real.exp_le_exp.mpr (by exact_mod_cast hab)).trans
      (exp_le_taylor_enclosure b.coe_nonneg K hK)
  rw [prefixMass_taylor, Real.exp_neg]
  simpa only [upperCommonMass, div_eq_mul_inv, mul_comm] using
    div_le_div_of_nonneg_left (taylorPrefix_pos a K).le (Real.exp_pos (a : ℝ)) he

lemma upperCommonMass_deficit_le (a b : ℝ≥0) (hab : a ≤ b) (K : ℕ) :
    1 - upperCommonMass a b K ≤ (b : ℝ) - a + errorBound (b : ℝ) K := by
  have hd : (0 : ℝ) ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hpoly := taylorPrefix_difference_le (a : ℝ) b a.coe_nonneg
    (by exact_mod_cast hab) K
  have hu := upperDenominator_pos b K
  have hdiff : 1 - upperCommonMass a b K =
      (taylorPrefix (b : ℝ) K - taylorPrefix (a : ℝ) K) / upperDenominator b K +
        errorBound (b : ℝ) K := by
    unfold upperCommonMass upperDenominator errorBound
    field_simp [ne_of_gt hu]
    <;> ring
  have hquot := div_le_div_of_nonneg_right hpoly hu.le
  have hratio : ((b : ℝ) - a) * taylorPrefix (b : ℝ) K / upperDenominator b K ≤
      (b : ℝ) - a := by
    have h := mul_le_mul_of_nonneg_left (residualMass_bounds b K).2 hd
    simpa only [residualMass, upperDenominator, mul_div_assoc, mul_one] using h
  rw [hdiff]
  exact add_le_add_right (hquot.trans hratio) _

/-- The common normalized count law uses actual a, never upper b. -/
lemma upperCommonMass_count_domination (a b : ℝ≥0) (hab : a ≤ b) (K k : ℕ) :
    upperCommonMass a b K * (prefixCount a K k).toReal ≤
      residualMass (b : ℝ) K * (prefixCount b K k).toReal := by
  rw [prefixCount_real, prefixCount_real]
  by_cases hk : k ≤ K
  · rw [if_pos hk, if_pos hk]
    have hSa := ne_of_gt (taylorPrefix_pos a K)
    have hSb := ne_of_gt (taylorPrefix_pos b K)
    have hU := ne_of_gt (upperDenominator_pos b K)
    have heqa : upperCommonMass a b K *
        (taylorTerm (a : ℝ) k / taylorPrefix (a : ℝ) K) =
        taylorTerm (a : ℝ) k / upperDenominator b K := by
      unfold upperCommonMass
      field_simp [hSa, hU]
      <;> ring
    have heqb : residualMass (b : ℝ) K *
        (taylorTerm (b : ℝ) k / taylorPrefix (b : ℝ) K) =
        taylorTerm (b : ℝ) k / upperDenominator b K := by
      unfold residualMass upperDenominator
      field_simp [hSb, hU]
      <;> ring
    rw [heqa, heqb]
    apply div_le_div_of_nonneg_right _ (upperDenominator_pos b K).le
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ a.coe_nonneg (by exact_mod_cast hab) k) (by positivity)
  · simp only [if_neg hk, mul_zero, le_refl]

#print axioms pow_succ_difference_le
#print axioms taylorTerm_difference_succ_le
#print axioms taylorPrefix_mono
#print axioms taylorPrefix_difference_le
#print axioms upperDenominator_pos
#print axioms upperCommonMass_bounds
#print axioms upperCommonMass_le_prefixMass
#print axioms upperCommonMass_deficit_le
#print axioms upperCommonMass_count_domination
end UnifiedLean.G6.UpperMeanCommon
