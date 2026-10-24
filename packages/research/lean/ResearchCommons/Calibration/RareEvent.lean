import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Formalization candidate for the OLD CALIBRATION-BOUND.md, CB-MEMORY-004.
The original mathematics is complete. Current elaboration is pending.
Independent fully observed Bernoulli trials and one SAME randomized decision
rule under both hypotheses are literal definitions, not supplied risk bounds.
-/

namespace ResearchCommons.Calibration
noncomputable section
open scoped BigOperators

abbrev EventRate := Set.Ioo (0 : ℝ) 1
abbrev Probability := Set.Icc (0 : ℝ) 1
abbrev Sample (n : ℕ) := Fin n → Bool
abbrev Decision (n : ℕ) := Sample n → Probability

def zeroSample (n : ℕ) : Sample n := fun _ => false

def bitMass (e : EventRate) (b : Bool) : ℝ :=
  if b then (e : ℝ) else 1 - (e : ℝ)

def sampleMass (e : EventRate) {n : ℕ} (w : Sample n) : ℝ :=
  ∏ i, bitMass e (w i)

def nullMass {n : ℕ} (w : Sample n) : ℝ :=
  if w = zeroSample n then 1 else 0

def nullError {n : ℕ} (d : Decision n) : ℝ :=
  ∑ w, nullMass w * (d w : ℝ)

def alternativeError (e : EventRate) {n : ℕ} (d : Decision n) : ℝ :=
  ∑ w, sampleMass e w * (1 - (d w : ℝ))

def miss (e : EventRate) (n : ℕ) : ℝ := (1 - (e : ℝ)) ^ n

theorem sample_mass_nonnegative (e : EventRate) {n : ℕ} (w : Sample n) :
    0 ≤ sampleMass e w := by
  unfold sampleMass
  apply Finset.prod_nonneg
  intro i _
  cases h : w i with
  | false => simpa [bitMass, h] using (sub_nonneg.mpr (le_of_lt e.property.2))
  | true => simpa [bitMass, h] using (le_of_lt e.property.1)

theorem sample_mass_normalized (e : EventRate) (n : ℕ) :
    ∑ w : Sample n, sampleMass e w = 1 := by
  unfold sampleMass
  rw [← Fintype.prod_sum]
  simp [Fintype.sum_bool, bitMass]

theorem all_zero_mass (e : EventRate) (n : ℕ) :
    sampleMass e (zeroSample n) = miss e n := by
  simp [sampleMass, zeroSample, bitMass, miss]

theorem miss_positive (e : EventRate) (n : ℕ) : 0 < miss e n :=
  pow_pos (sub_pos.mpr e.property.2) n

theorem miss_le_one (e : EventRate) (n : ℕ) : miss e n ≤ 1 := by
  rw [← sample_mass_normalized e n, ← all_zero_mass e n]
  exact Finset.single_le_sum (fun w _ => sample_mass_nonnegative e w)
    (Finset.mem_univ (zeroSample n))

theorem null_error_at_zero {n : ℕ} (d : Decision n) :
    nullError d = (d (zeroSample n) : ℝ) := by
  classical
  simp [nullError, nullMass]

theorem all_zero_error_contribution (e : EventRate) {n : ℕ} (d : Decision n) :
    miss e n * (1 - nullError d) ≤ alternativeError e d := by
  rw [null_error_at_zero, ← all_zero_mass e n]
  exact Finset.single_le_sum
    (fun w _ => mul_nonneg (sample_mass_nonnegative e w)
      (sub_nonneg.mpr (d w).property.2))
    (Finset.mem_univ (zeroSample n))

theorem sum_error_lower (e : EventRate) {n : ℕ} (d : Decision n) :
    miss e n ≤ nullError d + alternativeError e d := by
  have h := all_zero_error_contribution e d
  have ha : 0 ≤ nullError d := by
    rw [null_error_at_zero]
    exact (d (zeroSample n)).property.1
  have hqa := mul_nonneg (sub_nonneg.mpr (miss_le_one e n)) ha
  nlinarith

theorem worst_error_lower (e : EventRate) {n : ℕ} (d : Decision n) :
    miss e n / (1 + miss e n) ≤ max (nullError d) (alternativeError e d) := by
  have hq := le_of_lt (miss_positive e n)
  have hden : 0 < 1 + miss e n := by positivity
  apply (div_le_iff₀ hden).mpr
  have h := all_zero_error_contribution e d
  have ha := le_max_left (nullError d) (alternativeError e d)
  have hb := le_max_right (nullError d) (alternativeError e d)
  have hmul := mul_le_mul_of_nonneg_left ha hq
  nlinarith

def zeroProbability : Probability := ⟨0, by constructor <;> norm_num⟩
def oneProbability : Probability := ⟨1, by constructor <;> norm_num⟩

def thresholdRule (n : ℕ) (a : Probability) : Decision n :=
  fun w => if w = zeroSample n then a else oneProbability

theorem threshold_rule_errors (e : EventRate) (n : ℕ) (a : Probability) :
    nullError (thresholdRule n a) = (a : ℝ) ∧
    alternativeError e (thresholdRule n a) = miss e n * (1 - (a : ℝ)) := by
  classical
  constructor
  · rw [null_error_at_zero]
    simp [thresholdRule]
  · unfold alternativeError
    rw [Finset.sum_eq_single (zeroSample n)]
    · rw [all_zero_mass]
      simp [thresholdRule]
    · intro w _ hne
      simp [thresholdRule, hne, oneProbability]
    · intro h
      exact (h (Finset.mem_univ (zeroSample n))).elim

def balancedProbability (e : EventRate) (n : ℕ) : Probability :=
  ⟨miss e n / (1 + miss e n), by
    have hq := le_of_lt (miss_positive e n)
    have hden : 0 < 1 + miss e n := by positivity
    constructor
    · exact div_nonneg hq (le_of_lt hden)
    · apply (div_le_iff₀ hden).mpr
      linarith⟩

theorem balanced_rule_errors (e : EventRate) (n : ℕ) :
    nullError (thresholdRule n (balancedProbability e n)) = miss e n / (1 + miss e n) ∧
    alternativeError e (thresholdRule n (balancedProbability e n)) =
      miss e n / (1 + miss e n) := by
  obtain ⟨ha, hb⟩ := threshold_rule_errors e n (balancedProbability e n)
  constructor
  · exact ha
  · rw [hb]
    change miss e n * (1 - miss e n / (1 + miss e n)) =
      miss e n / (1 + miss e n)
    have hq := miss_positive e n
    have hden : 1 + miss e n ≠ 0 := ne_of_gt (by linarith)
    field_simp [hden]
    <;> ring

theorem sharp_sum_error (e : EventRate) (n : ℕ) :
    IsLeast (Set.range (fun d : Decision n => nullError d + alternativeError e d))
      (miss e n) := by
  constructor
  · refine ⟨thresholdRule n zeroProbability, ?_⟩
    obtain ⟨ha, hb⟩ := threshold_rule_errors e n zeroProbability
    dsimp only
    rw [ha, hb]
    simp [zeroProbability]
  · rintro _ ⟨d, rfl⟩
    exact sum_error_lower e d

theorem sharp_worst_error (e : EventRate) (n : ℕ) :
    IsLeast (Set.range (fun d : Decision n => max (nullError d) (alternativeError e d)))
      (miss e n / (1 + miss e n)) := by
  constructor
  · refine ⟨thresholdRule n (balancedProbability e n), ?_⟩
    obtain ⟨ha, hb⟩ := balanced_rule_errors e n
    dsimp only
    rw [ha, hb, max_self]
  · rintro _ ⟨d, rfl⟩
    exact worst_error_lower e d

theorem sharp_equal_prior_error (e : EventRate) (n : ℕ) :
    IsLeast (Set.range (fun d : Decision n => (nullError d + alternativeError e d) / 2))
      (miss e n / 2) := by
  constructor
  · refine ⟨thresholdRule n zeroProbability, ?_⟩
    obtain ⟨ha, hb⟩ := threshold_rule_errors e n zeroProbability
    rw [ha, hb]
    simp [zeroProbability]
  · rintro _ ⟨d, rfl⟩
    have h := sum_error_lower e d
    linarith

theorem no_finite_certain_decision (e : EventRate) {n : ℕ} (d : Decision n) :
    0 < max (nullError d) (alternativeError e d) := by
  have hp : 0 < miss e n / (1 + miss e n) :=
    div_pos (miss_positive e n) (by have hq := miss_positive e n; linarith)
  exact hp.trans_le (worst_error_lower e d)

theorem zero_trials_miss (e : EventRate) : miss e 0 = 1 := by simp [miss]

theorem fixed_rate_arbitrarily_accurate (e : EventRate) (η : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, ∃ d : Decision n, max (nullError d) (alternativeError e d) < η := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη (sub_lt_self 1 e.property.1)
  refine ⟨n, thresholdRule n (balancedProbability e n), ?_⟩
  obtain ⟨ha, hb⟩ := balanced_rule_errors e n
  rw [ha, hb, max_self]
  have hq := miss_positive e n
  have hden : 0 < 1 + miss e n := by linarith
  have hle : miss e n / (1 + miss e n) ≤ miss e n := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (miss e n)]
  exact hle.trans_lt hn

theorem miss_lower_rate_bound (lower e : EventRate) (hle : (lower : ℝ) ≤ e) (n : ℕ) :
    miss e n ≤ miss lower n := by
  unfold miss
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (sub_le_sub_left hle 1)
      (sub_nonneg.mpr (le_of_lt e.property.2))
      (pow_nonneg (sub_nonneg.mpr (le_of_lt lower.property.2)) n)

theorem bernoulli_lower (e : EventRate) (n : ℕ) :
    1 - (n : ℝ) * (e : ℝ) ≤ miss e n := by
  unfold miss
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_right ih
      (sub_nonneg.mpr (le_of_lt e.property.2))
    have hs := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (e : ℝ))
    simp only [Nat.cast_succ]
    nlinarith

theorem no_uniform_finite_guarantee (n : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1 / 2) :
    ∃ e : EventRate, ∀ d : Decision n,
      r < max (nullError d) (alternativeError e d) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < 1 - 2 * r := by linarith
  have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
  let ε : ℝ := (1 - 2 * r) / (2 * ((n : ℝ) + 1))
  have hε0 : 0 < ε := div_pos hd hden
  have hε1 : ε < 1 := by
    dsimp [ε]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  let e : EventRate := ⟨ε, hε0, hε1⟩
  have hne : (n : ℝ) * ε < 1 - 2 * r := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    have hpos := mul_pos hd (show 0 < (n : ℝ) + 2 by positivity)
    nlinarith
  have hq : 2 * r < miss e n := by
    have h := bernoulli_lower e n
    change 1 - (n : ℝ) * ε ≤ miss e n at h
    linarith
  refine ⟨e, ?_⟩
  intro d
  have hq0 := le_of_lt (miss_positive e n)
  have hq1 := miss_le_one e n
  have hdenq : 0 < 1 + miss e n := by positivity
  have hhalf : miss e n / 2 ≤ miss e n / (1 + miss e n) := by
    apply (le_div_iff₀ hdenq).mpr
    have hp := mul_nonneg hq0 (sub_nonneg.mpr hq1)
    nlinarith
  exact (show r < miss e n / 2 by linarith).trans_le
    (hhalf.trans (worst_error_lower e d))

end
end ResearchCommons.Calibration
