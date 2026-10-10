import UnifiedLean.G6.ProgramPrefix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
UNCHECKED explicit-Copy derivative of the original-source rate-bank draft.
CLOUD-G6-SOL-ULTRA-20261007, 2026-10-07.
Original cb793c6f is preserved unchanged; only implicit Copy arguments are anchored.
Compares holding AND each actual ordered merger choice at rho/2, maps through
one original destination, then iterates the same admitted Code kernel.
Original providers and running compiler inputs are unchanged. No executable
correspondence, boundary comparison, timed-bin reader or master is claimed.
-/
namespace UnifiedLean.G6.RateBankCommon
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.ProgramPrefix
open scoped Classical BigOperators ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def copyBound : ℝ := 1 + (Fintype.card Copy : ℝ)^2

noncomputable def populationPairCount (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E) : ℝ :=
  ((populationRoots (state s) (originalPlace N i)).offDiag.card : ℝ)

lemma copyBound_positive : 0 < copyBound (Copy := Copy) := by
  unfold copyBound
  positivity

lemma populationPairCount_le (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E) :
    populationPairCount N s i ≤ (Fintype.card Copy : ℝ)^2 := by
  have hc := Finset.card_le_univ
    (populationRoots (state s) (originalPlace N i)).offDiag
  have hr : (((populationRoots (state s) (originalPlace N i)).offDiag.card : ℝ)) ≤
      (Fintype.card (Copy × Copy) : ℝ) := by exact_mod_cast hc
  simpa only [populationPairCount, Fintype.card_prod, Nat.cast_mul, pow_two] using hr

lemma holding_coefficient_nonnegative (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E) :
    0 ≤ copyBound (Copy := Copy) - populationPairCount N s i / 2 := by
  have hc := populationPairCount_le N s i
  unfold copyBound
  nlinarith [sq_nonneg (Fintype.card Copy : ℝ)]

lemma totalRate_population_sum (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    totalRate N r s = ∑ i : Option E, populationPairCount N s i * pairRate r i / 2 := by
  unfold totalRate choiceRate
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ _ : (populationRoots (state s) (originalPlace N i)).offDiag,
    pairRate r i / 2) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  unfold populationPairCount
  ring

noncomputable def holdingNumerator (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) : ℝ :=
  copyBound (Copy := Copy) + ∑ i : Option E,
    (copyBound (Copy := Copy) - populationPairCount N s i / 2) * pairRate r i

lemma holdingNumerator_eq (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    holdingNumerator N r s = globalRateBound (Copy := Copy) r - totalRate N r s := by
  rw [totalRate_population_sum]
  unfold holdingNumerator globalRateBound
  simp_rw [sub_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold copyBound
  ring

lemma holdingNumerator_nonnegative (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    0 ≤ holdingNumerator N r s := by
  unfold holdingNumerator
  exact add_nonneg (copyBound_positive (Copy := Copy)).le (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (holding_coefficient_nonnegative N s i) (pairRate_pos r i).le))

lemma holding_choice_formula (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    choiceMass N r s none = holdingNumerator N r s / globalRateBound (Copy := Copy) r := by
  rw [holdingNumerator_eq]
  unfold choiceMass
  field_simp [ne_of_gt (globalRateBound_positive (Copy := Copy) r)]

lemma globalRateBound_bank_lower (r rhat : PositivePairRates E)
    (ell : ℝ) (hell1 : ell ≤ 1)
    (hbank : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i) :
    ell * globalRateBound (Copy := Copy) r ≤ globalRateBound (Copy := Copy) rhat := by
  have hsum : ell * (∑ i : Option E, pairRate r i) ≤
      ∑ i : Option E, pairRate rhat i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hbank i)
  have hadd : ell * (1 + ∑ i : Option E, pairRate r i) ≤
      1 + ∑ i : Option E, pairRate rhat i := by nlinarith
  unfold globalRateBound
  simpa only [copyBound, mul_assoc] using mul_le_mul_of_nonneg_right hadd (copyBound_positive (Copy := Copy)).le

lemma globalRateBound_bank_upper (r rhat : PositivePairRates E)
    (u : ℝ) (hu1 : 1 ≤ u)
    (hbank : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i) :
    globalRateBound (Copy := Copy) rhat ≤ u * globalRateBound (Copy := Copy) r := by
  have hsum : (∑ i : Option E, pairRate rhat i) ≤
      u * ∑ i : Option E, pairRate r i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hbank i)
  have hadd : (1 + ∑ i : Option E, pairRate rhat i) ≤
      u * (1 + ∑ i : Option E, pairRate r i) := by nlinarith
  unfold globalRateBound
  simpa only [copyBound, mul_assoc] using mul_le_mul_of_nonneg_right hadd (copyBound_positive (Copy := Copy)).le

lemma holdingNumerator_bank_lower (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (ell : ℝ) (hell1 : ell ≤ 1)
    (hbank : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i) :
    ell * holdingNumerator N r s ≤ holdingNumerator N rhat s := by
  have hsum : ell * (∑ i : Option E,
      (copyBound (Copy := Copy) - populationPairCount N s i / 2) * pairRate r i) ≤
      ∑ i : Option E,
      (copyBound (Copy := Copy) - populationPairCount N s i / 2) * pairRate rhat i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hc := holding_coefficient_nonnegative N s i
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hbank i) hc
  have hm : ell * copyBound (Copy := Copy) ≤ copyBound (Copy := Copy) := by
    simpa using mul_le_mul_of_nonneg_right hell1 (copyBound_positive (Copy := Copy)).le
  unfold holdingNumerator
  nlinarith

lemma ratio_bank_lower (x xhat g ghat ell u : ℝ)
    (hx : 0 ≤ x) (hg : 0 < g) (hghat : 0 < ghat)
    (hell : 0 ≤ ell) (hu : 0 < u)
    (hnum : ell * x ≤ xhat) (hden : ghat ≤ u * g) :
    (ell / u) * (x / g) ≤ xhat / ghat := by
  have hid : (ell / u) * (x / g) = (ell * x) / (u * g) := by
    field_simp
  rw [hid]
  apply (div_le_div_iff₀ (mul_pos hu hg) hghat).mpr
  exact (mul_le_mul_of_nonneg_left hden (mul_nonneg hell hx)).trans
    (mul_le_mul_of_nonneg_right hnum (mul_pos hu hg).le)

/-- BOTH original hold and original ordered-pair merger are compared.
The Choice carrier and merger destination do not depend on the rate bank. -/
theorem actual_choice_mass_bank_lower (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (p : Option (Choice N s)) :
    (ell / u) * choiceMass N r s p ≤ choiceMass N rhat s p := by
  have hu : 0 < u := lt_of_lt_of_le (by norm_num) hu1
  have hG := globalRateBound_positive (Copy := Copy) r
  have hGh := globalRateBound_positive (Copy := Copy) rhat
  have hden := globalRateBound_bank_upper (Copy := Copy) r rhat u hu1 hup
  cases p with
  | none =>
    rw [holding_choice_formula, holding_choice_formula]
    exact ratio_bank_lower _ _ _ _ _ _ (holdingNumerator_nonnegative N r s) hG hGh
      hell hu (holdingNumerator_bank_lower N r rhat s ell hell1 hlo) hden
  | some p =>
    change (ell / u) * (choiceRate N r s p / globalRateBound (Copy := Copy) r) ≤
      choiceRate N rhat s p / globalRateBound (Copy := Copy) rhat
    have hnum : ell * choiceRate N r s p ≤ choiceRate N rhat s p := by
      unfold choiceRate
      have h := div_le_div_of_nonneg_right (hlo p.1) (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_div_assoc] using h
    exact ratio_bank_lower _ _ _ _ _ _
      (div_nonneg (pairRate_pos r p.1).le (by norm_num)) hG hGh hell hu hnum hden

theorem actual_choice_pmf_bank_lower (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (p : Option (Choice N s)) :
    ENNReal.ofReal (ell / u) * choicePMF N r s p ≤ choicePMF N rhat s p := by
  change ENNReal.ofReal (ell / u) * ENNReal.ofReal (choiceMass N r s p) ≤
    ENNReal.ofReal (choiceMass N rhat s p)
  rw [← ENNReal.ofReal_mul (div_nonneg hell (lt_of_lt_of_le (by norm_num) hu1).le)]
  exact ENNReal.ofReal_le_ofReal (actual_choice_mass_bank_lower N r rhat s ell u
    hell hell1 hu1 hlo hup p)

theorem actual_source_step_bank_lower (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s d : Code N sample)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i) :
    ENNReal.ofReal (ell / u) * sourceStep N r s d ≤ sourceStep N rhat s d := by
  unfold sourceStep
  exact map_scaled_domination _ _ _
    (actual_choice_pmf_bank_lower N r rhat s ell u hell hell1 hu1 hlo hup)
    (stepDestination N s) d

theorem actual_source_iteration_bank_lower (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (k : ℕ) (s d : Code N sample)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i) :
    (ENNReal.ofReal (ell / u)) ^ k * sourceIteration N r k s d ≤
      sourceIteration N rhat k s d := by
  induction k generalizing s d with
  | zero => simp only [pow_zero, one_mul, sourceIteration, le_refl]
  | succ k ih =>
    rw [sourceIteration, sourceIteration, pow_succ]
    rw [mul_comm ((ENNReal.ofReal (ell / u)) ^ k) (ENNReal.ofReal (ell / u))]
    apply bind_scaled_domination _ _ _ _ _ _
      (fun a => actual_source_step_bank_lower N r rhat s a ell u hell hell1 hu1 hlo hup)
    intro a b
    exact ih a b

theorem actual_source_iteration_bank_lower_real (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (k : ℕ) (s d : Code N sample)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i) :
    (ell / u)^k * (sourceIteration N r k s d).toReal ≤
      (sourceIteration N rhat k s d).toReal := by
  have h := ENNReal.toReal_mono (PMF.apply_ne_top (sourceIteration N rhat k s) d)
    (actual_source_iteration_bank_lower N r rhat k s d ell u hell hell1 hu1 hlo hup)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (div_nonneg hell (lt_of_lt_of_le (by norm_num) hu1).le)] using h

#print axioms copyBound_positive
#print axioms populationPairCount_le
#print axioms holding_coefficient_nonnegative
#print axioms totalRate_population_sum
#print axioms holdingNumerator_eq
#print axioms holdingNumerator_nonnegative
#print axioms holding_choice_formula
#print axioms globalRateBound_bank_lower
#print axioms globalRateBound_bank_upper
#print axioms holdingNumerator_bank_lower
#print axioms ratio_bank_lower
#print axioms actual_choice_mass_bank_lower
#print axioms actual_choice_pmf_bank_lower
#print axioms actual_source_step_bank_lower
#print axioms actual_source_iteration_bank_lower
#print axioms actual_source_iteration_bank_lower_real

end UnifiedLean.G6.RateBankCommon
