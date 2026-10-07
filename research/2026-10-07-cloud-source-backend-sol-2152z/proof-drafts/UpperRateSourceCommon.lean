import UnifiedLean.G6.UpperMeanCommon
import UnifiedLean.G6.ResidualProgram
import UnifiedLean.G6.RateBankCommon
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
UNCHECKED additive actual-interval adapter, CLOUD-SOURCE-BACKEND-SOL-2152Z.
The future RateBankCommon import is pinned to RateBankCommonExplicitCopy
SHA256 0dfa158e84acd89f11177ef960c876a3ffb3bf118732be157b1293670cddb1e0.
UpperMeanCommon is pinned to 03bfc2b5; ResidualProgram to 76301709.
All new bodies are UNCHECKED and outside the current 155-module job frozen
at fb62f2e. No compiler, shared provider or workflow is changed.

The count reference has actual mean a, the numerical prefix has upper mean b,
and both source iterations use the original admitted Code/destination. The
actual rate-bank theorem compares holding and every ordered merger at rho/2.
Only counts k <= K use the alpha^K iteration comparison. Beyond K, the count
reference is zero. Residual mass goes to the SAME entering point mass.
No desired numerical/source-law premise, executable correspondence, physical
timed readout, inheritance composition or full-program claim is supplied.
-/

namespace UnifiedLean.G6.UpperRateSourceCommon
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.SourcePrefix
open UnifiedLean.G6.ResidualPrefix UnifiedLean.G6.ResidualProgram
open UnifiedLean.G6.UpperMeanCommon UnifiedLean.G6.RateBankCommon
open UnifiedLean.G6.ProgramPrefix
open scoped Classical BigOperators NNReal ENNReal

lemma rateRatio_nonnegative (ell u : ℝ) (hell : 0 ≤ ell) (hu1 : 1 ≤ u) :
    0 ≤ ell / u :=
  div_nonneg hell (le_trans (by norm_num : (0 : ℝ) ≤ 1) hu1)

lemma rateRatio_le_one (ell u : ℝ) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u) :
    ell / u ≤ 1 := by
  exact (div_le_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hu1)).mpr
    (hell1.trans hu1)

lemma rateRatioENN_le_one (ell u : ℝ) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u) :
    ENNReal.ofReal (ell / u) ≤ 1 := by
  calc
    ENNReal.ofReal (ell / u) ≤ ENNReal.ofReal 1 :=
      ENNReal.ofReal_le_ofReal (rateRatio_le_one ell u hell1 hu1)
    _ = 1 := by simp

lemma prefixCount_eq_zero_of_gt (a : ℝ≥0) (K k : ℕ) (hk : ¬ k ≤ K) :
    prefixCount a K k = 0 := by
  have hmem : k ∉ (Finset.range (K + 1) : Set ℕ) := by
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hk
  change ((countPMF a).filter (Finset.range (K + 1) : Set ℕ)
    (prefix_has_support a K)) k = 0
  exact PMF.filter_apply_eq_zero_of_notMem (prefix_has_support a K) hmem

lemma upperCount_mass_domination (a b : ℝ≥0) (hab : a ≤ b) (K k : ℕ) :
    ENNReal.ofReal (upperCommonMass a b K) * prefixCount a K k ≤
      ENNReal.ofReal (residualMass (b : ℝ) K) * prefixCount b K k := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((prefixCount a K).apply_ne_top k))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((prefixCount b K).apply_ne_top k))).mp
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (upperCommonMass_bounds a b hab K).1.le,
    ENNReal.toReal_ofReal (residualMass_bounds b K).1] using
    upperCommonMass_count_domination a b hab K k

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Upper-mean finite source law at ONE shared comparison bank, with residual
sent to the same entering state. This is a mathematical PMF, not an evaluator. -/
noncomputable def upperRateResidualSource (N : RootedBinary V E X)
    {sample : Copy → X} (rhat : PositivePairRates E) (b : ℝ≥0) (K : ℕ)
    (s : Code N sample) : PMF (Code N sample) :=
  residualPMF ((prefixCount b K).bind (fun k => sourceIteration N rhat k s))
    (PMF.pure s) (residualMass (b : ℝ) K)
    (residualMass_bounds b K).1 (residualMass_bounds b K).2

/-- Rate domination is used only on the supported count prefix. Both bank
bounds are on the actual original arc/root rates, rather than a fitted row. -/
theorem upper_rate_prefix_domination (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (a b : ℝ≥0)
    (hab : a ≤ b) (K : ℕ) (s d : Code N sample)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i) :
    (ENNReal.ofReal (upperCommonMass a b K) * (ENNReal.ofReal (ell / u)) ^ K) *
      ((prefixCount a K).bind (fun k => sourceIteration N r k s)) d ≤
      ENNReal.ofReal (residualMass (b : ℝ) K) *
        ((prefixCount b K).bind (fun k => sourceIteration N rhat k s)) d := by
  rw [PMF.bind_apply, PMF.bind_apply,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k ≤ K
  · have hpow : (ENNReal.ofReal (ell / u)) ^ K ≤
        (ENNReal.ofReal (ell / u)) ^ k :=
      pow_le_pow_right_of_le_one' (rateRatioENN_le_one ell u hell1 hu1) hk
    have hiter : (ENNReal.ofReal (ell / u)) ^ K * sourceIteration N r k s d ≤
        sourceIteration N rhat k s d :=
      (mul_le_mul_right' hpow _).trans
        (actual_source_iteration_bank_lower N r rhat k s d ell u
          hell hell1 hu1 hlo hup)
    calc
      (ENNReal.ofReal (upperCommonMass a b K) * (ENNReal.ofReal (ell / u)) ^ K) *
          (prefixCount a K k * sourceIteration N r k s d) =
          (ENNReal.ofReal (upperCommonMass a b K) * prefixCount a K k) *
            ((ENNReal.ofReal (ell / u)) ^ K * sourceIteration N r k s d) := by ac_rfl
      _ ≤ (ENNReal.ofReal (residualMass (b : ℝ) K) * prefixCount b K k) *
          sourceIteration N rhat k s d :=
        mul_le_mul' (upperCount_mass_domination a b hab K k) hiter
      _ = ENNReal.ofReal (residualMass (b : ℝ) K) *
          (prefixCount b K k * sourceIteration N rhat k s d) := by ac_rfl
  · rw [prefixCount_eq_zero_of_gt a K k hk]
    simp only [zero_mul, mul_zero, zero_le]

theorem numerical_interval_common_domination (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (t b : ℝ≥0)
    (hab : globalClockRate (Copy := Copy) r * t ≤ b) (K : ℕ) (s d : Code N sample)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i) :
    (ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
        (ENNReal.ofReal (ell / u)) ^ K) * finiteSourcePrefix N r t K s d ≤
      upperRateResidualSource N rhat b K s d := by
  exact (upper_rate_prefix_domination N r rhat _ b hab K s d ell u
    hell hell1 hu1 hlo hup).trans
    (residualPMF_domination
      ((prefixCount b K).bind (fun k => sourceIteration N rhat k s))
      (PMF.pure s) (residualMass (b : ℝ) K)
      (residualMass_bounds b K).1 (residualMass_bounds b K).2 d)

/-- The ACTUAL interval has the same common reference and common factor. -/
theorem actual_interval_common_domination (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t b : ℝ≥0)
    (hab : globalClockRate (Copy := Copy) r * t ≤ b) (K : ℕ) (s d : Code N sample)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2)
    (ell u : ℝ) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u) :
    (ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
        (ENNReal.ofReal (ell / u)) ^ K) * finiteSourcePrefix N r t K s d ≤
      sourceTimeKernel N r t s d := by
  have hcount := upperCommonMass_le_prefixMass
    (globalClockRate (Copy := Copy) r * t) b hab K hK
  have hc := (upperCommonMass_bounds
    (globalClockRate (Copy := Copy) r * t) b hab K).1.le
  have hactual : ENNReal.ofReal
      (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
      finiteSourcePrefix N r t K s d ≤ sourceTimeKernel N r t s d := by
    apply ofReal_scaled_domination _ _ _ hc
    intro z
    exact (mul_le_mul_of_nonneg_right hcount ENNReal.toReal_nonneg).trans
      (actual_source_prefix_domination N r t K s z)
  have hpow : (ENNReal.ofReal (ell / u)) ^ K ≤ 1 :=
    pow_le_one_of_le (rateRatioENN_le_one ell u hell1 hu1) K
  calc
    (ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
        (ENNReal.ofReal (ell / u)) ^ K) * finiteSourcePrefix N r t K s d =
        (ENNReal.ofReal (ell / u)) ^ K *
          (ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
            finiteSourcePrefix N r t K s d) := by ac_rfl
    _ ≤ 1 * (ENNReal.ofReal
        (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
        finiteSourcePrefix N r t K s d) := mul_le_mul_right' hpow _
    _ = ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
        finiteSourcePrefix N r t K s d := one_mul _
    _ ≤ sourceTimeKernel N r t s d := hactual

theorem actual_upper_rate_interval_tv (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (t b : ℝ≥0)
    (hab : globalClockRate (Copy := Copy) r * t ≤ b) (K : ℕ) (s : Code N sample)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i) :
    pmfTV (sourceTimeKernel N r t s) (upperRateResidualSource N rhat b K s) ≤
      1 - upperCommonMass (globalClockRate (Copy := Copy) r * t) b K * (ell / u) ^ K := by
  have h := common_pmf_tv (sourceTimeKernel N r t s)
    (upperRateResidualSource N rhat b K s) (finiteSourcePrefix N r t K s)
    (ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
      (ENNReal.ofReal (ell / u)) ^ K)
    (fun d => actual_interval_common_domination N r t b hab K s d hK ell u hell1 hu1)
    (fun d => numerical_interval_common_domination N r rhat t b hab K s d ell u
      hell hell1 hu1 hlo hup)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (upperCommonMass_bounds
      (globalClockRate (Copy := Copy) r * t) b hab K).1.le,
    ENNReal.toReal_ofReal (rateRatio_nonnegative ell u hell hu1)] using h

/-- ONE finite joint readout of the same source endpoint; its coordinates
need not be independent. No physical timed-bin readout equality is assumed. -/
theorem actual_upper_rate_joint_readout_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r rhat : PositivePairRates E) (t b : ℝ≥0)
    (hab : globalClockRate (Copy := Copy) r * t ≤ b) (K : ℕ) (s : Code N sample)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2)
    (ell u : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (readout : Code N sample → O) :
    pmfTV ((sourceTimeKernel N r t s).map readout)
      ((upperRateResidualSource N rhat b K s).map readout) ≤
      1 - upperCommonMass (globalClockRate (Copy := Copy) r * t) b K * (ell / u) ^ K := by
  have h := common_pmf_tv ((sourceTimeKernel N r t s).map readout)
    ((upperRateResidualSource N rhat b K s).map readout)
    ((finiteSourcePrefix N r t K s).map readout)
    (ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
      (ENNReal.ofReal (ell / u)) ^ K)
    (fun o => map_scaled_domination _ _ _
      (fun d => actual_interval_common_domination N r t b hab K s d hK ell u hell1 hu1)
      readout o)
    (fun o => map_scaled_domination _ _ _
      (fun d => numerical_interval_common_domination N r rhat t b hab K s d ell u
        hell hell1 hu1 hlo hup) readout o)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (upperCommonMass_bounds
      (globalClockRate (Copy := Copy) r * t) b hab K).1.le,
    ENNReal.toReal_ofReal (rateRatio_nonnegative ell u hell hu1)] using h

#print axioms rateRatio_nonnegative
#print axioms rateRatio_le_one
#print axioms rateRatioENN_le_one
#print axioms prefixCount_eq_zero_of_gt
#print axioms upperCount_mass_domination
#print axioms upperRateResidualSource
#print axioms upper_rate_prefix_domination
#print axioms numerical_interval_common_domination
#print axioms actual_interval_common_domination
#print axioms actual_upper_rate_interval_tv
#print axioms actual_upper_rate_joint_readout_tv

end UnifiedLean.G6.UpperRateSourceCommon
