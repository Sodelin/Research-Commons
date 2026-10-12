import G4ActualNaturalCombMoments
import G5StrictBoundaryRoutes
import UnifiedLean.Source.SourceEpochSemigroup
import Mathlib.Algebra.Polynomial.Roots

/-!
# Actual original-bank support certificates and cubic calibration

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
This transfers the inherited ALL-CAP D2 certificate-soundness argument and its
one-atom cubic certificate to the checked original COMMON comb observations.
No certificate-existence, RCF execution, unknown-size termination, larger-panel
copy transport, or general G4 closure is assumed or claimed here.
-/
namespace DotG4.ActualObservableBankCertificate
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UnrankedGenealogyObservation
open DotG34.SpecifiedCombEvent
open GProgram.G5.StrictBoundaryRoutes UnifiedLean.Source.SourceEpochSemigroup
open DotG4.ActualBankFirstMeeting DotG4.ActualNaturalCombMoments
open scoped Classical BigOperators ENNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

noncomputable def coinWeight (N : RootedBinary V E X) (p : HybridProbabilities N)
    (coin : Hybrid N → Bool) : ℝ := ((originalRegisterMeasure N p).toPMF coin).toReal

lemma coinWeight_positive (N : RootedBinary V E X) (p : HybridProbabilities N)
    (coin : Hybrid N → Bool) : 0 < coinWeight N p coin := by
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff _ _).mp (strict_original_register_coin N p coin))
    (PMF.apply_ne_top _ _)

lemma coinWeight_sum (N : RootedBinary V E X) (p : HybridProbabilities N) :
    ∑ coin, coinWeight N p coin = 1 :=
  pmf_sum_real _

noncomputable def realSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (coin : Hybrid N → Bool) : ℝ := (bankSurvival N C H p r coin i j).toReal

lemma realSurvival_positive (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (coin : Hybrid N → Bool) : 0 < realSurvival N C H p r i j coin := by
  simp only [realSurvival,bankSurvival,ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact Real.exp_pos _

lemma realSurvival_le_one (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (coin : Hybrid N → Bool) : realSurvival N C H p r i j coin ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using bankSurvival_le_one N C H p r coin i j)

noncomputable def combCoefficient (k : Nat) : ℝ :=
  2^k / ((Nat.factorial (k+1) : ℝ) * (Nat.factorial k : ℝ))

lemma combCoefficient_positive (k : Nat) : 0 < combCoefficient k := by
  unfold combCoefficient
  positivity

noncomputable def combProbability (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (k : Nat) : ℝ :=
  (naturalCompletedUnrankedLaw N C (repeatedSample k i j) H p (fun _ => true) r
    {toUnranked (comb (Sum.inr ()) (canonicalA k))}).toReal

/-- A normalized actual passive topology probability; the denominator is the
proved positive specified-comb coefficient. -/
noncomputable def observedMoment (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (k : Nat) : ℝ :=
  combProbability N C H p r i j k / combCoefficient k

lemma actual_observed_moment (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (k : Nat) (hk : 0 < k) :
    observedMoment N C H p r i j k =
      ∑ coin, coinWeight N p coin * realSurvival N C H p r i j coin ^ k.choose 2 := by
  unfold observedMoment combProbability
  apply (div_eq_iff (combCoefficient_positive k).ne').mpr
  rw [actual_natural_completed_comb_finite_moment N C H p r i j k hk,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (combCoefficient_positive k).le,
    ENNReal.toReal_sum (fun coin _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ENNReal.pow_ne_top (by simp [bankSurvival])))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,coinWeight,realSurvival]
  ring

noncomputable def sparsePolynomial (levels : Finset Nat) (c : Nat → ℝ) : Polynomial ℝ :=
  ∑ k ∈ levels, Polynomial.monomial (k.choose 2) (c k)

lemma sparsePolynomial_eval (levels : Finset Nat) (c : Nat → ℝ) (x : ℝ) :
    (sparsePolynomial levels c).eval x = ∑ k ∈ levels, c k * x^(k.choose 2) := by
  simp [sparsePolynomial,Polynomial.eval_finset_sum]

/-- Soundness of an observed sparse certificate for EVERY original natural
bank, without a support-size bound or a changed cut posterior. -/
theorem actual_observable_certificate_zero (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (levels : Finset Nat) (c : Nat → ℝ)
    (hlevels : ∀ k ∈ levels, 0 < k)
    (hnonneg : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ (sparsePolynomial levels c).eval x)
    (hobs : ∑ k ∈ levels, c k * observedMoment N C H p r i j k = 0)
    (coin : Hybrid N → Bool) :
    (sparsePolynomial levels c).eval (realSurvival N C H p r i j coin) = 0 := by
  let w := coinWeight N p
  let x := realSurvival N C H p r i j
  have hn : ∀ a, 0 ≤ w a * (sparsePolynomial levels c).eval (x a) := by
    intro a
    exact mul_nonneg (coinWeight_positive N p a).le
      (hnonneg _ ⟨(realSurvival_positive N C H p r i j a).le,realSurvival_le_one N C H p r i j a⟩)
  have hz : ∑ a, w a * (sparsePolynomial levels c).eval (x a) = 0 := by
    calc
      _ = ∑ k ∈ levels, c k * (∑ a, w a * x a ^ k.choose 2) := by
        simp only [sparsePolynomial_eval,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = ∑ k ∈ levels, c k * observedMoment N C H p r i j k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [actual_observed_moment N C H p r i j k (hlevels k hk)]
      _ = 0 := hobs
  have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hn a)).mp hz coin (Finset.mem_univ coin)
  exact (mul_eq_zero.mp ha).resolve_left (coinWeight_positive N p coin).ne'

/-- A nonzero observed certificate gives a finite real root grid.
Existence or computable discovery of the certificate is a separate obligation. -/
theorem actual_observable_certificate_roots (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (levels : Finset Nat) (c : Nat → ℝ)
    (hlevels : ∀ k ∈ levels, 0 < k) (hne : sparsePolynomial levels c ≠ 0)
    (hnonneg : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ (sparsePolynomial levels c).eval x)
    (hobs : ∑ k ∈ levels, c k * observedMoment N C H p r i j k = 0)
    (coin : Hybrid N → Bool) :
    realSurvival N C H p r i j coin ∈ (sparsePolynomial levels c).roots.toFinset := by
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hne).mpr
  exact actual_observable_certificate_zero N C H p r i j levels c hlevels hnonneg hobs coin

/-- The inherited one-atom sparse certificate uses exactly levels 1, 2, 3. -/
def cubicCoefficients (a : ℝ) (k : Nat) : ℝ :=
  if k = 1 then 2*a^3 else if k = 2 then -3*a^2 else 1

lemma cubic_certificate_eval (a x : ℝ) :
    (sparsePolynomial {1,2,3} (cubicCoefficients a)).eval x = (x-a)^2*(x+2*a) := by
  norm_num [sparsePolynomial_eval,cubicCoefficients,Nat.choose]
  ring

/-- Concrete original-bank rigidity from the two calibrated ACTUAL normalized
comb observations. Every original mask is forced, not merely a supplied arm pair.
The reference survival may equal one; no strict exposure assumption is used. -/
theorem actual_two_calibration_bank_rigidity (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (a : ℝ) (ha : 0 ≤ a)
    (h2 : observedMoment N C H p r i j 2 = a)
    (h3 : observedMoment N C H p r i j 3 = a^3)
    (coin : Hybrid N → Bool) : realSurvival N C H p r i j coin = a := by
  have h1 : observedMoment N C H p r i j 1 = 1 := by
    rw [actual_observed_moment N C H p r i j 1 (by decide)]
    simpa using coinWeight_sum N p
  have hlevels : ∀ k ∈ ({1,2,3} : Finset Nat), 0 < k := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> decide
  have hnonneg : ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 ≤ (sparsePolynomial {1,2,3} (cubicCoefficients a)).eval x := by
    intro x hx
    rw [cubic_certificate_eval]
    exact mul_nonneg (sq_nonneg _) (by linarith [hx.1])
  have hobs : ∑ k ∈ ({1,2,3} : Finset Nat), cubicCoefficients a k *
      observedMoment N C H p r i j k = 0 := by
    norm_num [cubicCoefficients,h1,h2,h3]
    ring
  have hz := actual_observable_certificate_zero N C H p r i j {1,2,3}
    (cubicCoefficients a) hlevels hnonneg hobs coin
  rw [cubic_certificate_eval] at hz
  have hp : 0 < realSurvival N C H p r i j coin + 2*a := by
    linarith [realSurvival_positive N C H p r i j coin]
  have hs := (mul_eq_zero.mp hz).resolve_right hp.ne'
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

/-- The literal calibrated three-/four-copy probability equality from the
inherited paired natural-tree certificate. The conclusion holds for every
original bank, including those not exposed to the observer. -/
theorem actual_cubic_observation_forces_constant (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X)
    (hcal : 18 * combProbability N C H p r i j 3 =
      (3 * combProbability N C H p r i j 2)^3)
    (coin : Hybrid N → Bool) :
    realSurvival N C H p r i j coin = 3 * combProbability N C H p r i j 2 := by
  have h2 : observedMoment N C H p r i j 2 = 3 * combProbability N C H p r i j 2 := by
    norm_num [observedMoment,combCoefficient]
    ring
  have h3 : observedMoment N C H p r i j 3 = 18 * combProbability N C H p r i j 3 := by
    norm_num [observedMoment,combCoefficient]
    ring
  apply actual_two_calibration_bank_rigidity N C H p r i j _ _ h2 (h3.trans hcal) coin
  exact mul_nonneg (by norm_num) ENNReal.toReal_nonneg

/-- Exact two-moment calibration is equivalent to constant survival in every
original bank. This is the inherited paired natural-tree calibration premise. -/
theorem actual_cubic_observation_iff_constant (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) :
    (18 * combProbability N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3) ↔
    (∀ coin, realSurvival N C H p r i j coin = 3 * combProbability N C H p r i j 2) := by
  constructor
  · intro h coin
    exact actual_cubic_observation_forces_constant N C H p r i j h coin
  · intro h
    have hm : observedMoment N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3 := by
      rw [actual_observed_moment N C H p r i j 3 (by decide)]
      norm_num [Nat.choose]
      simp_rw [h]
      rw [← Finset.sum_mul,coinWeight_sum,one_mul]
    have h3 : observedMoment N C H p r i j 3 = 18 * combProbability N C H p r i j 3 := by
      norm_num [observedMoment,combCoefficient]
      ring
    exact h3.symm.trans hm

#print axioms actual_cubic_observation_iff_constant
#print axioms actual_cubic_observation_forces_constant
#print axioms actual_observable_certificate_roots
#print axioms actual_two_calibration_bank_rigidity
end DotG4.ActualObservableBankCertificate
