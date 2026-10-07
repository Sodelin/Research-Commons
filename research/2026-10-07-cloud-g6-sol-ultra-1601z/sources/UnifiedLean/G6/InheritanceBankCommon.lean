import UnifiedLean.G6.ProgramPrefix
import UnifiedLean.Source.SourceNaturalInitialization
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
UNCHECKED pinned-API derivative of the source-connected inheritance draft.
CLOUD-G6-SOL-ULTRA-20261007, 2026-10-07.
Original c7dc9a75 and namespace derivative 009e8434 are preserved unchanged.
Retain the Hybrid namespace; replace one unavailable multiplication lemma only.
Actual once-drawn ALL-original-hybrid register versus CURRENT AtNode coins.
No COMMON redraw, selected-tip substitution, normalization or hidden oracle.
No compiler, executable numeric backend or full G6 claim.
-/
namespace UnifiedLean.G6.InheritanceBankCommon
open Nanuq.Source GProgram.SourceForest MeasureTheory ProbabilityTheory
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.G6.ProgramPrefix
open scoped Classical BigOperators ENNReal

lemma actual_bit_singleton (gamma : unitInterval) (b : Bool) :
    bitMeasure gamma {b} =
      if b then ENNReal.ofReal (gamma : ℝ) else ENNReal.ofReal (1 - (gamma : ℝ)) := by
  unfold bitMeasure
  rw [bernoulliMeasure_apply gamma (measurableSet_singleton b)]
  cases b <;> simp [ENNReal.ofReal_eq_coe_nnreal, unitInterval.toNNReal,
    unitInterval.coe_symm_eq, gamma.property.1, sub_nonneg.mpr gamma.property.2] <;> rfl

lemma actual_bit_bank_lower (gamma gammahat : unitInterval) (beta : ℝ)
    (hbeta : 0 ≤ beta) (htrue : beta * (gamma : ℝ) ≤ (gammahat : ℝ))
    (hfalse : beta * (1 - (gamma : ℝ)) ≤ 1 - (gammahat : ℝ)) (b : Bool) :
    ENNReal.ofReal beta * bitMeasure gamma {b} ≤ bitMeasure gammahat {b} := by
  rw [actual_bit_singleton, actual_bit_singleton]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
  · rw [← ENNReal.ofReal_mul hbeta]
    exact ENNReal.ofReal_le_ofReal hfalse
  · rw [← ENNReal.ofReal_mul hbeta]
    exact ENNReal.ofReal_le_ofReal htrue

lemma actual_current_coin_product (Site : Type*) [Fintype Site]
    (gamma : unitInterval) (coin : Site → Bool) :
    currentCoinPMF Site gamma coin = ∏ i : Site, bitMeasure gamma {coin i} := by
  unfold currentCoinPMF
  rw [Measure.toPMF_apply]
  unfold independentCoinMeasure
  rw [Measure.pi_singleton]

/-- Pointwise product on the actual Site carrier, including the empty carrier. -/
theorem actual_current_coin_bank_lower (Site : Type*) [Fintype Site]
    (gamma gammahat : unitInterval) (beta : ℝ) (hbeta : 0 ≤ beta)
    (htrue : beta * (gamma : ℝ) ≤ (gammahat : ℝ))
    (hfalse : beta * (1 - (gamma : ℝ)) ≤ 1 - (gammahat : ℝ))
    (coin : Site → Bool) :
    (ENNReal.ofReal beta) ^ Fintype.card Site * currentCoinPMF Site gamma coin ≤
      currentCoinPMF Site gammahat coin := by
  rw [actual_current_coin_product, actual_current_coin_product]
  have h := Finset.prod_le_prod' (fun (i : Site) (_ : i ∈ Finset.univ) =>
    actual_bit_bank_lower gamma gammahat beta hbeta htrue hfalse (coin i))
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_current_owner_count (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : V) :
    Fintype.card (AtNode (state s) v) ≤ Fintype.card Copy := by
  exact Fintype.card_le_of_injective (fun a : AtNode (state s) v => a.val)
    Subtype.val_injective

/-- Each active original root reads a fresh coin at THIS actual boundary. -/
theorem actual_independent_pulse_bank_lower (N : RootedBinary V E X)
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N)
    (s d : Code N sample) (gamma gammahat : unitInterval) (beta : ℝ)
    (hbeta : 0 ≤ beta) (htrue : beta * (gamma : ℝ) ≤ (gammahat : ℝ))
    (hfalse : beta * (1 - (gamma : ℝ)) ≤ 1 - (gammahat : ℝ)) :
    (ENNReal.ofReal beta) ^ Fintype.card (AtNode (state s) H.hybrid) *
      independentPulseKernel H gamma s d ≤ independentPulseKernel H gammahat s d := by
  unfold independentPulseKernel
  exact map_scaled_domination _ _ _
    (actual_current_coin_bank_lower (AtNode (state s) H.hybrid)
      gamma gammahat beta hbeta htrue hfalse) (pulseCode H s) d

/-- Uniform over every full entering Code. No original tip is re-coined. -/
theorem actual_independent_pulse_bank_lower_uniform (N : RootedBinary V E X)
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N)
    (s d : Code N sample) (gamma gammahat : unitInterval) (beta : ℝ)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htrue : beta * (gamma : ℝ) ≤ (gammahat : ℝ))
    (hfalse : beta * (1 - (gamma : ℝ)) ≤ 1 - (gammahat : ℝ)) :
    (ENNReal.ofReal beta) ^ Fintype.card Copy * independentPulseKernel H gamma s d ≤
      independentPulseKernel H gammahat s d := by
  have hmu : ENNReal.ofReal beta ≤ 1 := by
    calc
      ENNReal.ofReal beta ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hbeta1
      _ = 1 := by simp
  have hpow : (ENNReal.ofReal beta) ^ Fintype.card Copy ≤
      (ENNReal.ofReal beta) ^ Fintype.card (AtNode (state s) H.hybrid) :=
    pow_le_pow_right_of_le_one' hmu (actual_current_owner_count N s H.hybrid)
  exact (mul_le_mul' hpow le_rfl).trans
    (actual_independent_pulse_bank_lower N H s d gamma gammahat beta hbeta htrue hfalse)

lemma actual_original_register_product (N : RootedBinary V E X)
    (p : HybridProbabilities N) (coin : Hybrid N → Bool) :
    (originalRegisterMeasure N p).toPMF coin =
      ∏ h : Hybrid N, bitMeasure (originalGamma p h) {coin h} := by
  rw [Measure.toPMF_apply]
  unfold originalRegisterMeasure
  rw [Measure.pi_singleton]

/-- The product is over ALL original hybrids, including unused latent slots. -/
theorem actual_original_register_coin_bank_lower (N : RootedBinary V E X)
    (p phat : HybridProbabilities N) (beta : Hybrid N → ℝ)
    (hbeta : ∀ h, 0 ≤ beta h)
    (htrue : ∀ h, beta h * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta h * (1 - p.gamma h) ≤ 1 - phat.gamma h)
    (coin : Hybrid N → Bool) :
    (∏ h : Hybrid N, ENNReal.ofReal (beta h)) * (originalRegisterMeasure N p).toPMF coin ≤
      (originalRegisterMeasure N phat).toPMF coin := by
  rw [actual_original_register_product, actual_original_register_product]
  have h := Finset.prod_le_prod' (fun (h : Hybrid N) (_ : h ∈ Finset.univ) =>
    actual_bit_bank_lower (originalGamma p h) (originalGamma phat h) (beta h)
      (hbeta h) (htrue h) (hfalse h) (coin h))
  simpa only [Finset.prod_mul_distrib] using h

theorem actual_original_register_bank_lower (N : RootedBinary V E X)
    (p phat : HybridProbabilities N) (beta : Hybrid N → ℝ)
    (hbeta : ∀ h, 0 ≤ beta h)
    (htrue : ∀ h, beta h * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta h * (1 - p.gamma h) ≤ 1 - phat.gamma h)
    (register : V → Bool) :
    (∏ h : Hybrid N, ENNReal.ofReal (beta h)) * originalRegisterPMF N p register ≤
      originalRegisterPMF N phat register := by
  unfold originalRegisterPMF
  exact map_scaled_domination _ _ _
    (actual_original_register_coin_bank_lower N p phat beta hbeta htrue hfalse)
    (originalRegister N) register

theorem actual_natural_initial_code_bank_lower (N : RootedBinary V E X)
    (sample : Copy → X) (p phat : HybridProbabilities N) (beta : Hybrid N → ℝ)
    (hbeta : ∀ h, 0 ≤ beta h)
    (htrue : ∀ h, beta h * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta h * (1 - p.gamma h) ≤ 1 - phat.gamma h)
    (d : Code N sample) :
    (∏ h : Hybrid N, ENNReal.ofReal (beta h)) *
      ((originalRegisterPMF N p).map (initialCode N sample)) d ≤
      ((originalRegisterPMF N phat).map (initialCode N sample)) d := by
  exact map_scaled_domination _ _ _
    (actual_original_register_bank_lower N p phat beta hbeta htrue hfalse)
    (initialCode N sample) d

/-- The initial record retains the once-drawn register jointly with its Code. -/
theorem actual_joint_register_initial_code_bank_lower (N : RootedBinary V E X)
    (sample : Copy → X) (p phat : HybridProbabilities N) (beta : Hybrid N → ℝ)
    (hbeta : ∀ h, 0 ≤ beta h)
    (htrue : ∀ h, beta h * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta h * (1 - p.gamma h) ≤ 1 - phat.gamma h)
    (z : (V → Bool) × Code N sample) :
    (∏ h : Hybrid N, ENNReal.ofReal (beta h)) *
      ((originalRegisterPMF N p).map (fun register => (register, initialCode N sample register))) z ≤
      ((originalRegisterPMF N phat).map (fun register => (register, initialCode N sample register))) z := by
  exact map_scaled_domination _ _ _
    (actual_original_register_bank_lower N p phat beta hbeta htrue hfalse)
    (fun register => (register, initialCode N sample register)) z

#print axioms actual_bit_singleton
#print axioms actual_bit_bank_lower
#print axioms actual_current_coin_product
#print axioms actual_current_coin_bank_lower
#print axioms actual_current_owner_count
#print axioms actual_independent_pulse_bank_lower
#print axioms actual_independent_pulse_bank_lower_uniform
#print axioms actual_original_register_product
#print axioms actual_original_register_coin_bank_lower
#print axioms actual_original_register_bank_lower
#print axioms actual_natural_initial_code_bank_lower
#print axioms actual_joint_register_initial_code_bank_lower

end UnifiedLean.G6.InheritanceBankCommon
