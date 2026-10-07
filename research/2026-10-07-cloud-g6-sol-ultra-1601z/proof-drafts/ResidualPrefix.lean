import UnifiedLean.G6.TaylorCertificate

/-!
UNCHECKED draft: residual lumping is distinct from normalized conditioning.
CLOUD-G6-SOL-ULTRA-20261007, 2026-10-07.
Translates the residual alternative in Astra's count/source handoff §3.
The vector adds the residual to the SAME sourceIteration at count zero.
No executable correspondence, calendar readout or positive reconstruction
is assumed or established by this finite endpoint adapter.
-/
namespace UnifiedLean.G6.ResidualPrefix
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.Conditioning
open UnifiedLean.G6.SourcePrefix UnifiedLean.G6.TaylorCertificate
open scoped Classical BigOperators NNReal

noncomputable def residualMass (a : ℝ) (K : ℕ) : ℝ :=
  taylorPrefix a K / (taylorPrefix a K + 2 * taylorTerm a (K + 1))

lemma residualMass_bounds (a : ℝ≥0) (K : ℕ) :
    0 ≤ residualMass (a : ℝ) K ∧ residualMass (a : ℝ) K ≤ 1 := by
  have hS := taylorPrefix_pos a K
  have hT := taylorTerm_nonneg a.coe_nonneg (K + 1)
  have hU : 0 < taylorPrefix (a : ℝ) K + 2 * taylorTerm (a : ℝ) (K + 1) := by
    linarith
  constructor
  · exact div_nonneg hS.le hU.le
  · exact (div_le_one hU).mpr (by linarith)

lemma residualMass_deficit (a : ℝ≥0) (K : ℕ) :
    1 - residualMass (a : ℝ) K = errorBound (a : ℝ) K := by
  have hS := taylorPrefix_pos a K
  have hT := taylorTerm_nonneg a.coe_nonneg (K + 1)
  have hU : taylorPrefix (a : ℝ) K + 2 * taylorTerm (a : ℝ) (K + 1) ≠ 0 := by
    positivity
  unfold residualMass errorBound
  field_simp [hU]
  <;> ring

lemma residualMass_le_prefixMass (a : ℝ≥0) (K : ℕ)
    (hK : 2 * (a : ℝ) ≤ (K : ℝ) + 2) :
    residualMass (a : ℝ) K ≤ prefixMass a K := by
  have h := prefix_deficit_le_certificate a K hK
  rw [← residualMass_deficit] at h
  linarith

/-- Real coordinates of a probability vector; z is the residual destination law. -/
noncomputable def residualVector {A : Type*} (q z : PMF A) (rho : ℝ) : A → ℝ :=
  fun a => rho * (q a).toReal + (1 - rho) * (z a).toReal

lemma residualVector_nonneg {A : Type*} (q z : PMF A) (rho : ℝ)
    (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (a : A) :
    0 ≤ residualVector q z rho a := by
  exact add_nonneg (mul_nonneg h0 ENNReal.toReal_nonneg)
    (mul_nonneg (sub_nonneg.mpr h1) ENNReal.toReal_nonneg)

lemma residualVector_sum {A : Type*} [Fintype A] (q z : PMF A) (rho : ℝ) :
    (∑ a, residualVector q z rho a) = 1 := by
  simp only [residualVector, Finset.sum_add_distrib, ← Finset.mul_sum, pmf_sum_real,
    mul_one]
  ring

theorem residualVector_tv {A : Type*} [Fintype A]
    (p q z : PMF A) (rho : ℝ) (h1 : rho ≤ 1)
    (hdom : ∀ a, rho * (q a).toReal ≤ (p a).toReal) :
    tv (fun a => (p a).toReal) (residualVector q z rho) ≤ 1 - rho := by
  have hsum : (∑ a, rho * (q a).toReal) = rho := by
    rw [← Finset.mul_sum, pmf_sum_real, mul_one]
  have hcommon (a : A) : rho * (q a).toReal ≤ residualVector q z rho a := by
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h1) ENNReal.toReal_nonneg)
  simpa only [hsum] using common_subprobability_tv _ _ _
    (pmf_sum_real p) (residualVector_sum q z rho) hdom hcommon

/-- Count coefficients of the distinct residual-lumped law. -/
noncomputable def residualCountReal (a : ℝ≥0) (K k : ℕ) : ℝ :=
  residualMass (a : ℝ) K * (prefixCount a K k).toReal +
    if k = 0 then errorBound (a : ℝ) K else 0

theorem residualCountReal_coefficients (a : ℝ≥0) (K k : ℕ) :
    residualCountReal a K k =
      (if k ≤ K then taylorTerm (a : ℝ) k /
        (taylorPrefix (a : ℝ) K + 2 * taylorTerm (a : ℝ) (K + 1)) else 0) +
      if k = 0 then errorBound (a : ℝ) K else 0 := by
  unfold residualCountReal
  rw [prefixCount_real]
  congr 1
  by_cases hk : k ≤ K
  · rw [if_pos hk, if_pos hk]
    unfold residualMass
    have hS := ne_of_gt (taylorPrefix_pos a K)
    field_simp [hS]
    <;> ring
  · simp only [if_neg hk, mul_zero]

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Residual is assigned to count zero of the original source, not a new state. -/
noncomputable def residualSourceVector (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample) : Code N sample → ℝ :=
  residualVector (finiteSourcePrefix N r t K s) (sourceIteration N r 0 s)
    (residualMass ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K)

theorem actual_source_residual_tv (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample)
    (hK : 2 * ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) ≤ (K : ℝ) + 2) :
    tv (fun d => (sourceTimeKernel N r t s d).toReal) (residualSourceVector N r t K s) ≤
      errorBound ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K := by
  rw [← residualMass_deficit]
  apply residualVector_tv _ _ _ _ (residualMass_bounds _ K).2
  intro d
  exact (mul_le_mul_of_nonneg_right (residualMass_le_prefixMass _ K hK)
    ENNReal.toReal_nonneg).trans (actual_source_prefix_domination N r t K s d)

/-- One finite joint readout uses the same residual mixture and source bank. -/
theorem actual_source_joint_residual_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample)
    (readout : Code N sample → O)
    (hK : 2 * ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) ≤ (K : ℝ) + 2) :
    tv (fun o => (((sourceTimeKernel N r t s).map readout) o).toReal)
      (residualVector ((finiteSourcePrefix N r t K s).map readout)
        ((sourceIteration N r 0 s).map readout)
        (residualMass ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K)) ≤
      errorBound ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K := by
  rw [← residualMass_deficit]
  apply residualVector_tv _ _ _ _ (residualMass_bounds _ K).2
  intro o
  have hdom : prefixMass (globalClockRate (Copy := Copy) r * t) K *
      (((finiteSourcePrefix N r t K s).map readout) o).toReal ≤
      (((sourceTimeKernel N r t s).map readout) o).toReal := by
    simp only [finiteSourcePrefix, sourceTimeKernel, PMF.map_bind]
    exact filtered_bind_domination_real _ _ (prefix_has_support _ K)
      (fun k => (sourceIteration N r k s).map readout) o
  exact (mul_le_mul_of_nonneg_right (residualMass_le_prefixMass _ K hK)
    ENNReal.toReal_nonneg).trans hdom

#print axioms residualMass_bounds
#print axioms residualMass_deficit
#print axioms residualMass_le_prefixMass
#print axioms residualVector_nonneg
#print axioms residualVector_sum
#print axioms residualVector_tv
#print axioms residualCountReal_coefficients
#print axioms actual_source_residual_tv
#print axioms actual_source_joint_residual_tv
end UnifiedLean.G6.ResidualPrefix
