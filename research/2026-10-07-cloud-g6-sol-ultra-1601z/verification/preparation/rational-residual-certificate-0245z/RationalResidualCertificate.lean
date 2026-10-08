import UnifiedLean.G6.RationalCertificate
import UnifiedLean.G6.ResidualPrefix
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
UNCHECKED additive source prototype, 8 October 2026, internal Lean lane.
Computable rational coefficients of the ORIGINAL residual-lumped count law.
The existing normalized count evaluator remains separate. No Python/Rust
program semantics, source-state table enumeration or arbitrary-real oracle
is supplied here. This file is outside the running 176-module source freeze.
-/

namespace UnifiedLean.G6.RationalResidualCertificate
open UnifiedLean.G6.RationalCertificate UnifiedLean.G6.TaylorCertificate
open UnifiedLean.G6.SourcePrefix UnifiedLean.G6.ResidualPrefix
open UnifiedLean.G6.FiniteProbability
open scoped BigOperators NNReal

def rationalDenominator (q : ℚ) (K : ℕ) : ℚ :=
  rationalPrefix q K + 2 * rationalTerm q (K + 1)

def rationalRetained (q : ℚ) (K : ℕ) : ℚ :=
  rationalPrefix q K / rationalDenominator q K

/-- The residual is placed at count zero, with finite support at K. -/
def rationalResidualCount (q : ℚ) (K k : ℕ) : ℚ :=
  (if k ≤ K then rationalTerm q k / rationalDenominator q K else 0) +
    if k = 0 then rationalError q K else 0

lemma rationalDenominator_pos (q : ℚ) (hq : 0 ≤ q) (K : ℕ) :
    0 < rationalDenominator q K := by
  have hS := rationalPrefix_one_le hq K
  have hT := rationalTerm_nonneg hq (K + 1)
  unfold rationalDenominator
  linarith

lemma rationalRetained_bounds (q : ℚ) (hq : 0 ≤ q) (K : ℕ) :
    0 ≤ rationalRetained q K ∧ rationalRetained q K ≤ 1 := by
  have hS := rationalPrefix_one_le hq K
  have hT := rationalTerm_nonneg hq (K + 1)
  have hU := rationalDenominator_pos q hq K
  unfold rationalRetained
  constructor
  · exact div_nonneg (by linarith) hU.le
  · apply (div_le_one hU).mpr
    unfold rationalDenominator
    linarith

lemma rationalRetained_deficit (q : ℚ) (hq : 0 ≤ q) (K : ℕ) :
    1 - rationalRetained q K = rationalError q K := by
  have hU := ne_of_gt (rationalDenominator_pos q hq K)
  have hUexplicit : rationalPrefix q K + 2 * rationalTerm q (K + 1) ≠ 0 := hU
  unfold rationalRetained rationalDenominator rationalError
  field_simp [hUexplicit] <;> ring

lemma rationalResidualCount_nonneg (q : ℚ) (hq : 0 ≤ q) (K k : ℕ) :
    0 ≤ rationalResidualCount q K k := by
  have hU := (rationalDenominator_pos q hq K).le
  have hT := rationalTerm_nonneg hq k
  have hnext := rationalTerm_nonneg hq (K + 1)
  have herror : 0 ≤ rationalError q K := by
    change 0 ≤ 2 * rationalTerm q (K + 1) / rationalDenominator q K
    exact div_nonneg (by positivity) hU
  unfold rationalResidualCount
  by_cases hk : k ≤ K <;> by_cases hz : k = 0 <;>
    simp only [hk, hz, if_true, if_false] <;> positivity

lemma rationalResidualCount_support (q : ℚ) (K k : ℕ) (hk : K < k) :
    rationalResidualCount q K k = 0 := by
  have hle : ¬ k ≤ K := not_le.mpr hk
  have hz : k ≠ 0 := by omega
  simp only [rationalResidualCount, if_neg hle, if_neg hz, zero_add]

lemma rationalResidualCount_sum (q : ℚ) (hq : 0 ≤ q) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), rationalResidualCount q K k) = 1 := by
  have hfirst : (∑ k ∈ Finset.range (K + 1),
      (if k ≤ K then rationalTerm q k / rationalDenominator q K else 0)) =
      rationalRetained q K := by
    calc
      _ = ∑ k ∈ Finset.range (K + 1),
          rationalTerm q k / rationalDenominator q K := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      _ = rationalRetained q K := by
        rw [← Finset.sum_div]
        rfl
  have hzero : (∑ k ∈ Finset.range (K + 1),
      if k = 0 then rationalError q K else 0) = rationalError q K := by
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range, Nat.succ_pos, if_true]
  simp only [rationalResidualCount, Finset.sum_add_distrib, hfirst, hzero]
  have hd := rationalRetained_deficit q hq K
  linarith

lemma rationalDenominator_real (q : ℚ) (K : ℕ) :
    (rationalDenominator q K : ℝ) =
      taylorPrefix (q : ℝ) K + 2 * taylorTerm (q : ℝ) (K + 1) := by
  simp only [rationalDenominator, Rat.cast_add, Rat.cast_mul,
    Rat.cast_ofNat, rationalPrefix_real, rationalTerm_real]

lemma rationalRetained_real (q : ℚ) (K : ℕ) :
    (rationalRetained q K : ℝ) = residualMass (q : ℝ) K := by
  simp only [rationalRetained, Rat.cast_div, rationalPrefix_real,
    rationalDenominator_real, residualMass]

/-- Scalar coefficient correspondence with the already proved real backend. -/
theorem rationalResidualCount_actual (q : ℚ) (a : ℝ≥0)
    (ha : (a : ℝ) = (q : ℝ)) (K k : ℕ) :
    (rationalResidualCount q K k : ℝ) = residualCountReal a K k := by
  rw [residualCountReal_coefficients]
  simp [rationalResidualCount, rationalDenominator, rationalTerm_real,
    rationalPrefix_real, rationalError_real, ha]

theorem cutoff_residual_deficit (q ε : ℚ) (hq : 0 ≤ q) (hε : 0 < ε) :
    1 - rationalRetained q (cutoff q ε hq hε) ≤ ε := by
  rw [rationalRetained_deficit q hq]
  exact (cutoff_accepts q ε hq hε).2

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- An exact rational mean and computed cutoff certify the SAME source vector. -/
theorem actual_source_residual_tv_cutoff (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0)
    (q ε : ℚ) (hq : 0 ≤ q) (hε : 0 < ε)
    (hmean : ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) = (q : ℝ))
    (s : Code N sample) :
    tv (fun d => (sourceTimeKernel N r t s d).toReal)
      (residualSourceVector N r t (cutoff q ε hq hε) s) ≤ (ε : ℝ) := by
  have haccept := cutoff_accepts q ε hq hε
  have hK : 2 * ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) ≤
      (cutoff q ε hq hε : ℝ) + 2 := by
    rw [hmean]
    exact_mod_cast haccept.1
  have herror : errorBound (q : ℝ) (cutoff q ε hq hε) ≤ (ε : ℝ) := by
    rw [← rationalError_real]
    exact_mod_cast haccept.2
  have h := actual_source_residual_tv N r t (cutoff q ε hq hε) s hK
  rw [hmean] at h
  exact h.trans herror

#print axioms rationalDenominator
#print axioms rationalRetained
#print axioms rationalResidualCount
#print axioms rationalDenominator_pos
#print axioms rationalRetained_bounds
#print axioms rationalRetained_deficit
#print axioms rationalResidualCount_nonneg
#print axioms rationalResidualCount_support
#print axioms rationalResidualCount_sum
#print axioms rationalDenominator_real
#print axioms rationalRetained_real
#print axioms rationalResidualCount_actual
#print axioms cutoff_residual_deficit
#print axioms actual_source_residual_tv_cutoff
end UnifiedLean.G6.RationalResidualCertificate
