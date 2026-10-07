import UnifiedLean.G6.ProgramPrefix
import UnifiedLean.G6.ResidualPrefix

/-!
UNCHECKED root draft, 2026-10-07.
The mean b is a numerical enclosure while every source iteration retains
the original physical rate bank. No biological retiming or arbitrary-real
enclosure oracle is supplied. Original hand conclusion: Astra count/source §5.
-/
namespace UnifiedLean.G6.MeanEnclosure
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.Conditioning
open UnifiedLean.G6.SourcePrefix UnifiedLean.G6.TaylorCertificate
open UnifiedLean.G6.ResidualPrefix UnifiedLean.G6.ProgramPrefix
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
open scoped BigOperators NNReal

theorem tv_triangle {A : Type*} [Fintype A] (p q r : A → ℝ) :
    tv p r ≤ tv p q + tv q r := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    abs_sub_le (p a) (q a) (r a))
  simp only [Finset.sum_add_distrib] at h
  unfold tv
  linarith

theorem count_mean_domination_real (a b : ℝ≥0) (hab : a ≤ b) (k : ℕ) :
    Real.exp ((a : ℝ) - b) * (countPMF a k).toReal ≤ (countPMF b k).toReal := by
  have hpow : (a : ℝ) ^ k ≤ (b : ℝ) ^ k :=
    pow_le_pow_left₀ a.coe_nonneg (by exact_mod_cast hab) k
  rw [countPMF_real, countPMF_real]
  have hexp : Real.exp ((a : ℝ) - b) * Real.exp (-(a : ℝ)) =
      Real.exp (-(b : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp ((a : ℝ) - b) * (Real.exp (-(a : ℝ)) * (a : ℝ) ^ k / k.factorial) =
        Real.exp (-(b : ℝ)) * (a : ℝ) ^ k / k.factorial := by
          rw [mul_div_assoc, ← mul_assoc, hexp]
    _ ≤ Real.exp (-(b : ℝ)) * (b : ℝ) ^ k / k.factorial :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
        (by positivity)

theorem count_mean_domination (a b : ℝ≥0) (hab : a ≤ b) (k : ℕ) :
    ENNReal.ofReal (Real.exp ((a : ℝ) - b)) * countPMF a k ≤ countPMF b k := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((countPMF a).apply_ne_top k))
    ((countPMF b).apply_ne_top k)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact count_mean_domination_real a b hab k

theorem count_bind_mean_domination {A : Type*} (a b : ℝ≥0) (hab : a ≤ b)
    (f : ℕ → PMF A) (d : A) :
    Real.exp ((a : ℝ) - b) * (((countPMF a).bind f) d).toReal ≤
      (((countPMF b).bind f) d).toReal := by
  have h : ENNReal.ofReal (Real.exp ((a : ℝ) - b)) * ((countPMF a).bind f) d ≤
      ((countPMF b).bind f) d := by
    simpa only [mul_one] using bind_scaled_domination
      (countPMF b) (countPMF a) f f (ENNReal.ofReal (Real.exp ((a : ℝ) - b))) 1
      (count_mean_domination a b hab) (fun _ _ => by simp) d
  have hr := ENNReal.toReal_mono (((countPMF b).bind f).apply_ne_top d) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hr

theorem count_bind_mean_tv {A : Type*} [Fintype A]
    (a b : ℝ≥0) (hab : a ≤ b) (f : ℕ → PMF A) :
    pmfTV ((countPMF a).bind f) ((countPMF b).bind f) ≤ (b : ℝ) - a := by
  let mu := Real.exp ((a : ℝ) - b)
  have hmu : mu ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact sub_nonpos.mpr hab')
  have hsum : (∑ d, mu * (((countPMF a).bind f) d).toReal) = mu := by
    rw [← Finset.mul_sum, pmf_sum_real, mul_one]
  have htv : pmfTV ((countPMF a).bind f) ((countPMF b).bind f) ≤ 1 - mu := by
    simpa only [pmfTV, hsum] using common_subprobability_tv _ _
      (fun d => mu * (((countPMF a).bind f) d).toReal)
      (pmf_sum_real _) (pmf_sum_real _)
      (fun d => by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hmu (ENNReal.toReal_nonneg :
          0 ≤ (((countPMF a).bind f) d).toReal))
      (count_bind_mean_domination a b hab f)
  have he := Real.add_one_le_exp ((a : ℝ) - b)
  dsimp [mu] at htv
  linarith

theorem count_bind_prefix_enclosure_tv {A : Type*} [Fintype A]
    (a b : ℝ≥0) (hab : a ≤ b) (f : ℕ → PMF A) (K : ℕ)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2) :
    pmfTV ((countPMF a).bind f) ((prefixCount b K).bind f) ≤
      ((b : ℝ) - a) + errorBound (b : ℝ) K := by
  have hfirst := count_bind_mean_tv a b hab f
  have hsecond : pmfTV ((countPMF b).bind f) ((prefixCount b K).bind f) ≤
      errorBound (b : ℝ) K :=
    (conditioned_mixture_tv _ _ (prefix_has_support b K) f).trans
      (prefix_deficit_le_certificate b K hK)
  have htri := tv_triangle (fun d => (((countPMF a).bind f) d).toReal)
    (fun d => (((countPMF b).bind f) d).toReal)
    (fun d => (((prefixCount b K).bind f) d).toReal)
  change pmfTV ((countPMF a).bind f) ((prefixCount b K).bind f) ≤
    pmfTV ((countPMF a).bind f) ((countPMF b).bind f) +
      pmfTV ((countPMF b).bind f) ((prefixCount b K).bind f) at htri
  linarith

theorem count_bind_residual_enclosure_tv {A : Type*} [Fintype A]
    (a b : ℝ≥0) (hab : a ≤ b) (f : ℕ → PMF A) (K : ℕ)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2) :
    tv (fun d => (((countPMF a).bind f) d).toReal)
      (residualVector ((prefixCount b K).bind f) (f 0) (residualMass (b : ℝ) K)) ≤
      ((b : ℝ) - a) + errorBound (b : ℝ) K := by
  have hfirst := count_bind_mean_tv a b hab f
  have hsecond : tv (fun d => (((countPMF b).bind f) d).toReal)
      (residualVector ((prefixCount b K).bind f) (f 0) (residualMass (b : ℝ) K)) ≤
      errorBound (b : ℝ) K := by
    rw [← residualMass_deficit]
    apply residualVector_tv _ _ _ _ (residualMass_bounds b K).2
    intro d
    exact (mul_le_mul_of_nonneg_right (residualMass_le_prefixMass b K hK)
      ENNReal.toReal_nonneg).trans
        (filtered_bind_domination_real _ _ (prefix_has_support b K) f d)
  have htri := tv_triangle (fun d => (((countPMF a).bind f) d).toReal)
    (fun d => (((countPMF b).bind f) d).toReal)
    (residualVector ((prefixCount b K).bind f) (f 0) (residualMass (b : ℝ) K))
  change tv (fun d => (((countPMF a).bind f) d).toReal)
      (residualVector ((prefixCount b K).bind f) (f 0) (residualMass (b : ℝ) K)) ≤
    pmfTV ((countPMF a).bind f) ((countPMF b).bind f) +
      tv (fun d => (((countPMF b).bind f) d).toReal)
        (residualVector ((prefixCount b K).bind f) (f 0) (residualMass (b : ℝ) K)) at htri
  linarith

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The enclosure changes only numerical count weights; the original r stays fixed. -/
noncomputable def finiteMeanPrefix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (b : ℝ≥0) (K : ℕ) (s : Code N sample) : PMF (Code N sample) :=
  (prefixCount b K).bind (fun k => sourceIteration N r k s)

theorem actual_source_enclosed_prefix_tv (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t b : ℝ≥0) (K : ℕ) (s : Code N sample)
    (hab : globalClockRate (Copy := Copy) r * t ≤ b)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2) :
    pmfTV (sourceTimeKernel N r t s) (finiteMeanPrefix N r b K s) ≤
      ((b : ℝ) - ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)) +
        errorBound (b : ℝ) K :=
  count_bind_prefix_enclosure_tv _ b hab (fun k => sourceIteration N r k s) K hK

theorem actual_source_joint_enclosed_prefix_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t b : ℝ≥0) (K : ℕ) (s : Code N sample)
    (readout : Code N sample → O)
    (hab : globalClockRate (Copy := Copy) r * t ≤ b)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2) :
    pmfTV ((sourceTimeKernel N r t s).map readout)
      ((finiteMeanPrefix N r b K s).map readout) ≤
      ((b : ℝ) - ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)) +
        errorBound (b : ℝ) K := by
  simp only [sourceTimeKernel, finiteMeanPrefix, PMF.map_bind]
  exact count_bind_prefix_enclosure_tv _ b hab
    (fun k => (sourceIteration N r k s).map readout) K hK

theorem actual_source_joint_enclosed_residual_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t b : ℝ≥0) (K : ℕ) (s : Code N sample)
    (readout : Code N sample → O)
    (hab : globalClockRate (Copy := Copy) r * t ≤ b)
    (hK : 2 * (b : ℝ) ≤ (K : ℝ) + 2) :
    tv (fun o => (((sourceTimeKernel N r t s).map readout) o).toReal)
      (residualVector ((finiteMeanPrefix N r b K s).map readout)
        ((sourceIteration N r 0 s).map readout) (residualMass (b : ℝ) K)) ≤
      ((b : ℝ) - ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)) +
        errorBound (b : ℝ) K := by
  simp only [sourceTimeKernel, finiteMeanPrefix, PMF.map_bind]
  exact count_bind_residual_enclosure_tv _ b hab
    (fun k => (sourceIteration N r k s).map readout) K hK

#print axioms tv_triangle
#print axioms count_mean_domination_real
#print axioms count_mean_domination
#print axioms count_bind_mean_domination
#print axioms count_bind_mean_tv
#print axioms count_bind_prefix_enclosure_tv
#print axioms count_bind_residual_enclosure_tv
#print axioms actual_source_enclosed_prefix_tv
#print axioms actual_source_joint_enclosed_prefix_tv
#print axioms actual_source_joint_enclosed_residual_tv
end UnifiedLean.G6.MeanEnclosure

