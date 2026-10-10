import UnifiedLean.Source.SourceCompletionHarmonic

/-!
# Actual original ancestral kernel converges to its constructed completion

Contributor: dot, 2026-10-02. This closes the eventual-law admission of the
finite ancestral jump completion: for every original source root state, the
actual normalized source-time kernel converges coordinatewise to that same
completion PMF. The proof uses derived harmonicity and actual exponential
transient decay; no desired limiting distribution is supplied as a premise.
-/
namespace UnifiedLean.Source.SourceEventualCompletionLimit
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Filter
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceAncestralDrift
open UnifiedLean.Source.SourceAncestralAbsorption
open UnifiedLean.Source.SourceCompletionHarmonic
open scoped Classical BigOperators NNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma pmf_real_le_one {A : Type*} (p : PMF A) (a : A) : (p a).toReal ≤ 1 := by
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one a)

/-- Actual terminal-coordinate error is controlled by the source's derived
transient mass. The fixed finite state-count factor is explicit and makes no
claim about hidden source-graph recognition budgets. -/
theorem actual_ancestral_completion_error [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample)
    (hs : AncestralRoot N s) :
    |(sourceTimeKernel N r t s d).toReal-(completionKernel N r s d).toReal| ≤
      (Fintype.card (Code N sample) : ℝ)*excessRank s*Real.exp (-(r.ancestral/2*(t : ℝ))) := by
  have hh := congrArg (fun p : PMF (Code N sample) => (p d).toReal)
    (completion_source_time_harmonic N r t s hs)
  rw [bind_probability_real,tsum_fintype] at hh
  have hδ : (∑ z : Code N sample, (sourceTimeKernel N r t s z).toReal *
      (if z = d then (1 : ℝ) else 0)) = (sourceTimeKernel N r t s d).toReal := by simp
  rw [← hδ,← hh,← Finset.sum_sub_distrib]
  have hterm : ∀ z : Code N sample,
      |(sourceTimeKernel N r t s z).toReal * (if z = d then (1 : ℝ) else 0) -
        (sourceTimeKernel N r t s z).toReal * (completionKernel N r z d).toReal| ≤
      excessRank s*Real.exp (-(r.ancestral/2*(t : ℝ))) := by
    intro z
    by_cases hz : liveCard z ≤ 1
    · rw [completion_terminal N r z hz]
      simp only [PMF.pure_apply,apply_ite,ENNReal.toReal_one,ENNReal.toReal_zero]
      have hnon := mul_nonneg (excessRank_nonnegative N s) (Real.exp_pos (-(r.ancestral/2*(t : ℝ)))).le
      by_cases heq : z = d
      · subst z; simpa using hnon
      · simpa [heq,Ne.symm heq] using hnon
    · have hunit : |(if z = d then (1 : ℝ) else 0)-(completionKernel N r z d).toReal| ≤ 1 := by
        have hp := pmf_real_le_one (completionKernel N r z) d
        have hn : 0 ≤ (completionKernel N r z d).toReal := ENNReal.toReal_nonneg
        apply abs_le.mpr
        split_ifs <;> constructor <;> linarith
      calc
        _ = (sourceTimeKernel N r t s z).toReal *
            |(if z = d then (1 : ℝ) else 0)-(completionKernel N r z d).toReal| := by
          rw [← mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
        _ ≤ (sourceTimeKernel N r t s z).toReal := by
          nlinarith [show 0 ≤ (sourceTimeKernel N r t s z).toReal from ENNReal.toReal_nonneg]
        _ ≤ _ := actual_ancestral_time_transient_bound N r t s z hs (lt_of_not_ge hz)
  calc
    _ ≤ ∑ z : Code N sample,
        |(sourceTimeKernel N r t s z).toReal * (if z = d then (1 : ℝ) else 0) -
          (sourceTimeKernel N r t s z).toReal * (completionKernel N r z d).toReal| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Code N sample, excessRank s*Real.exp (-(r.ancestral/2*(t : ℝ))) :=
      Finset.sum_le_sum (fun z _ => hterm z)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

/-- Genuine eventual ORIGINAL-source completion law. Every coordinate of the
actual source-time PMF converges to the already constructed exponential-winner
completion, with no absorption or terminal-law field in the model. -/
theorem actual_ancestral_kernel_tendsto_completion [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s d : Code N sample)
    (hs : AncestralRoot N s) :
    Tendsto (fun t : ℝ≥0 => (sourceTimeKernel N r t s d).toReal) atTop
      (𝓝 (completionKernel N r s d).toReal) := by
  have ht : Tendsto (fun t : ℝ≥0 => -(r.ancestral/2*(t : ℝ))) atTop atBot := by
    simpa only [neg_mul,id_eq] using
      (NNReal.tendsto_coe_atTop.mpr tendsto_id).const_mul_atTop_of_neg
        (show -(r.ancestral/2) < 0 by linarith [r.ancestral_pos])
  have hb : Tendsto (fun t : ℝ≥0 => (Fintype.card (Code N sample) : ℝ)*excessRank s*
      Real.exp (-(r.ancestral/2*(t : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using (Real.tendsto_exp_atBot.comp ht).const_mul
      ((Fintype.card (Code N sample) : ℝ)*excessRank s)
  have hc : Tendsto (fun _ : ℝ≥0 => (completionKernel N r s d).toReal) atTop
      (𝓝 (completionKernel N r s d).toReal) := tendsto_const_nhds
  have hlo := hc.sub hb
  have hhi := hc.add hb
  simp only [sub_zero,add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro t
    have hh := (abs_le.mp (actual_ancestral_completion_error N r t s d hs)).1
    linarith
  · intro t
    have hh := (abs_le.mp (actual_ancestral_completion_error N r t s d hs)).2
    linarith

#print axioms actual_ancestral_completion_error
#print axioms actual_ancestral_kernel_tendsto_completion
end UnifiedLean.Source.SourceEventualCompletionLimit
