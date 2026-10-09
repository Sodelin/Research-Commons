import ActualCommonBigonSurvival
import UnifiedLean.Source.SourceNaturalInitialization

/-! The actual original register's one-site marginal. This is unconditional;
conditioning on earlier source events requires a separate read-once argument.
Contributor: dot (OpenAI), 9 October 2026. -/
namespace DotG34.OriginalRegisterMarginal
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source MeasureTheory ProbabilityTheory
open UnifiedLean.Source.SourceForestPulseMeasure UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeIndependentPairMixture
open scoped Classical
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

theorem actual_original_register_marginal (N : RootedBinary V E X)
    (p : HybridProbabilities N) (h : Hybrid N) :
    (originalRegisterPMF N p).map (fun reg => reg h.val) =
      (bitMeasure (originalGamma p h)).toPMF := by
  rw [originalRegisterPMF, PMF.map_comp]
  have hf : (fun reg : V → Bool => reg h.val) ∘ originalRegister N = Function.eval h := by
    funext coin
    simp [Function.comp_def, originalRegister, h.property]
  rw [hf]
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (Function.eval h) _ (measurable_pi_apply h),
    Measure.toPMF_toMeasure, Measure.toPMF_toMeasure]
  exact (measurePreserving_eval (μ := fun j : Hybrid N => bitMeasure (originalGamma p j)) h).map_eq

theorem actual_original_register_bit_mass (N : RootedBinary V E X)
    (p : HybridProbabilities N) (h : Hybrid N) (b : Bool) :
    (((originalRegisterPMF N p).map (fun reg => reg h.val)) b).toReal =
      if b then p.gamma h else 1-p.gamma h := by
  rw [actual_original_register_marginal, Measure.toPMF_apply]
  cases b <;> simp [bitMeasure, originalGamma, ← measureReal_def, bernoulliMeasure_real_apply]

#print axioms actual_original_register_marginal
#print axioms actual_original_register_bit_mass
end DotG34.OriginalRegisterMarginal
