import G7OriginalBoundaryPolynomial
import UnifiedLean.Source.SourceNaturalInitialization

/-! One original hybrid-register polynomial mixture, before the actual source
programme. Repeated COMMON uses do not redraw these bits. -/
namespace GProgram.G7.OriginalInitializationPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory ProbabilityTheory
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestPulseMeasure
open GProgram.G7.OriginalBoundaryPolynomial
open scoped Classical BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_original_coin_mass (N : RootedBinary V E X) (p : HybridProbabilities N)
    (coin : Hybrid N → Bool) :
    ((originalRegisterMeasure N p).toPMF coin).toReal =
      ∏ h : Hybrid N, if coin h then p.gamma h else 1-p.gamma h := by
  rw [Measure.toPMF_apply,originalRegisterMeasure,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro h _
  cases hb : coin h <;>
    simp [bitMeasure,hb,← measureReal_def,bernoulliMeasure_real_apply,originalGamma]

noncomputable def registerPolynomial (N : RootedBinary V E X) (coin : Hybrid N → Bool) :
    MvPolynomial (Hybrid N) ℚ :=
  ∏ h : Hybrid N, if coin h then MvPolynomial.X h else 1-MvPolynomial.X h

lemma registerPolynomial_eval (N : RootedBinary V E X) (p : HybridProbabilities N)
    (coin : Hybrid N → Bool) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) p.gamma (registerPolynomial N coin) =
      ((originalRegisterMeasure N p).toPMF coin).toReal := by
  rw [actual_original_coin_mass]
  simp only [registerPolynomial,MvPolynomial.eval₂_prod]
  apply Finset.prod_congr rfl
  intro h _
  cases coin h <;> simp

noncomputable def initialPolynomial (N : RootedBinary V E X) (sample : Copy → X)
    (o : SelectedIndex N sample Finset.univ) : MvPolynomial (Hybrid N) ℚ :=
  ∑ coin : Hybrid N → Bool,
    if projection N Finset.univ (initialCode N sample (originalRegister N coin)) = o
    then registerPolynomial N coin else 0

theorem actual_original_initial_polynomial (N : RootedBinary V E X) (sample : Copy → X)
    (p : HybridProbabilities N) (o : SelectedIndex N sample Finset.univ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) p.gamma (initialPolynomial N sample o) =
      (((originalRegisterPMF N p).map (initialCode N sample)).map
        (projection N Finset.univ) o).toReal := by
  rw [originalRegisterPMF,PMF.map_comp,PMF.map_comp,map_probability_real]
  simp only [initialPolynomial,MvPolynomial.eval₂_sum,Function.comp_def]
  apply Finset.sum_congr rfl
  intro coin _
  by_cases h : projection N Finset.univ (initialCode N sample (originalRegister N coin)) = o
  · simp only [if_pos h,mul_one]
    exact registerPolynomial_eval N p coin
  · simp [h]

end GProgram.G7.OriginalInitializationPolynomial
