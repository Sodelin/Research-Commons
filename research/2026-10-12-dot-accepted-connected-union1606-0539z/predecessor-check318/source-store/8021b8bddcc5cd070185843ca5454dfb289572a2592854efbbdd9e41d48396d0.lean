import UnifiedLean.Source.UniformizedSourceStep
import UnifiedLean.Source.SourceForestIntrinsicGenerator
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual normalized source step bound to its original forest generator

Contributor: dot, 2026-10-02. The uniformized finite PMF is connected to the
existing original forest/population/register generator, including source-valid
snapshot encoding after each real merger. This is the source operator instance
needed before matrix-exponential/finite-time transport; calendar-compatible
reachability and timed-path observations remain separate.
-/
namespace UnifiedLean.Source.SourceStepGeneratorBinding
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open MeasureTheory
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance codeMeasurable {N : RootedBinary V E X} {sample : Copy → X} :
    MeasurableSpace (Code N sample) := ⊤
local instance choiceMeasurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : MeasurableSpace (Option (Choice N s)) := ⊤

lemma choicePMF_real (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Option (Choice N s)) :
    (choicePMF N r s p).toReal = choiceMass N r s p := by
  simp only [choicePMF,PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (choiceMass_nonnegative N r s p)]

/-- Actual PMF expectation, not a separate fitted finite weighted table. -/
theorem sourceStep_expectation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (F : Code N sample → ℝ) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * F d) =
      ∑ p : Option (Choice N s), choiceMass N r s p * F (stepDestination N s p) := by
  have hm : Measurable (stepDestination N s) := measurable_of_countable _
  have hf : Measurable F := measurable_of_countable _
  calc
    _ = ∫ d, F d ∂(sourceStep N r s).toMeasure := by
      rw [PMF.integral_eq_sum]
      simp only [smul_eq_mul]
    _ = ∫ p, F (stepDestination N s p) ∂(choicePMF N r s).toMeasure := by
      rw [sourceStep,← PMF.toMeasure_map (stepDestination N s) (choicePMF N r s) hm,integral_map hm.aemeasurable hf.aestronglyMeasurable]
    _ = _ := by
      rw [PMF.integral_eq_sum]
      simp only [smul_eq_mul,choicePMF_real]

/-- A real source merger is encoded/decoded without changing its complete
selected INTERNAL view. Original graph/sample/registry IDs remain fixed. -/
lemma merged_destination_selectedView (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (p : Choice N s) :
    selectedView (state (stepDestination N s (some p))) keep =
      selectedView (merge (state s) p.2.val.1 p.2.val.2) keep := by
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  let hs := merge_source_valid N sample (state s) s.property hm
  exact decode_encode_selectedView N.root (merge (state s) p.2.val.1 p.2.val.2) hs.forest keep

/-- The actual weighted source choices have the EXACT inherited generator
increment, with no posterior/refitted source or assumed generator field. -/
theorem actual_choice_increment_eq_native_generator (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (keep : Finset Copy) (f : SelectedView V E Copy → ℝ) :
    (∑ p : Choice N s, choiceRate N r s p *
      (f (selectedView (state (stepDestination N s (some p))) keep) -
        f (selectedView (state s) keep))) =
      nativeSourceGenerator N.root (state s) keep r.edge r.ancestral f := by
  simp_rw [merged_destination_selectedView]
  unfold choiceRate
  rw [Fintype.sum_sigma,Fintype.sum_option]
  unfold nativeSourceGenerator originalPopulationGenerator sourceIncrement
  simp only [pairRate,originalPlace]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_attach ((populationRoots (state s) (.edge e)).offDiag)
      (fun p : Copy × Copy => f (selectedView (merge (state s) p.1 p.2) keep) -
        f (selectedView (state s) keep))
  · rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_attach ((populationRoots (state s) (.rootPopulation N.root)).offDiag)
      (fun p : Copy × Copy => f (selectedView (merge (state s) p.1 p.2) keep) -
        f (selectedView (state s) keep))

/-- Explicit finite-step expectation is the current readout plus its actual
source-generator increment divided by the PROVED global uniformization rate. -/
theorem sourceStep_expectation_eq_generator (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (keep : Finset Copy) (f : SelectedView V E Copy → ℝ) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * f (selectedView (state d) keep)) =
      f (selectedView (state s) keep) +
        nativeSourceGenerator N.root (state s) keep r.edge r.ancestral f /
          globalRateBound (Copy := Copy) r := by
  rw [sourceStep_expectation,Fintype.sum_option]
  simp only [choiceMass]
  rw [show stepDestination N s none = s from rfl]
  rw [← actual_choice_increment_eq_native_generator N r s keep f]
  have hpos := globalRateBound_positive (Copy := Copy) r
  have hsum : (∑ p : Choice N s, choiceRate N r s p *
      (f (selectedView (state (stepDestination N s (some p))) keep) -
        f (selectedView (state s) keep))) =
      (∑ p : Choice N s, choiceRate N r s p *
        f (selectedView (state (stepDestination N s (some p))) keep)) -
      totalRate N r s * f (selectedView (state s) keep) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,totalRate]
  rw [hsum]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  ring

/-- The constructed normalized source PMF's entire selected-view expectation
is intrinsic to that view. This is the actual finite-step source binding for
the existing infinitesimal G2 transport, not yet a time/calendar theorem. -/
theorem sourceStep_selected_expectation_intrinsic (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (keep : Finset Copy) (f : SelectedView V E Copy → ℝ) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * f (selectedView (state d) keep)) =
      f (selectedView (state s) keep) +
        intrinsicSourceGenerator N.root (selectedView (state s) keep) keep r.edge r.ancestral f /
          globalRateBound (Copy := Copy) r := by
  rw [sourceStep_expectation_eq_generator,
    native_source_generator_intertwining N.root (state s) s.property.forest keep r.edge r.ancestral f]

#print axioms sourceStep_expectation
#print axioms merged_destination_selectedView
#print axioms actual_choice_increment_eq_native_generator
#print axioms sourceStep_expectation_eq_generator
#print axioms sourceStep_selected_expectation_intrinsic
end UnifiedLean.Source.SourceStepGeneratorBinding
