import G5ObservedCutPosterior
import G5PosteriorJointCell

namespace GProgram.G5.ActualConditionalPartition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G5.OriginalProgramSurvival GProgram.G5.OriginalSelectedPosterior
open GProgram.G5.EnumeratedTripleRow GProgram.G5.EnumeratedPosteriorGerm
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourcePoissonKernel
open GProgram.G5.FrozenTripleAnalyticSupport
open GProgram.G5.ActualFrozenTripleRow GProgram.G5.TriplePartitionReadout
open GProgram.G5.FrozenTriplePolynomialKernel
open GProgram.G5.ObservedCutPosterior GProgram.G5.PosteriorJointCell
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The conditional future row is the Bayes ratio of the actual two-cut
partition joint row. The denominator is the genuine original survival mass. -/
theorem actual_conditional_partition_cell (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N)) (i : Fin 3 ≃ Copy) (t : ℝ≥0) (gene : Fin 5) :
    (((originalTripleCodePosterior N sample p r past).bind
      (sourceTimeKernel N r t)).map (indexedPartition N i)) gene =
      ((originalProgramLaw N sample p r past).bind (fun d =>
        (sourceProgram N r [.interval t] d).map (fun e =>
          (indexedPartition N i d,indexedPartition N i e)))) (0,gene) *
      ((originalProgramLaw N sample p r past).toOuterMeasure
        {d | indexedPartition N i d = 0})⁻¹ := by
  rw [← actual_observed_cut_posterior N sample p r past i]
  simpa [sourceProgram,sourceProgramStep] using
    posterior_joint_cell (originalProgramLaw N sample p r past) (sourceTimeKernel N r t)
      (indexedPartition N i) (indexedPartition N i) (0 : Fin 5) gene
      (actual_discrete_event_witness N sample p r past i)

theorem actual_discrete_denominator_positive (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N)) (i : Fin 3 ≃ Copy) :
    0 < ((originalProgramLaw N sample p r past).toOuterMeasure
      {d | indexedPartition N i d = 0}).toReal :=
  event_mass_real_positive _ _ (actual_discrete_event_witness N sample p r past i)

/-- The conditional joint-cell ratio identified from the original observation
is exactly the inherited positive finite frozen-source mixture. Population
locations remain the actual entering code's locations. -/
theorem actual_joint_ratio_frozen_mixture (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N)) (i : Fin 3 ≃ Copy)
    (place : ActualSeed N (originalTripleCodePosterior N sample p r past) → Copy → Option E)
    (hloc : ∀ s x, copyLocation (state s.val) x = originalPlace N (place s x))
    (t : ℝ≥0) (gene : Fin 5) :
    (((originalProgramLaw N sample p r past).bind (fun d =>
        (sourceProgram N r [.interval t] d).map (fun e =>
          (indexedPartition N i d,indexedPartition N i e)))) (0,gene) *
      ((originalProgramLaw N sample p r past).toOuterMeasure
        {d | indexedPartition N i d = 0})⁻¹).toReal =
    frozenMixture (actualSeedWeight N (originalTripleCodePosterior N sample p r past))
      (fun s => triplePopulationRate r (place s ∘ i))
      (fun s => ancestorPartition (place s ∘ i)) (t : ℝ) gene := by
  rw [← actual_conditional_partition_cell N sample p r past i t gene]
  exact actual_original_posterior_mixture N i sample p r past place hloc t gene

#print axioms actual_joint_ratio_frozen_mixture
#print axioms actual_conditional_partition_cell
#print axioms actual_discrete_denominator_positive
end GProgram.G5.ActualConditionalPartition
