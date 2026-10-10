import NaturalPastCompleteObservation
import UnifiedLean.G6.FiniteCorruptionBoundary

/-!
CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026.
UNCHECKED original-source observation consumer, outside176 and staged179.
One ACTUAL once-drawn-register, native compiled calendar and completion
joint law is read once. No supplied desired observation law is a field.
-/
namespace CloudG6.ActualObservationCorruption

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open CloudG3.ActualCutJointLaw CloudG6.NaturalPastCompleteObservation
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open scoped Classical

universe u v w x y z
variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y} {O : Type z}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Fintype Tag] [Fintype O]
variable [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

/-- Uses the actual whole ORIGINAL calendar, not an arbitrary stochastic row.
A finite readout alone does not establish biological menu/pruning admission. -/
noncomputable def actualCompiledObservation (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) : PMF O :=
  (naturalCompletedJoint N C sample p r bin hbin
    (compiledCalendarProgram N C H (originalGamma p) common)).map readout

/-- q may be another actual source observation, with a different finite
original graph/carrier, provided both are read into the SAME joint alphabet.
This is pairwise overlap, not distance to an entire wrong target image. -/
theorem actual_original_observation_shared_corruption_iff
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) (q : PMF O) (beta : ℝ) :
    (∃ observed : PMF O,
      pmfTV (actualCompiledObservation N C sample H p common r bin hbin readout)
        observed ≤ beta ∧ pmfTV q observed ≤ beta) ↔
    pmfTV (actualCompiledObservation N C sample H p common r bin hbin readout) q ≤
      2 * beta := by
  exact shared_corruption_iff _ q beta

#print axioms actual_original_observation_shared_corruption_iff

end CloudG6.ActualObservationCorruption
