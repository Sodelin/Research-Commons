import G5ActualActivatedPrefix
import G5ActualConditionalPartition

namespace GProgram.G5.ActivatedPosteriorPlacement
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open GProgram.G5.ActualActivatedPrefix GProgram.G5.OriginalProgramSurvival
open GProgram.G5.OriginalSelectedPosterior GProgram.G5.EnumeratedPosteriorGerm
open GProgram.G5.EnumeratedTripleRow GProgram.G5.ActualConditionalPartition
open GProgram.G5.ActualFrozenTripleRow GProgram.G5.TriplePartitionReadout
open GProgram.G5.FrozenTripleAnalyticSupport GProgram.G5.FrozenTriplePolynomialKernel
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def activatedPast (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (a : ℝ) (dates : List ℝ) (t : ℝ≥0) : List (ProgramStep N) :=
  boundaryOperations N C H (originalGamma p) common a ++
    calendarTail N C H (originalGamma p) common a dates ++ [.interval t]

theorem actual_original_activated_placement (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (a : ℝ) (dates : List ℝ) (t : ℝ≥0)
    (htips : ∀ x, C.age (N.leaf (sample x)) = a)
    (d : Code N sample)
    (hd : d ∈ (originalProgramLaw N sample p r (activatedPast N C H p common a dates t)).support)
    (x : Copy) : copyLocation (state d) x = originalPlace N (codePopulation N d x) := by
  obtain ⟨reg,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact codePopulation_actual N d
    (actual_activated_prefix_no_pending N C sample reg H (originalGamma p) common r a dates t htips d hdr) x

theorem actual_posterior_activated_placement (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (a : ℝ) (dates : List ℝ) (t : ℝ≥0)
    (htips : ∀ x, C.age (N.leaf (sample x)) = a)
    (s : ActualSeed N (originalTripleCodePosterior N sample p r
      (activatedPast N C H p common a dates t))) (x : Copy) :
    copyLocation (state s.val) x = originalPlace N (codePopulation N s.val x) := by
  have hd := ((PMF.mem_support_filter_iff
    (actual_full_code_event_witness N sample p r Finset.univ
      (activatedPast N C H p common a dates t))).mp s.property).2
  exact actual_original_activated_placement N C sample H p common r a dates t htips s.val hd x

/-- The source-derived positive mixture now takes its actual populations
from the Code itself; no population-location equality is a caller premise.
The actual compiler-prefix decomposition remains a separate use-site identity. -/
theorem actual_activated_ratio_mixture (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (a : ℝ) (dates : List ℝ) (t u : ℝ≥0)
    (htips : ∀ x, C.age (N.leaf (sample x)) = a) (i : Fin 3 ≃ Copy) (gene : Fin 5) :
    let past := activatedPast N C H p common a dates t
    (((originalProgramLaw N sample p r past).bind (fun d =>
      (sourceProgram N r [.interval u] d).map (fun e =>
        (indexedPartition N i d,indexedPartition N i e)))) (0,gene) *
      ((originalProgramLaw N sample p r past).toOuterMeasure
        {d | indexedPartition N i d = 0})⁻¹).toReal =
    frozenMixture (actualSeedWeight N (originalTripleCodePosterior N sample p r past))
      (fun s => triplePopulationRate r (codePopulation N s.val ∘ i))
      (fun s => ancestorPartition (codePopulation N s.val ∘ i)) (u : ℝ) gene := by
  dsimp only
  exact actual_joint_ratio_frozen_mixture N sample p r _ i (fun s => codePopulation N s.val)
    (actual_posterior_activated_placement N C sample H p common r a dates t htips) u gene

#print axioms actual_activated_ratio_mixture
#print axioms actual_posterior_activated_placement
end GProgram.G5.ActivatedPosteriorPlacement
