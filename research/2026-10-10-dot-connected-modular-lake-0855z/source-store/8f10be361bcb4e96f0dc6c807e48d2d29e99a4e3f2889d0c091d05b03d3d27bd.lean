import G5PhysicalCutChart
import G5ObservedTwoCutPartitionLaw

namespace GProgram.G5.PhysicalCutConditionalLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open GProgram.G2.ChronologicalPathReadout
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.ObservedBinHistory
open GProgram.G5.TwoCutSourceWord GProgram.G5.TwoCutPartitionDecoder
open GProgram.G5.ObservedTwoCutPartitionLaw GProgram.G5.OriginalProgramSurvival
open GProgram.G5.EnumeratedTripleRow GProgram.G5.EnumeratedPosteriorGerm
open GProgram.G5.ActualActivatedPrefix GProgram.G5.ActivatedPosteriorPlacement
open GProgram.G5.OriginalEpochChart GProgram.G5.PhysicalCutChart
open GProgram.G5.ActualConditionalPartition GProgram.G5.FrozenTripleAnalyticSupport
open GProgram.G5.ActualFrozenTripleRow GProgram.G5.TriplePartitionReadout
attribute [local instance] GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Complete below-root source use-site of the accepted G5 conditional-row
argument. The physical cut supplies its positive interval and literal prefix;
its actual population placement is derived, not assumed. -/
theorem actual_physical_cut_conditional_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (i : Fin 3 ≃ Copy) (a0 t : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (ht : a0 < t)
    (hroot : t < C.age N.root) (hnot : ∀ v, C.age v ≠ t) :
    ∃ (dates : List ℝ) (elapsed : ℝ≥0) (epsilon : ℝ), 0 < epsilon ∧
      let past := activatedPast N C H p common (firstOriginalDate N C) dates elapsed
      (0 < ((originalProgramLaw N sample p r past).toOuterMeasure
        {d | indexedPartition N i d = 0}).toReal) ∧
      ∀ u : ℝ≥0, (u : ℝ) < epsilon →
        (naturalObservedFullLaw N C sample H p common r).map
          (fun o => let B := observedAgeBins (twoCutBin t (t+u)) o
            (binPartition i 0 B,binPartition i 1 B)) =
          ((originalProgramLaw N sample p r past).bind (fun d =>
            (sourceProgram N r [.interval u] d).map (fun e =>
              (indexedPartition N i d,indexedPartition N i e)))).toMeasure ∧
        ∀ gene : Fin 5,
          (((originalProgramLaw N sample p r past).bind (fun d =>
            (sourceProgram N r [.interval u] d).map (fun e =>
              (indexedPartition N i d,indexedPartition N i e)))) (0,gene) *
            ((originalProgramLaw N sample p r past).toOuterMeasure
              {d | indexedPartition N i d = 0})⁻¹).toReal =
          frozenMixture (actualSeedWeight N (originalTripleCodePosterior N sample p r past))
            (fun s => triplePopulationRate r (codePopulation N s.val ∘ i))
            (fun s => ancestorPartition (codePopulation N s.val ∘ i)) (u : ℝ) gene := by
  have hfirst := first_date_of_contemporaneous_tips N C a0 htips
  have hft : firstOriginalDate N C < t := by simpa only [hfirst] using ht
  obtain ⟨pre,guard,next,post,hsplit,hleft,hright⟩ := original_gap_exists N C t hft hroot hnot
  obtain ⟨dates,hprefix⟩ := prefix_activation_shape N C H (originalGamma p) common pre guard next post hsplit
  let P := prefixThrough N C H (originalGamma p) common pre guard
  let elapsed := Real.toNNReal (t-guard)
  let past := activatedPast N C H p common (firstOriginalDate N C) dates elapsed
  have hpast : past = P ++ [.interval elapsed] := by
    unfold past activatedPast P
    rw [←hprefix]
  have hage : firstOriginalDate N C + (programDuration N P : ℝ) + (elapsed : ℝ) = t := by
    rw [prefix_age_is_guard N C H (originalGamma p) common pre guard next post hsplit]
    dsimp only [elapsed]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hleft.le)]
    ring
  have hsample : ∀ x : Copy, C.age (N.leaf (sample x)) = firstOriginalDate N C := by
    intro x
    rw [hfirst,htips]
  refine ⟨dates,elapsed,next-t,sub_pos.mpr hright,?_⟩
  dsimp only
  refine ⟨actual_discrete_denominator_positive N sample p r past i,?_⟩
  intro u hu
  constructor
  · have hw := actual_original_epoch_word N C H (originalGamma p) common pre guard next post hsplit
    rw [gap_three_parts hleft hright u hu] at hw
    have ho := actual_observed_two_cut_partition_law N C sample H p common r P
      (boundaryOperations N C H (originalGamma p) common next ++
        calendarTail N C H (originalGamma p) common next post)
      elapsed u (Real.toNNReal (next-t-u)) hw i
    dsimp only at ho
    rw [hage] at ho
    simpa only [←hpast] using ho
  · intro gene
    exact actual_activated_ratio_mixture N C sample H p common r
      (firstOriginalDate N C) dates elapsed u hsample i gene

#print axioms actual_physical_cut_conditional_law
end GProgram.G5.PhysicalCutConditionalLaw
