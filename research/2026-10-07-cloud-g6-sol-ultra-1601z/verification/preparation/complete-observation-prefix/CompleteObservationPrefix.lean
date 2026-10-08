import ActualObservationCutRefinement

/-!
Contributor: CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026.
UNCHECKED additive consumer, outside the frozen 165-module run.
The actual complete-calendar law, the same source history and unchanged
completion kernel supply the two laws. No desired Gamma/source equality
is assumed. Legal cuts, fixed-bin contracts and ancestral support remain
explicit. Normalized prefix conditioning is used; executable table and
physical entering-matrix/menu correspondence remain separate obligations.
-/

namespace UnifiedLean.G6.CompleteObservationPrefix
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.SourceFiniteHistory GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G2.ChronologicalPathReadout
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.ProgramPrefix
open UnifiedLean.G6.HistoryPrefix
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open CloudG3.CompleteCalendarJointLaw
open scoped Classical NNReal ENNReal BigOperators

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- The same finite-prefix history reader followed by the original exact
completion/tag-update kernel. No completion row is fitted or resampled. -/
noncomputable def finiteCompleteJoint (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (B : Copy → Copy → Tag) (tailTag : Tag) :
    PMF (TaggedEndpoint (Tag := Tag) N sample) :=
  ((finiteHistoryLaw N r K (physicalOps N word) s).map
    (endpointHistoryReadout N word s B)).bind (jointTailKernel N r tailTag)

/-- Actual Gamma is derived from the original finite calendar and legal
cut refinement; the exact tail uses the same kernel on both sides. -/
theorem actual_gamma_tail_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) (tailTag : Tag)
    (hword : wordBinContract N bin word offset)
    (z : TaggedEndpoint (Tag := Tag) N sample) :
    programMass (Copy := Copy) N r K (physicalOps N word) *
      finiteCompleteJoint N r K word s (fun a b => bin (M a b)) tailTag z ≤
    ((calendarJointPMF N r bin hbin ops s offset M).bind
      (jointTailKernel N r tailTag)) z := by
  rw [original_gamma_refined_endpoint_history N r bin hbin ops word href
    s offset M hword]
  unfold finiteCompleteJoint
  simpa only [mul_one] using bind_scaled_domination
    ((sourceHistoryLaw N r (physicalOps N word) s).map
      (endpointHistoryReadout N word s (fun a b => bin (M a b))))
    ((finiteHistoryLaw N r K (physicalOps N word) s).map
      (endpointHistoryReadout N word s (fun a b => bin (M a b))))
    (jointTailKernel N r tailTag) (jointTailKernel N r tailTag)
    (programMass (Copy := Copy) N r K (physicalOps N word)) 1
    (map_scaled_domination _ _ _ (actual_history_domination N r K
      (physicalOps N word) s) (endpointHistoryReadout N word s
        (fun a b => bin (M a b))))
    (fun _ _ => by simp) z

/-- Conversion of the actual complete-record pushforward into the already
proved principal Gamma/tail kernel, with explicit original support/cut. -/
theorem actual_completed_joint_eq_gamma_tail (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (ops : List (ProgramStep N)) (s : Code N sample)
    (hroot : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d)
    (offset cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ offset + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag) (M : Copy → Copy → ℝ) :
    completedJoint N r bin hbin ops s offset (fun a b => bin (M a b)) =
      (calendarJointPMF N r bin hbin ops s offset M).bind
        (jointTailKernel N r tailTag) := by
  apply PMF.toMeasure_injective
  rw [completed_joint_toMeasure]
  exact actual_complete_joint_source_law N r bin hbin ops s hroot
    offset cut tailTag hoff htail M

/-- One joint finite readout after the entire actual calendar and completion
inherits the history-prefix bound without multiplying by its coordinate count. -/
theorem actual_complete_joint_readout_prefix_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word)) (s : Code N sample)
    (hroot : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d)
    (offset cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ offset + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag) (M : Copy → Copy → ℝ)
    (hword : wordBinContract N bin word offset)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    pmfTV ((completedJoint N r bin hbin ops s offset
        (fun a b => bin (M a b))).map readout)
      ((finiteCompleteJoint N r K word s (fun a b => bin (M a b)) tailTag).map readout) ≤
      1 - (programMass (Copy := Copy) N r K (physicalOps N word)).toReal := by
  rw [actual_completed_joint_eq_gamma_tail N r bin hbin ops s hroot
    offset cut tailTag hoff htail M]
  apply pmf_scaled_domination_tv
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K (physicalOps N word))
  · intro o
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ o)
      (map_scaled_domination _ _ _
        (actual_gamma_tail_domination N r K bin hbin ops word href s
          offset M tailTag hword) readout o)

/-- The same actual full-output comparison has an occurrence-wise budget. -/
theorem actual_complete_joint_readout_prefix_tv_budget {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word)) (s : Code N sample)
    (hroot : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d)
    (offset cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ offset + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag) (M : Copy → Copy → ℝ)
    (hword : wordBinContract N bin word offset)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    pmfTV ((completedJoint N r bin hbin ops s offset
        (fun a b => bin (M a b))).map readout)
      ((finiteCompleteJoint N r K word s (fun a b => bin (M a b)) tailTag).map readout) ≤
      ((physicalOps N word).map
        (fun op => 1 - (stepMass (Copy := Copy) N r K op).toReal)).sum :=
  (actual_complete_joint_readout_prefix_tv N r K bin hbin ops word href
    s hroot offset cut tailTag hoff htail M hword readout).trans
      (program_deficit_le_sum (Copy := Copy) N r K (physicalOps N word))

/-- Honest finite event comparison for the same complete joint readout. -/
theorem actual_complete_joint_readout_prefix_event {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word)) (s : Code N sample)
    (hroot : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d)
    (offset cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ offset + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag) (M : Copy → Copy → ℝ)
    (hword : wordBinContract N bin word offset)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) (event : Finset O) :
    |(∑ o ∈ event, (((completedJoint N r bin hbin ops s offset
        (fun a b => bin (M a b))).map readout) o).toReal) -
      ∑ o ∈ event, (((finiteCompleteJoint N r K word s
        (fun a b => bin (M a b)) tailTag).map readout) o).toReal| ≤
      1 - (programMass (Copy := Copy) N r K (physicalOps N word)).toReal := by
  rw [actual_completed_joint_eq_gamma_tail N r bin hbin ops s hroot
    offset cut tailTag hoff htail M]
  apply pmf_scaled_domination_event
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K (physicalOps N word))
  · intro o
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ o)
      (map_scaled_domination _ _ _
        (actual_gamma_tail_domination N r K bin hbin ops word href s
          offset M tailTag hword) readout o)

/-- The PMF in the TV/event statements is the actual complete-record
pushforward through this SAME readout, rather than a supplied output law. -/
theorem actual_complete_observation_toMeasure {O : Type*} [Fintype O]
    [MeasurableSpace O] (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    (completeCalendarTraceLaw N r ops s).map
        (readout ∘ completeReadout N bin ops s offset (fun a b => bin (M a b))) =
      ((completedJoint N r bin hbin ops s offset
        (fun a b => bin (M a b))).map readout).toMeasure := by
  have ho : Measurable readout := measurable_of_countable _
  have hm := complete_readout_measurable N bin hbin ops s offset
    (fun a b => bin (M a b))
  calc
    _ = ((completeCalendarTraceLaw N r ops s).map
        (completeReadout N bin ops s offset (fun a b => bin (M a b)))).map readout :=
      (Measure.map_map ho hm).symm
    _ = ((completedJoint N r bin hbin ops s offset
        (fun a b => bin (M a b))).toMeasure).map readout :=
      congrArg (Measure.map readout)
        (completed_joint_toMeasure N r bin hbin ops s offset
          (fun a b => bin (M a b))).symm
    _ = _ := PMF.toMeasure_map readout _ ho

#print axioms actual_gamma_tail_domination
#print axioms actual_completed_joint_eq_gamma_tail
#print axioms actual_complete_joint_readout_prefix_tv
#print axioms actual_complete_joint_readout_prefix_tv_budget
#print axioms actual_complete_joint_readout_prefix_event
#print axioms actual_complete_observation_toMeasure

end UnifiedLean.G6.CompleteObservationPrefix
