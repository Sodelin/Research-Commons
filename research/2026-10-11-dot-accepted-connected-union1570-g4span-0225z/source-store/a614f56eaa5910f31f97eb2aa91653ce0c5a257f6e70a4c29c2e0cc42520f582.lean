import NaturalCalendarPastAdmission
import UnifiedLean.G6.CompleteObservationPrefix

/-!
Contributor: CLOUD-CALENDAR-REVIEW-SOL, 8 October 2026.
UNCHECKED additive ORIGINAL source composition, outside all176 inputs.
Keep the ACTUAL derived natural Code/old-bin prior correlated and exact;
approximate only the suffix history, then use SAME actual completion.
The full actual completed calendar supplies the compared output law.
No desired Gamma/old law, entering independence, inverse-bin age matrix,
new latent biological label or numerical-bank correspondence is assumed.
-/
namespace CloudG6.NaturalPastCompleteObservation
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.ChronologicalPathReadout GProgram.G2.SourceFiniteHistory
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG3.CompleteCalendarJointLaw CloudG3.ActualCalendarEndpointHistory
open CloudG3.ActualObservationCutRefinement
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.ProgramPrefix
open UnifiedLean.G6.HistoryPrefix UnifiedLean.G6.CompleteObservationPrefix
open CloudG6.NaturalCalendarPastAdmission
open scoped Classical NNReal ENNReal BigOperators

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- The full ACTUAL completed clock calendar from original leaf ages and
once-drawn original registers. The readout is applied only afterwards. -/
noncomputable def naturalCompletedJoint (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) : PMF (TaggedEndpoint (Tag := Tag) N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    completedJoint N r bin hbin ops (initialCode N sample register)
      (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b)))

/-- The SAME naturally derived correlated old past feeds every finite suffix
row. Only that future endpoint history is capped; completion is unchanged. -/
noncomputable def finiteNaturalPastComplete (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (K : ℕ) (bin : ℝ → Tag) (hbin : Measurable bin)
    (past : List (ProgramStep N)) (word : List (ProgramStep N × Tag)) (tailTag : Tag) :
    PMF (TaggedEndpoint (Tag := Tag) N sample) :=
  (naturalPastJoint N C sample p r bin hbin past).bind (fun q =>
    finiteCompleteJoint N r K word q.1 q.2 tailTag)

/-- Original full compiled-calendar support derives AncestralRoot for every
initial register. Actual completion and the natural-past append theorem then
supply the conditional suffix law with its SAME old tags; no Gamma field. -/
theorem actual_natural_completed_eq_past_suffix (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (past future : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = past ++ future)
    (cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ firstOriginalDate N C + (programDuration N (past ++ future) : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag) :
    naturalCompletedJoint N C sample p r bin hbin (past ++ future) =
      (naturalPastJoint N C sample p r bin hbin past).bind (fun q =>
        (calendarJoint N r bin hbin future q.1
          (firstOriginalDate N C + (programDuration N past : ℝ)) q.2).bind
            (jointTailKernel N r tailTag)) := by
  have hroot (register : V → Bool) :
      ∀ d ∈ (sourceProgram N r (past ++ future) (initialCode N sample register)).support,
        AncestralRoot N d := by
    intro d hd
    rw [← hwhole] at hd
    exact initialized_original_calendar_ancestral_support N C sample register H
      (originalGamma p) common r hd
  have hrow (register : V → Bool) :=
    actual_completed_joint_eq_gamma_tail N r bin hbin (past ++ future)
      (initialCode N sample register) (hroot register) (firstOriginalDate N C)
      cut tailTag hoff htail (leafAgeMatrix N C sample)
  unfold naturalCompletedJoint
  calc
    _ = (naturalPastJoint N C sample p r bin hbin (past ++ future)).bind
        (jointTailKernel N r tailTag) := by
      unfold naturalPastJoint
      rw [PMF.bind_bind]
      simp_rw [hrow]
    _ = _ := by rw [actual_natural_past_append, PMF.bind_bind]

/-- Uniform suffix domination for the actual carried old Tag matrix. Its
source/history law is derived by legal refinement and the actual fixed-bin
reader. No artificial real preimage of an arbitrary old bin is introduced. -/
theorem actual_suffix_tail_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (bin : ℝ → Tag) (hbin : Measurable bin)
    (future : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N future (physicalOps N word)) (s : Code N sample)
    (offset : ℝ) (B : Copy → Copy → Tag) (tailTag : Tag)
    (hword : wordBinContract N bin word offset)
    (z : TaggedEndpoint (Tag := Tag) N sample) :
    programMass (Copy := Copy) N r K (physicalOps N word) *
      finiteCompleteJoint N r K word s B tailTag z ≤
    ((calendarJoint N r bin hbin future s offset B).bind
      (jointTailKernel N r tailTag)) z := by
  rw [cut_refines_actual_calendar_joint N r bin hbin href s offset B,
    actual_calendar_joint_endpoint_history N r bin hbin word s offset B hword]
  unfold finiteCompleteJoint
  simpa only [mul_one] using bind_scaled_domination
    ((sourceHistoryLaw N r (physicalOps N word) s).map
      (endpointHistoryReadout N word s B))
    ((finiteHistoryLaw N r K (physicalOps N word) s).map
      (endpointHistoryReadout N word s B))
    (jointTailKernel N r tailTag) (jointTailKernel N r tailTag)
    (programMass (Copy := Copy) N r K (physicalOps N word)) 1
    (map_scaled_domination _ _ _ (actual_history_domination N r K
      (physicalOps N word) s) (endpointHistoryReadout N word s B))
    (fun _ _ => by simp) z

/-- One finite JOINT complete readout inherits ONLY the future suffix deficit.
The actual naturally initialized old Code/bins are derived and shared by
both laws, with their full dependence and old live subtrees intact. -/
theorem actual_natural_complete_readout_prefix_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (K : ℕ)
    (bin : ℝ → Tag) (hbin : Measurable bin) (past future : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = past ++ future)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N future (physicalOps N word)) (cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ firstOriginalDate N C + (programDuration N (past ++ future) : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag)
    (hword : wordBinContract N bin word
      (firstOriginalDate N C + (programDuration N past : ℝ)))
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    pmfTV ((naturalCompletedJoint N C sample p r bin hbin (past ++ future)).map readout)
      ((finiteNaturalPastComplete N C sample p r K bin hbin past word tailTag).map readout) ≤
      1 - (programMass (Copy := Copy) N r K (physicalOps N word)).toReal := by
  have hdom (z : TaggedEndpoint (Tag := Tag) N sample) :
      programMass (Copy := Copy) N r K (physicalOps N word) *
        finiteNaturalPastComplete N C sample p r K bin hbin past word tailTag z ≤
      naturalCompletedJoint N C sample p r bin hbin (past ++ future) z := by
    rw [actual_natural_completed_eq_past_suffix N C sample H p common r bin hbin
      past future hwhole cut tailTag hoff htail]
    unfold finiteNaturalPastComplete
    simpa only [one_mul] using bind_scaled_domination
      (naturalPastJoint N C sample p r bin hbin past)
      (naturalPastJoint N C sample p r bin hbin past)
      (fun q => (calendarJoint N r bin hbin future q.1
        (firstOriginalDate N C + (programDuration N past : ℝ)) q.2).bind
          (jointTailKernel N r tailTag))
      (fun q => finiteCompleteJoint N r K word q.1 q.2 tailTag) 1
      (programMass (Copy := Copy) N r K (physicalOps N word)) (fun _ => by simp)
      (fun q z => actual_suffix_tail_domination N r K bin hbin future word href
        q.1 (firstOriginalDate N C + (programDuration N past : ℝ)) q.2 tailTag hword z) z
  apply pmf_scaled_domination_tv
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K (physicalOps N word))
  · intro o
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ o)
      (map_scaled_domination _ _ _ hdom readout o)

/-- The same joint complete readout has an occurrence-wise suffix budget;
its number of coordinates and the exact past length incur no extra factor. -/
theorem actual_natural_complete_readout_prefix_tv_budget {O : Type*} [Fintype O]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (K : ℕ)
    (bin : ℝ → Tag) (hbin : Measurable bin) (past future : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = past ++ future)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N future (physicalOps N word)) (cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ firstOriginalDate N C + (programDuration N (past ++ future) : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag)
    (hword : wordBinContract N bin word
      (firstOriginalDate N C + (programDuration N past : ℝ)))
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    pmfTV ((naturalCompletedJoint N C sample p r bin hbin (past ++ future)).map readout)
      ((finiteNaturalPastComplete N C sample p r K bin hbin past word tailTag).map readout) ≤
      ((physicalOps N word).map
        (fun op => 1 - (stepMass (Copy := Copy) N r K op).toReal)).sum :=
  (actual_natural_complete_readout_prefix_tv N C sample H p common r K bin hbin
    past future hwhole word href cut tailTag hoff htail hword readout).trans
      (program_deficit_le_sum (Copy := Copy) N r K (physicalOps N word))

/-- The actual law in the TV theorem is the original register mixture of
complete-clock pushforwards through this SAME readout. No biological menu
or pruning identity follows merely from choosing a map. -/
theorem actual_natural_complete_observation_toMeasure {O : Type*} [Fintype O]
    [MeasurableSpace O] (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    ((naturalCompletedJoint N C sample p r bin hbin ops).map readout).toMeasure =
      ∑ register : V → Bool, originalRegisterPMF N p register •
        (completeCalendarTraceLaw N r ops (initialCode N sample register)).map
          (readout ∘ completeReadout N bin ops (initialCode N sample register)
            (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b))) := by
  have hrow (register : V → Bool) :=
    actual_complete_observation_toMeasure N r bin hbin ops (initialCode N sample register)
      (firstOriginalDate N C) (leafAgeMatrix N C sample) readout
  unfold naturalCompletedJoint
  rw [PMF.map_bind]
  apply Measure.ext
  intro S hS
  rw [PMF.toMeasure_bind_apply _ _ _ hS, tsum_fintype, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro register _
  rw [← hrow]

#print axioms actual_natural_completed_eq_past_suffix
#print axioms actual_suffix_tail_domination
#print axioms actual_natural_complete_readout_prefix_tv
#print axioms actual_natural_complete_readout_prefix_tv_budget
#print axioms actual_natural_complete_observation_toMeasure

end CloudG6.NaturalPastCompleteObservation
