import NaturalPastCompleteObservation
import UnifiedLean.Source.SourceAncestralAbsorption

/-! Original-natural-register consumer of the previously proved exact ancestral
cut-extension identity. No new Markov or completion law is assumed or proved.
Contributor: dot, 2026-10-09. -/
namespace UnifiedLean.G6.NaturalAncestralCutExtension
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceAncestralAbsorption
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceCalendarCompatibility
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ChronologicalPathReadout
open CloudG3.ActualCalendarCutContext CloudG3.CompleteCalendarJointLaw
open CloudG6.NaturalPastCompleteObservation CloudG6.NaturalCalendarPastAdmission
open UnifiedLean.G6.CompleteObservationPrefix
open scoped NNReal
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Re-express the inherited same-clock measure identity as its actual PMF. -/
theorem completed_joint_append_interval (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (t : ℝ≥0) (B : Copy → Copy → Tag) :
    completedJoint N r bin hbin ops s offset B =
      completedJoint N r bin hbin (ops ++ [.interval t]) s offset B := by
  apply PMF.toMeasure_injective
  rw [completed_joint_toMeasure, completed_joint_toMeasure]
  exact actual_complete_calendar_cut_refinement N r bin hbin ops s offset t B

/-- The unchanged original register mixture, initialization, old ages and bin
map describe the same completed experiment after exposing an extra interval. -/
theorem natural_completed_append_interval (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (t : ℝ≥0) :
    naturalCompletedJoint N C sample p r bin hbin ops =
      naturalCompletedJoint N C sample p r bin hbin (ops ++ [.interval t]) := by
  unfold naturalCompletedJoint
  apply congrArg (PMF.bind (originalRegisterPMF N p))
  funext register
  exact completed_joint_append_interval N r bin hbin ops _ _ t _

/-- Every finite requested last cut lies before the extended end. The exact
unbounded ancestral completion above that end is still retained. -/
theorem extend_beyond_cut (N : RootedBinary V E X) (offset cut : ℝ)
    (ops : List (ProgramStep N)) :
    cut ≤ offset + (programDuration N
      (ops ++ [.interval (Real.toNNReal (cut - (offset + (programDuration N ops : ℝ))))]) : ℝ) := by
  rw [program_duration_append]
  simp only [programDuration, add_zero, NNReal.coe_add]
  have h := Real.le_coe_toNNReal (cut - (offset + (programDuration N ops : ℝ)))
  linarith

/-- An exposed ancestral interval preserves the actual root support, by the
inherited source-iteration support theorem rather than a new completion axiom. -/
theorem ancestral_time_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample)
    (hs : AncestralRoot N s) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : AncestralRoot N d := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact ancestral_iteration_support N r k s hs hk

/-- The genuine original compiled calendar, followed by the SAME positive
ancestral population, remains on ancestral-root support for every original
register assignment. No observational success conditioning is introduced. -/
theorem original_extended_ancestral_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (register : V → Bool) (t : ℝ≥0)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (compiledCalendarProgram N C H (originalGamma p) common ++ [.interval t])
      (initialCode N sample register)).support) : AncestralRoot N d := by
  rw [sourceProgram_append] at hd
  obtain ⟨s,hs,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hsroot := initialized_original_calendar_ancestral_support N C sample register H
    (originalGamma p) common r hs
  have htime : d ∈ (sourceTimeKernel N r t s).support := by
    simpa only [sourceProgram, PMF.bind_pure, sourceProgramStep] using hd
  exact ancestral_time_support N r t s hsroot htime

/-- The original naturally initialized completed experiment admits ANY finite
last cut. Expose enough of its same ancestral process, then use exact completion
with a constant tail bin. No cut-before-original-root restriction remains. -/
theorem actual_natural_arbitrary_last_cut (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (cut : ℝ) (tailTag : Tag)
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag) :
    let ops := compiledCalendarProgram N C H (originalGamma p) common
    let t : ℝ≥0 := Real.toNNReal (cut - (firstOriginalDate N C + (programDuration N ops : ℝ)))
    naturalCompletedJoint N C sample p r bin hbin ops =
      (naturalPastJoint N C sample p r bin hbin (ops ++ [.interval t])).bind
        (jointTailKernel N r tailTag) := by
  dsimp only
  generalize hops : compiledCalendarProgram N C H (originalGamma p) common = ops
  generalize ht : Real.toNNReal (cut -
    (firstOriginalDate N C + (programDuration N ops : ℝ))) = t
  rw [natural_completed_append_interval N C sample p r bin hbin ops t]
  have hroot (register : V → Bool) :
      ∀ d ∈ (sourceProgram N r (ops ++ [.interval t])
        (initialCode N sample register)).support, AncestralRoot N d := by
    intro d hd
    rw [← hops] at hd
    exact original_extended_ancestral_support N C sample H p common r register t hd
  have hcut := extend_beyond_cut N (firstOriginalDate N C) cut ops
  rw [ht] at hcut
  have hrow (register : V → Bool) :=
    actual_completed_joint_eq_gamma_tail N r bin hbin (ops ++ [.interval t])
      (initialCode N sample register) (hroot register)
      (firstOriginalDate N C) cut tailTag hcut htail
      (leafAgeMatrix N C sample)
  unfold naturalCompletedJoint naturalPastJoint
  rw [PMF.bind_bind]
  apply congrArg (PMF.bind (originalRegisterPMF N p))
  funext register
  exact hrow register

#print axioms completed_joint_append_interval
#print axioms natural_completed_append_interval
#print axioms extend_beyond_cut
#print axioms ancestral_time_support
#print axioms original_extended_ancestral_support
#print axioms actual_natural_arbitrary_last_cut
end UnifiedLean.G6.NaturalAncestralCutExtension
