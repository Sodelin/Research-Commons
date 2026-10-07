import ActualCalendarEndpointHistory

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED separate G6 original-calendar adapter. CutRefines contains only
finite nonnegative interval subdivisions and their composition. Its law is
proved from actual retained-clock renewal, never supplied as a premise.
Previously published author sources and current formal inputs stay fixed.
-/

namespace CloudG3.ActualObservationCutRefinement
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport GProgram.G2.SourceFiniteHistory
open UnifiedLean.G6.ProgramPrefix UnifiedLean.G6.HistoryPrefix UnifiedLean.G6.FiniteProbability
open CloudG3.ActualCalendarCutContext CloudG3.ActualFiniteCutJointLaw
open CloudG3.ActualCalendarEndpointHistory
open scoped Classical NNReal

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- A finite analytical subdivision derivation. No rule changes an original
boundary, inserts a register draw, or changes an interval's total duration. -/
inductive CutRefines (N : RootedBinary V E X) :
    List (ProgramStep N) → List (ProgramStep N) → Prop
  | refl (ops : List (ProgramStep N)) : CutRefines N ops ops
  | split (prefix suffix : List (ProgramStep N)) (t v : ℝ≥0) :
      CutRefines N (prefix ++ .interval (t + v) :: suffix)
        (prefix ++ .interval t :: .interval v :: suffix)
  | trans {a b c : List (ProgramStep N)} :
      CutRefines N a b → CutRefines N b c → CutRefines N a c

/-- Each rule is discharged by the actual full-joint interval law. -/
theorem cut_refines_actual_calendar_joint (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) {ops refined : List (ProgramStep N)}
    (href : CutRefines N ops refined) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) :
    calendarJoint N r bin hbin ops s offset B =
      calendarJoint N r bin hbin refined s offset B := by
  induction href with
  | refl ops => rfl
  | split prefix suffix t v =>
      exact calendar_joint_refinement_in_context N r bin hbin prefix suffix
        s offset t v B
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Original unrefined canonical Gamma equals the original source endpoint
history for its fixed-bin analytical subdivision. Refinement is a derivation
of legal source interval subdivisions, not an assumed Gamma equality. -/
theorem original_gamma_refined_endpoint_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (ops : List (ProgramStep N))
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hword : wordBinContract N bin word offset) :
    CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r bin hbin ops s offset M =
      (sourceHistoryLaw N r (physicalOps N word) s).map
        (endpointHistoryReadout N word s (fun a b => bin (M a b))) := by
  have he : CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r bin hbin
      ops s offset M = calendarJoint N r bin hbin ops s offset (fun a b => bin (M a b)) := by
    apply PMF.toMeasure_injective
    rw [CloudG3.CompleteCalendarJointLaw.calendar_joint_pmf_toMeasure,
      calendar_joint_toMeasure]
    rfl
  rw [he, cut_refines_actual_calendar_joint N r bin hbin href s offset
    (fun a b => bin (M a b))]
  exact actual_calendar_joint_endpoint_history N r bin hbin word s offset
    (fun a b => bin (M a b)) hword

/-- The bound applies to the original actual calendar after the actual
subdivision transport, with one reader of its full refined source history. -/
theorem original_gamma_refined_history_prefix_tv (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (K : ℕ)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hword : wordBinContract N bin word offset) :
    pmfTV (CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r bin hbin ops s offset M)
      ((finiteHistoryLaw N r K (physicalOps N word) s).map
        (endpointHistoryReadout N word s (fun a b => bin (M a b)))) ≤
      1 - (programMass (Copy := Copy) N r K (physicalOps N word)).toReal := by
  rw [original_gamma_refined_endpoint_history N r bin hbin ops word href s offset M hword]
  simpa only [PMF.pure_bind] using same_initial_joint_history_readout_tv N r K
    (physicalOps N word) (PMF.pure s)
    (endpointHistoryReadout N word s (fun a b => bin (M a b)))

#print axioms cut_refines_actual_calendar_joint
#print axioms original_gamma_refined_endpoint_history
#print axioms original_gamma_refined_history_prefix_tv

end CloudG3.ActualObservationCutRefinement
