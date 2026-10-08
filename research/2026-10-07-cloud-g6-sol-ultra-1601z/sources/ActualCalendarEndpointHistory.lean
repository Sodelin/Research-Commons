import ActualFiniteCutJointLaw
import UnifiedLean.G6.HistoryPrefix

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED separate actual Gamma/history consumer. The entering matrix is
carried once; original source kernels, boundaries, bank and endpoint Codes
are unchanged. Only auxiliary fixed-bin labels are added to the readout.
No Gamma probabilities, source law or solver/backend equality are assumed.
-/

namespace CloudG3.ActualCalendarEndpointHistory
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourcePoissonKernel
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.SourceFiniteHistory GProgram.G2.CalendarDecoration
open UnifiedLean.G6.BinHistory UnifiedLean.G6.BinFold
open UnifiedLean.G6.ProgramPrefix UnifiedLean.G6.FiniteProbability UnifiedLean.G6.HistoryPrefix
open CloudG3.LiteralSameBinTrace CloudG3.ActualCutJointLaw CloudG3.ActualTailBinRow
open CloudG3.ActualCalendarCutContext CloudG3.ActualFiniteCutJointLaw
open scoped Classical NNReal

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

def physicalOps (N : RootedBinary V E X) (word : List (ProgramStep N × Tag)) :
    List (ProgramStep N) := word.map Prod.fst

noncomputable def endpointStepTags (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (tag : Tag) (s d : Code N sample) (B : Copy → Copy → Tag) :
    Copy → Copy → Tag := match op with
  | .interval _ => tagUpdate N s d tag B
  | .boundary _ => B

/-- Boundary labels are unused readout metadata; no new biological boundary
or COMMON register draw is introduced. Only interval interiors need a bin. -/
noncomputable def stepBinContract (N : RootedBinary V E X) (bin : ℝ → Tag)
    (offset : ℝ) (op : ProgramStep N) (tag : Tag) : Prop := match op with
  | .interval h => ∀ a : ℝ, offset < a → a < offset + (h : ℝ) → bin a = tag
  | .boundary _ => True

noncomputable def wordBinContract (N : RootedBinary V E X) (bin : ℝ → Tag) :
    List (ProgramStep N × Tag) → ℝ → Prop
  | [], _ => True
  | q :: word, offset => stepBinContract N bin offset q.1 q.2 ∧
      wordBinContract N bin word (segmentOffset N q.1 offset)

/-- Deterministic endpoint-history readout. The supplied initial Code/matrix
is read once; every original endpoint genealogy is retained in the history. -/
noncomputable def endpointHistoryReadout (N : RootedBinary V E X) {sample : Copy → X} :
    (word : List (ProgramStep N × Tag)) → Code N sample → (Copy → Copy → Tag) →
      (Fin (physicalOps N word).length → Code N sample) → TaggedEndpoint (Tag := Tag) N sample
  | [], s, B, _ => (s, B)
  | q :: word, s, B, h => by
      change (Fin ((physicalOps N word).length + 1) → Code N sample) at h
      exact endpointHistoryReadout N word (h 0)
        (endpointStepTags N q.1 q.2 s (h 0) B) (Fin.tail h)

/-- Actual fixed-bin interval row at full Copy cap, derived from the verified
SAME-clock fold and the original unconditional raw endpoint source law. -/
theorem actual_interval_joint_source_row (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (s : Code N sample) (offset : ℝ) (h : ℝ≥0)
    (tag : Tag) (B : Copy → Copy → Tag)
    (hconst : ∀ a : ℝ, offset < a → a < offset + (h : ℝ) → bin a = tag) :
    (actualMarkedTraceLaw N r (Fintype.card Copy) s (h : ℝ)).map
        (tailTraceReadout N bin s offset B) =
      ((sourceTimeKernel N r h s).map (fun d => (d, tagUpdate N s d tag B))).toMeasure := by
  let u : Code N sample → TaggedEndpoint (Tag := Tag) N sample := fun d => (d, tagUpdate N s d tag B)
  have hu : Measurable u := measurable_of_countable _
  have hm := marked_trace_measurable N (Fintype.card Copy) s (h : ℝ)
  calc
    _ = (currentPairClockMeasure N r s).map
        ((tailTraceReadout N bin s offset B) ∘ literalMarkedTrace N (Fintype.card Copy) (h : ℝ) s) := by
      rw [actualMarkedTraceLaw,
        Measure.map_map (tail_trace_readout_measurable N bin hbin s offset B) hm]
    _ = ((actualMarkedTraceLaw N r (Fintype.card Copy) s (h : ℝ)).map
        (fun z => traceEndpoint N (Fintype.card Copy) s z.2)).map u := by
      rw [actualMarkedTraceLaw, Measure.map_map (raw_tail_endpoint_measurable N s) hm,
        Measure.map_map hu ((raw_tail_endpoint_measurable N s).comp hm)]
      apply Measure.map_congr
      filter_upwards [actual_same_bin_endpoint_fold N r s offset (h : ℝ) bin tag hconst] with c hc
      exact Prod.ext rfl (hc (Fintype.card Copy) B)
    _ = ((sourceTimeKernel N r h s).toMeasure).map u := by
      rw [actual_trace_endpoint_source_law N r s h]
    _ = _ := PMF.toMeasure_map u (sourceTimeKernel N r h s) hu

/-- Every observed row comes from the original actual segment: boundaries
retain old tags, and intervals use their original physical bank. -/
theorem actual_segment_endpoint_tag_row (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (op : ProgramStep N) (tag : Tag)
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag)
    (hconst : stepBinContract N bin offset op tag) :
    segmentJoint N r bin hbin op s offset B =
      (sourceProgramStep N r op s).map
        (fun d => (d, endpointStepTags N op tag s d B)) := by
  apply PMF.toMeasure_injective
  cases op with
  | interval h =>
      rw [interval_segment_joint_toMeasure]
      exact actual_interval_joint_source_row N r bin hbin s offset h tag B hconst
  | boundary b =>
      rw [segment_joint_toMeasure, actualSegmentLaw,
        Measure.map_map (segment_readout_measurable N bin hbin (.boundary b) s offset B)
          (boundary_record_measurable N),
        PMF.toMeasure_map _ _ (measurable_of_countable _)]
      rfl

/-- This identifies ACTUAL Gamma with a deterministic reader of the original
joint endpoint history. Gamma probabilities are never supplied as an input. -/
theorem actual_calendar_joint_endpoint_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag)
    (hword : wordBinContract N bin word offset) :
    calendarJoint N r bin hbin (physicalOps N word) s offset B =
      (sourceHistoryLaw N r (physicalOps N word) s).map (endpointHistoryReadout N word s B) := by
  induction word generalizing s offset B with
  | nil =>
      change calendarJoint N r bin hbin [] s offset B =
        (historyLaw (sourceProgramStep N r) [] s).map (fun _ => (s, B))
      rw [calendar_joint_nil, historyLaw, PMF.pure_map]
  | cons q word ih =>
      have hh : stepBinContract N bin offset q.1 q.2 := hword.1
      have ht : wordBinContract N bin word (segmentOffset N q.1 offset) := hword.2
      have he (d : Code N sample) :
          (((sourceHistoryLaw N r (physicalOps N word) d).map (Fin.cons d)).map
            (endpointHistoryReadout N (q :: word) s B)) =
          (sourceHistoryLaw N r (physicalOps N word) d).map
            (endpointHistoryReadout N word d (endpointStepTags N q.1 q.2 s d B)) := by
        rw [PMF.map_comp]
        congr 1
        funext z
        simp only [Function.comp_def, endpointHistoryReadout, Fin.cons_zero, Fin.tail_cons]
      calc
        _ = (sourceProgramStep N r q.1 s).bind (fun d =>
            calendarJoint N r bin hbin (physicalOps N word) d (segmentOffset N q.1 offset)
              (endpointStepTags N q.1 q.2 s d B)) := by
          change calendarJoint N r bin hbin (q.1 :: physicalOps N word) s offset B = _
          rw [calendar_joint_cons, actual_segment_endpoint_tag_row N r bin hbin q.1 q.2
            s offset B hh, PMF.bind_map]
          rfl
        _ = (sourceProgramStep N r q.1 s).bind (fun d =>
            (sourceHistoryLaw N r (physicalOps N word) d).map
              (endpointHistoryReadout N word d (endpointStepTags N q.1 q.2 s d B))) := by
          apply congrArg (PMF.bind (sourceProgramStep N r q.1 s))
          funext d
          exact ih d (segmentOffset N q.1 offset) (endpointStepTags N q.1 q.2 s d B) ht
        _ = _ := by
          change _ = ((sourceProgramStep N r q.1 s).bind (fun d =>
            (sourceHistoryLaw N r (physicalOps N word) d).map (Fin.cons d))).map
              (endpointHistoryReadout N (q :: word) s B)
          rw [PMF.map_bind]
          simp_rw [he]

/-- The verified one-JOINT-history prefix error now applies to ACTUAL Gamma,
using the same full Code/tag reader and supplied entering matrix. -/
theorem actual_calendar_joint_history_prefix_tv (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (K : ℕ)
    (bin : ℝ → Tag) (hbin : Measurable bin) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag)
    (hword : wordBinContract N bin word offset) :
    pmfTV (calendarJoint N r bin hbin (physicalOps N word) s offset B)
      ((finiteHistoryLaw N r K (physicalOps N word) s).map
        (endpointHistoryReadout N word s B)) ≤
      1 - (programMass (Copy := Copy) N r K (physicalOps N word)).toReal := by
  rw [actual_calendar_joint_endpoint_history N r bin hbin word s offset B hword]
  simpa only [PMF.pure_bind] using same_initial_joint_history_readout_tv N r K
    (physicalOps N word) (PMF.pure s) (endpointHistoryReadout N word s B)

/-- Canonical principal Gamma, with the original real matrix binned once,
is the same actual pushforward as calendarJoint. This identifies its law
with the original full endpoint history rather than a supplied table. -/
theorem actual_original_gamma_endpoint_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hword : wordBinContract N bin word offset) :
    CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r bin hbin
        (physicalOps N word) s offset M =
      (sourceHistoryLaw N r (physicalOps N word) s).map
        (endpointHistoryReadout N word s (fun a b => bin (M a b))) := by
  have he : CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r bin hbin
      (physicalOps N word) s offset M =
      calendarJoint N r bin hbin (physicalOps N word) s offset (fun a b => bin (M a b)) := by
    apply PMF.toMeasure_injective
    rw [CloudG3.CompleteCalendarJointLaw.calendar_joint_pmf_toMeasure,
      calendar_joint_toMeasure]
    rfl
  rw [he]
  exact actual_calendar_joint_endpoint_history N r bin hbin word s offset
    (fun a b => bin (M a b)) hword

/-- The actual canonical Gamma inherits the already verified single-history
finite-prefix bound after the source-connected identification above. -/
theorem actual_original_gamma_history_prefix_tv (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (K : ℕ)
    (bin : ℝ → Tag) (hbin : Measurable bin) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hword : wordBinContract N bin word offset) :
    pmfTV (CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r bin hbin
        (physicalOps N word) s offset M)
      ((finiteHistoryLaw N r K (physicalOps N word) s).map
        (endpointHistoryReadout N word s (fun a b => bin (M a b)))) ≤
      1 - (programMass (Copy := Copy) N r K (physicalOps N word)).toReal := by
  rw [actual_original_gamma_endpoint_history N r bin hbin word s offset M hword]
  simpa only [PMF.pure_bind] using same_initial_joint_history_readout_tv N r K
    (physicalOps N word) (PMF.pure s)
    (endpointHistoryReadout N word s (fun a b => bin (M a b)))

#print axioms actual_interval_joint_source_row
#print axioms actual_segment_endpoint_tag_row
#print axioms actual_calendar_joint_endpoint_history
#print axioms actual_calendar_joint_history_prefix_tv
#print axioms actual_original_gamma_endpoint_history
#print axioms actual_original_gamma_history_prefix_tv

end CloudG3.ActualCalendarEndpointHistory
