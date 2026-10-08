import TaggedSourceIteration
import NaturalCalendarPastAdmission

/-!
Contributor: Cloud Sol /root/source_backend_review_sol, 2026-10-08.
EXPERIMENTAL/UNCHECKED proof-only consumer, outside frozen176/179 inputs.
Imports pin TaggedSourceIteration69ac and selected NaturalCalendarPastAdmission
c206, plus their unchanged original clock/calendar providers. No compiler run.
The literal SAME physical bin record and the naturally initialized joint past
are read through the full original-Location tagged forest and SAME register.
No desired row, law, decoder correctness or entering independence is an input.
This identifies native original source/count readouts, not Python tables or a
complete backend/marked-path law. Copy cap/normalizer are the original ones.
-/
namespace CloudG6.NaturalOneBinForestCount

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.ChronologicalPathReadout
open UnifiedLean.G6.BinHistory
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG3.ActualCalendarEndpointHistory
open CloudG6.TaggedSourceIteration CloudG6.NaturalCalendarPastAdmission
open scoped Classical NNReal

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- All original node/edge/root Locations and the full original register.
Only current representative IDs and recursive child order are quotiented. -/
abbrev ForestRecord (V : Type u) (E : Type v) (Copy : Type w) (Tag : Type y) :=
  (Location V E → Finset (Quotient (taggedTreeSetoid Copy Tag))) × (V → Bool)

/-- A discrete observation carrier; it does not assert all binary trees are
finite in number or contract equal-tag grafts. -/
local instance forestRecordMeasurable :
    MeasurableSpace (ForestRecord V E Copy Tag) := ⊤

/-- Concrete original-bank count mixture with a derived endpoint tag update.
Mean is globalClockRate at EXACT original card Copy, with all original rates.
The input Code and old tags stay joint; no new register draw occurs. -/
noncomputable def oneBinForestCount (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (h : ℝ≥0)
    (q : TaggedCode N sample Tag) : PMF (ForestRecord V E Copy Tag) :=
  (countPMF (globalClockRate (Copy := Copy) r * h)).bind (fun k =>
    (sourceIteration N r k q.1).map (fun d =>
      forestReadout N (d,tagUpdate N q.1 d tag q.2)))

theorem forest_readout_measurable (N : RootedBinary V E X) {sample : Copy → X} :
    Measurable (forestReadout (Tag := Tag) N (sample := sample)) :=
  measurable_of_countable _

/-- PMF map/bind algebra on the unchanged original Poisson/source kernel. -/
theorem source_time_forest_count (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (h : ℝ≥0)
    (q : TaggedCode N sample Tag) :
    (sourceTimeKernel N r h q.1).map (fun d =>
      forestReadout N (d,tagUpdate N q.1 d tag q.2)) = oneBinForestCount N r tag h q := by
  rw [sourceTimeKernel,PMF.map_bind]
  rfl

/-- SAME actual literal marked record, including inactive padding and zero
duration. The inherited clock/fold/source-row theorem derives the law; the
only bin premise is the physical open-interval date condition. -/
theorem actual_literal_one_bin_forest_count [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (s : Code N sample)
    (offset : ℝ) (h : ℝ≥0) (tag : Tag) (B : Copy → Copy → Tag)
    (hconst : ∀ a : ℝ, offset < a → a < offset+(h : ℝ) → bin a = tag) :
    (actualMarkedTraceLaw N r (Fintype.card Copy) s (h : ℝ)).map
        (forestReadout N ∘ tailTraceReadout N bin s offset B) =
      (oneBinForestCount N r tag h (s,B)).toMeasure := by
  rw [← Measure.map_map (forest_readout_measurable N)
        (tail_trace_readout_measurable N bin hbin s offset B),
    actual_interval_joint_source_row N r bin hbin s offset h tag B hconst,
    PMF.toMeasure_map _ _ (forest_readout_measurable N),PMF.map_comp]
  change ((sourceTimeKernel N r h s).map (fun d =>
    forestReadout N (d,tagUpdate N s d tag B))).toMeasure = _
  rw [source_time_forest_count]

/-- Equivalent finite actual-segment PMF consumer. Every node/outside tree
and all original register coordinates are included in forestReadout. -/
theorem actual_segment_one_bin_forest_count [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (s : Code N sample)
    (offset : ℝ) (h : ℝ≥0) (tag : Tag) (B : Copy → Copy → Tag)
    (hconst : ∀ a : ℝ, offset < a → a < offset+(h : ℝ) → bin a = tag) :
    (segmentJoint N r bin hbin (.interval h) s offset B).map (forestReadout N) =
      oneBinForestCount N r tag h (s,B) := by
  rw [actual_segment_endpoint_tag_row N r bin hbin (.interval h) tag s offset B hconst,
    PMF.map_comp]
  change (sourceTimeKernel N r h s).map (fun d =>
    forestReadout N (d,tagUpdate N s d tag B)) = _
  exact source_time_forest_count N r tag h (s,B)

/-- Substantive natural-past continuation consumer. The entering joint law
comes from ORIGINAL leaf ages, once-drawn native registers and actual clock
calendar records; no desired entering law/independence is a caller field.
Past boundaries/current-owner/COMMON choices are preserved in ops, not erased.
The physical time is exactly firstOriginalDate + past programDuration.
An actual initialized full-guard prefix must be used for a physical guard
application; this theorem does not replace the agenda/support proof. -/
theorem actual_natural_past_one_bin_forest_count [Nonempty Copy]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (h : ℝ≥0) (tag : Tag)
    (hconst : ∀ a : ℝ,
      firstOriginalDate N C+(programDuration N ops : ℝ) < a →
      a < firstOriginalDate N C+(programDuration N ops : ℝ)+(h : ℝ) → bin a = tag) :
    (naturalPastJoint N C sample p r bin hbin (ops ++ [.interval h])).map
        (forestReadout N) =
      (naturalPastJoint N C sample p r bin hbin ops).bind
        (oneBinForestCount N r tag h) := by
  rw [actual_natural_past_append N C sample p r bin hbin ops [.interval h],PMF.map_bind]
  apply congrArg (PMF.bind (naturalPastJoint N C sample p r bin hbin ops))
  funext q
  rw [calendar_joint_single]
  exact actual_segment_one_bin_forest_count N r bin hbin q.1
    (firstOriginalDate N C+(programDuration N ops : ℝ)) h tag q.2 hconst

end CloudG6.NaturalOneBinForestCount
