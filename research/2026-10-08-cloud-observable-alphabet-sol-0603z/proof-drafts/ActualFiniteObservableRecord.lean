import SourceIndependentForestAlphabet
import ActualSourceCorruptionClasses

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
EXPERIMENTAL SOURCE/HAND; every new body compiler UNCHECKED/outside179.
Instantiates the original-source class's finite reader from fixed external
Copy/Tag and ACTUAL valid forests. No hidden IDs/register enter the output.
Neither desired source law nor arbitrary tree injection is a premise.
Biological full-menu/pruning/ancestral observation identification is separate.
-/
namespace CloudG6.ActualFiniteObservableRecord

open ProbabilityTheory Nanuq.Source GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep
open CloudG3.ActualCutJointLaw CloudG6.ActualObservationCorruption
open CloudG6.NaturalPastCompleteObservation
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open CloudG6.ActualSourceCorruptionClasses CloudG6.SourceIndependentForestAlphabet
open scoped Classical

universe u v w x y
variable {Copy : Type w} {X : Type x} {Tag : Type y}
variable [Fintype Copy] [DecidableEq Copy] [Fintype X]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
variable {sample : Copy → X}

/-- Every admitted original Code supplies the graph-independent proper
forest; no probabilistic support/equality field is necessary for admission. -/
theorem actual_observed_record_proper
    (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (q : TaggedEndpoint (Tag := Tag) s.original.network sample) :
    ProperForest (observedRecord s q).1 :=
  actual_source_full_forest_proper (state q.1) q.1.property.forest

noncomputable def boundedObservedRecord
    (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (q : TaggedEndpoint (Tag := Tag) s.original.network sample) :
    FiniteObservedRecord Copy Tag :=
  (⟨(observedRecord s q).1, actual_observed_record_proper s q⟩, (observedRecord s q).2)

theorem boundedObservedRecord_forget
    (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (q : TaggedEndpoint (Tag := Tag) s.original.network sample) :
    forgetFiniteRecord (boundedObservedRecord s q) = observedRecord s q := rfl

theorem actual_observable_finite_reader
    (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (q : TaggedEndpoint (Tag := Tag) s.original.network sample) :
    finiteRecordReader (observedRecord s q) = some (boundedObservedRecord s q) := by
  rw [← boundedObservedRecord_forget s q]
  exact finiteRecordReader_forget (boundedObservedRecord s q)

/-- The entire SAME actual completed original source is read into one fixed
Copy/Tag finite alphabet across arbitrary finite hidden graphs. -/
noncomputable def nativeFiniteLaw (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) : PMF (FiniteObservedRecord Copy Tag) :=
  actualCompiledObservation s.original.network s.original.calendar sample
    s.registry s.inheritance (fun _ => mode) s.rates bin hbin (boundedObservedRecord s)

/-- Forgetting proof membership recovers EXACTLY the original raw observable
payload law. Finiteness neither removes trees/tags nor reveals hidden data. -/
theorem actual_native_finite_record_forget (mode : Bool) (bin : ℝ → Tag)
    (hbin : Measurable bin) (s : OriginalParameters.{u,v,w,x} Copy X sample) :
    (nativeFiniteLaw mode bin hbin s).map forgetFiniteRecord =
      (naturalCompletedJoint s.original.network s.original.calendar sample
        s.inheritance s.rates bin hbin
        (compiledCalendarProgram s.original.network s.original.calendar s.registry
          (originalGamma s.inheritance) (fun _ => mode))).map (observedRecord s) := by
  unfold nativeFiniteLaw actualCompiledObservation
  rw [PMF.map_comp]
  apply congrArg (PMF.map · _)
  funext q
  exact boundedObservedRecord_forget s q

/-- Instantiates the existing source-class family with the derived finite
observable-only reader. Internal registers are still drawn/reused by the
source law; this biological reader does not expose or resample their values. -/
theorem actual_native_law_finite_reader (mode : Bool) (bin : ℝ → Tag)
    (hbin : Measurable bin) (s : OriginalParameters.{u,v,w,x} Copy X sample) :
    nativeLaw mode bin hbin finiteRecordReader s = (nativeFiniteLaw mode bin hbin s).map some := by
  unfold nativeLaw nativeFiniteLaw actualCompiledObservation
  rw [PMF.map_comp]
  apply congrArg (PMF.map · _)
  funext q
  exact actual_observable_finite_reader s q

/-- Invalid unrestricted payloads are outside the actual source image. -/
theorem actual_native_reader_invalid_zero (mode : Bool) (bin : ℝ → Tag)
    (hbin : Measurable bin) (s : OriginalParameters.{u,v,w,x} Copy X sample) :
    nativeLaw mode bin hbin finiteRecordReader s none = 0 := by
  rw [actual_native_law_finite_reader, PMF.map_apply]
  simp

end CloudG6.ActualFiniteObservableRecord
