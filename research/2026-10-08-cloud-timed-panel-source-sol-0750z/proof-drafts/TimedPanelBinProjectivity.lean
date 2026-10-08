import NativeFiniteReaderMenu
import G5HiddenRegisterTimedProjectivity
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
Authored SOURCE/HAND adapter, compiler UNCHECKED/outside181.
REUSE: dot's actual timed G2 chronology/physical matrix/all-panel proof and
Astra G5's register-hidden consumer. New work is only measurable forward bins
and their exact binding to the existing actual native panel PMF.
No desired row/projectivity/chronology/finite-age law is an admission field.
-/
namespace CloudG6.TimedPanelBinProjectivity

open MeasureTheory ProbabilityTheory Filter Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G2.JointTimedObservation GProgram.G2.FaithfulTimedOutput
open GProgram.G2.LiteralTimedObservationPruning GProgram.G2.ActualTimedAllPanelLaw
open GProgram.G2.ControlledTraceAssembly GProgram.G2.ChronologicalPathReadout
open GProgram.G2.RegisteredPathProjection GProgram.G2.CompletedPathProjection
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G5.HiddenRegisterTimedProjectivity
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG6.NaturalCalendarPastAdmission CloudG6.NaturalPastCompleteObservation
open CloudG6.ActualPanelForestReadout CloudG6.NaturalPanelPhysicalAges
open CloudG6.ActualFiniteObservableRecord CloudG6.ActualSourceCorruptionClasses
open scoped Classical

universe u v w x y
variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.CalendarHistoryBinding.joinedMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable

/-- A total forward coarsening of the inherited timed output, on only literal
selected coordinates. The original faithful source theorem below DERIVES
true finite-age flags there; false payload zero is not asserted to be an age. -/
noncomputable def timedPanelBins (keep : Finset Copy) (bin : ℝ → Tag)
    (o : TimedObservation Copy) : RawPanelRecord keep Tag :=
  (o.1.getD ∅, fun a b => bin (o.2 a.val b.val).2)

theorem timed_panel_bins_measurable (keep : Finset Copy) (bin : ℝ → Tag)
    (hbin : Measurable bin) : Measurable (timedPanelBins keep bin) := by
  have hF : Measurable (fun o : TimedObservation Copy => o.1.getD ∅) :=
    (measurable_of_countable (fun q : Option (Finset (UnrankedTree Copy)) => q.getD ∅)).comp
      measurable_fst
  have hB (a b : PanelCopy keep) :
      Measurable (fun o : TimedObservation Copy => bin (o.2 a.val b.val).2) :=
    hbin.comp (((measurable_pi_apply b.val).comp
      ((measurable_pi_apply a.val).comp measurable_snd)).snd)
  apply measurable_to_countable'
  intro a
  change MeasurableSet {o : TimedObservation Copy | timedPanelBins keep bin o = a}
  simp only [timedPanelBins, Prod.ext_iff, funext_iff]
  apply MeasurableSet.inter (measurableSet_eq_fun hF measurable_const)
  apply Measurable.setOf
  apply Measurable.forall
  intro x
  apply Measurable.forall
  intro y
  exact (hB x y).eq measurable_const

/-- The inherited matrix initializer is literally c206 leafAgeMatrix. -/
theorem timed_matrix_panel_bins (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (bin : ℝ → Tag)
    (ops : List (ProgramStep N)) (keep : Finset Copy)
    (z : CompleteCalendarRecord N sample ops) :
    timedPanelBins keep bin (matrixObservation N keep (completeEnd N ops z)
      (completeMatrix N ops (initialCode N sample register) (firstOriginalDate N C)
        (fun a _ => C.age (N.leaf (sample a))) z)) =
      physicalPanelFields N C sample register bin ops keep z := by
  apply Prod.ext
  · rfl
  · funext a b
    simp [timedPanelBins, matrixObservation, physicalPanelFields,
      leafAgeMatrix, a.property, b.property]

/-- True finite-age flags for all actually selected pairs, diagonals included,
are DERIVED from the actual full original physical source, not assumed. -/
theorem actual_selected_finite_flags (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (keep : Finset Copy) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      ∀ a b : PanelCopy keep,
        ((timedObservation N C sample keep (chronologicalPath N
          (compiledCalendarProgram N C H gamma common)
          (observeCompleted N (fun d => joinedProjection N keep (.inl d))
            (compiledCalendarProgram N C H gamma common) (initialCode N sample register) z))).2
              a.val b.val).1 = true := by
  filter_upwards [actual_original_faithful_output N C sample register H gamma common r keep]
    with z hz
  intro a b
  rw [hz]
  simp [matrixObservation, a.property, b.property]

noncomputable def binnedRegisteredPanel (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (bin : ℝ → Tag) (keep : Finset Copy) (ops : List (ProgramStep N))
    (z : RegisteredRecord N sample ops) : RawPanelRecord keep Tag :=
  timedPanelBins keep bin (pruneTimedObservation keep
    (eraseRegister (fullReadout N C sample Finset.univ ops z)))

theorem binned_registered_panel_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (bin : ℝ → Tag) (hbin : Measurable bin)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    Measurable (binnedRegisteredPanel N C sample bin keep ops) :=
  (timed_panel_bins_measurable keep bin hbin).comp
    ((ordinary_prune_measurable keep).comp
      (erase_register_measurable.comp (full_readout_measurable N C sample Finset.univ ops)))

/-- SAME full trace, literal pruning and SAME physical matrix forward bins. -/
theorem actual_registered_binned_panel_physical (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (keep : Finset Copy) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      binnedRegisteredPanel N C sample bin keep (compiledCalendarProgram N C H gamma common)
        (register, z) = physicalPanelFields N C sample register bin
          (compiledCalendarProgram N C H gamma common) keep z := by
  filter_upwards [actual_original_faithful_output N C sample register H gamma common r Finset.univ]
    with z hz
  dsimp only [binnedRegisteredPanel, eraseRegister, fullReadout, registeredChronologicalPath,
    registeredPathObservation, registeredTimedObservation, Function.comp_apply, id_eq]
  rw [hz, prune_matrix_observation]
  exact timed_matrix_panel_bins N C sample register bin _ keep z

/-- The row premise of the original register-assembly helper is DERIVED from
the actual physical readout, not inserted as a desired equality field. -/
theorem actual_registered_binned_panel_row (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (keep : Finset Copy) :
    (completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)).map (fun z => binnedRegisteredPanel N C sample bin keep
        (compiledCalendarProgram N C H gamma common) (register, z)) =
      ((completedJoint N r bin hbin (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register) (firstOriginalDate N C)
        (fun a b => bin (leafAgeMatrix N C sample a b))).map
          (endpointPanelReadout N keep)).toMeasure := by
  exact (Measure.map_congr (actual_registered_binned_panel_physical N C sample register H
    gamma common r bin keep)).trans
      (initialized_panel_physical_source_law N C sample register r bin hbin _ keep).symm

/-- Exact natural joint panel PMF binds to inherited physical timed output.
The original register is drawn once and erased ONLY at the readout boundary. -/
theorem natural_panel_full_timed_binding (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (keep : Finset Copy) :
    ((naturalCompletedJoint N C sample p r bin hbin
      (compiledCalendarProgram N C H (originalGamma p) common)).map
        (endpointPanelReadout N keep)).toMeasure =
      ((naturalObservedFullLaw N C sample H p common r).map (pruneTimedObservation keep)).map
        (timedPanelBins keep bin) := by
  let ops := compiledCalendarProgram N C H (originalGamma p) common
  let K := fun register => (completedJoint N r bin hbin ops (initialCode N sample register)
    (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b))).map
      (endpointPanelReadout N keep)
  have hrow := registered_map_of_row_law N sample r ops (originalRegisterPMF N p)
    (binnedRegisteredPanel N C sample bin keep ops)
    (binned_registered_panel_measurable N C sample bin hbin keep ops) K
    (fun register => actual_registered_binned_panel_row N C sample register H
      (originalGamma p) common r bin hbin keep)
  have ht : ((naturalObservedFullLaw N C sample H p common r).map
      (pruneTimedObservation keep)).map (timedPanelBins keep bin) =
      ((originalRegisterPMF N p).bind K).toMeasure := by
    unfold naturalObservedFullLaw
    rw [Measure.map_map (ordinary_prune_measurable keep) erase_register_measurable,
      Measure.map_map (timed_panel_bins_measurable keep bin hbin)
        ((ordinary_prune_measurable keep).comp erase_register_measurable),
      Measure.map_map ((timed_panel_bins_measurable keep bin hbin).comp
        ((ordinary_prune_measurable keep).comp erase_register_measurable))
        (full_readout_measurable N C sample Finset.univ ops)]
    exact hrow
  unfold naturalCompletedJoint
  rw [PMF.map_bind]
  exact ht.symm

/-- Genuine JOINT forest/pair-bin equality with the separately initialized
smaller-Copy actual timed source. Chronology is reused from the actual G2/G5
law; it is not inferred from a topology marginal or consistency predicate. -/
theorem actual_natural_panel_bin_projectivity (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (keep : Finset Copy) :
    ((naturalCompletedJoint N C sample p r bin hbin
      (compiledCalendarProgram N C H (originalGamma p) common)).map
        (endpointPanelReadout N keep)).toMeasure =
      (naturalObservedSelectedLaw N C sample H p common r keep).map (timedPanelBins keep bin) := by
  rw [natural_panel_full_timed_binding,
    actual_natural_hidden_timed_all_panel_projectivity N C sample H p common r keep]

/-- Instantiates the literal finite native panel observer, keeping original
source/sample/bin/mode/parents/rates and the SAME register prior. -/
theorem native_finite_panel_bin_projectivity (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    {sample : Copy → X} (s : OriginalParameters.{u,v,w,x} Copy X sample) (keep : Finset Copy) :
    (((nativeFiniteLaw mode bin hbin s).map (finitePanelReadout keep)).map Subtype.val).toMeasure =
      (naturalObservedSelectedLaw s.original.network s.original.calendar sample s.registry
        s.inheritance (fun _ => mode) s.rates keep).map (timedPanelBins keep bin) := by
  rw [native_finite_panel_source]
  exact actual_natural_panel_bin_projectivity s.original.network s.original.calendar sample
    s.registry s.inheritance (fun _ => mode) s.rates bin hbin keep

end CloudG6.TimedPanelBinProjectivity
