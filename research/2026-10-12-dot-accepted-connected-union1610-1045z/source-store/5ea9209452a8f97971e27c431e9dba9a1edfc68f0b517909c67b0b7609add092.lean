import G2ControlledTraceAssembly
import G2ActualChronologicalPathLaw

/-!
Original-register-preserving chronological path transport.
Contributor: dot (OpenAI), 7 October 2026. The original register is drawn once
and retained jointly with every path coordinate. The old completed-record
reader is used literally; its law is identified through proved gluing.
-/
namespace GProgram.G2.RegisteredPathProjection
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceInitializedCalendar
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.ControlledTraceAssembly GProgram.G2.CompletedPathProjection
open GProgram.G2.ChronologicalPathReadout GProgram.G2.ChronologicalGluing
open GProgram.G2.CompletedCalendarPathLaw GProgram.G2.ActualChronologicalPathLaw
open GProgram.G2.EpochPathProjection
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EpochPathProjection.joinedIndexMeasurable

noncomputable def registeredPathObservation (N : RootedBinary V E X) (sample : Copy → X)
    (f : Code N sample → Q) (ops : List (ProgramStep N))
    (z : RegisteredRecord N sample ops) : (V → Bool) × CompletedObservation Q ops.length :=
  (z.1,observeCompleted N f ops (initialCode N sample z.1) z.2)

lemma registered_path_observation_measurable (N : RootedBinary V E X) (sample : Copy → X)
    (f : Code N sample → Q) (ops : List (ProgramStep N)) :
    Measurable (registeredPathObservation N sample f ops) := by
  have hm : Measurable (fun z : (V → Bool) × CompleteCalendarRecord N sample ops =>
      observeCompleted N f ops (initialCode N sample z.1) z.2) :=
    measurable_from_prod_countable_right
      (fun reg => observe_completed_measurable N f ops (initialCode N sample reg))
  exact measurable_fst.prodMk hm

noncomputable def registeredChronologicalPath (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) (z : (V → Bool) × CompletedObservation Q ops.length) :
    (V → Bool) × (ℝ≥0 → Q) := (z.1,chronologicalPath N ops z.2)

lemma registered_chronological_path_measurable (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) : Measurable (registeredChronologicalPath N (Q := Q) ops) :=
  measurable_fst.prodMk ((chronological_path_measurable N ops).comp measurable_snd)

/-- The legacy completed observation's unclamped segment readers are used
only on their true interval interiors by the chronological map. -/
lemma actual_legacy_chronological_readout_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (completeCalendarTraceLaw N r ops s).map
      (chronologicalPath N ops ∘ observeCompleted N f ops s) =
      (completeCalendarTraceLaw N r ops s).map (actualChronologicalPath N f ops s) := by
  rw [actual_chronological_path_join_law,
    Measure.map_map (joined_chronological_path_measurable N ops)
      (observed_completed_measurable N f ops s)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (fun z =>
    (clamped_chronological_agrees N f ops s z.2.1
      (CompleteEpochPath.completePath N f z.1 z.2.2)).symm)

lemma actual_legacy_cross_carrier_path_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (completeCalendarTraceLaw N r ops s).map
      (chronologicalPath N ops ∘ observeCompleted N (fun z => joinedProjection N keep (.inl z)) ops s) =
    (completeCalendarTraceLaw N r ops d).map
      (chronologicalPath N ops ∘ observeCompleted N (fun z => joinedProjection N keep (.inr z)) ops d) := by
  rw [actual_legacy_chronological_readout_law,actual_legacy_chronological_readout_law,
    actual_cross_carrier_chronological_path_law N r keep ops s d hs]

/-- The full original register and all chronological path coordinates are
transported jointly. Empty panels retain that same register. -/
theorem actual_registered_chronological_path_all_panels (N : RootedBinary V E X)
    (sample : Copy → X) (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (ρ : PMF (V → Bool)) :
    (registeredTraceLaw N sample r ops ρ).map
      (registeredChronologicalPath N ops ∘
        registeredPathObservation N sample (fun z => joinedProjection N keep (.inl z)) ops) =
    (registeredTraceLaw N (selectedSample sample keep) r ops ρ).map
      (registeredChronologicalPath N ops ∘
        registeredPathObservation N (selectedSample sample keep)
          (fun z => joinedProjection N keep (.inr z)) ops) := by
  have hf := (registered_chronological_path_measurable N ops).comp
    (registered_path_observation_measurable N sample
      (fun z => joinedProjection N keep (.inl z)) ops)
  have hg := (registered_chronological_path_measurable N ops).comp
    (registered_path_observation_measurable N (selectedSample sample keep)
      (fun z => joinedProjection N keep (.inr z)) ops)
  rw [registeredTraceLaw,registeredTraceLaw,
    Measure.map_finset_sum' hf.aemeasurable,Measure.map_finset_sum' hg.aemeasurable]
  apply Finset.sum_congr rfl
  intro reg hreg
  rw [Measure.map_smul,Measure.map_smul]
  congr 1
  have hi : Measurable (fun z : CompleteCalendarRecord N sample ops => (reg,z)) :=
    measurable_const.prodMk measurable_id
  have hj : Measurable (fun z : CompleteCalendarRecord N (selectedSample sample keep) ops => (reg,z)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.map_map hf hi,Measure.map_map hg hj]
  have h := actual_legacy_cross_carrier_path_law N r keep ops
    (initialCode N sample reg) (initialCode N (selectedSample sample keep) reg)
    (actual_initial_copy_carrier_diagram N sample keep reg).symm
  have hm : Measurable (fun p : ℝ≥0 → JoinedIndex N sample keep => (reg,p)) :=
    measurable_const.prodMk measurable_id
  have ht := congrArg (fun μ : Measure (ℝ≥0 → JoinedIndex N sample keep) =>
      μ.map (fun p => (reg,p))) h
  rw [Measure.map_map hm ((chronological_path_measurable N ops).comp
      (observe_completed_measurable N _ ops (initialCode N sample reg))),
    Measure.map_map hm ((chronological_path_measurable N ops).comp
      (observe_completed_measurable N _ ops (initialCode N (selectedSample sample keep) reg)))] at ht
  exact ht

#print axioms registered_path_observation_measurable
#print axioms registered_chronological_path_measurable
#print axioms actual_legacy_chronological_readout_law
#print axioms actual_legacy_cross_carrier_path_law
#print axioms actual_registered_chronological_path_all_panels
end GProgram.G2.RegisteredPathProjection
