import G2OriginalAbsoluteAges

/-!
One measurable joint topology/absolute-age observation of the actual path.
Contributor: dot (OpenAI), 6 October 2026.
Infinite or absent pair times retain an explicit false flag; their zero payload
is never interpreted as an age. Diagonal entries use original sampling dates.
The final master interpretation additionally binds this encoding to all actual
graft decorations; the law equality here is not by itself that final gate.
-/
namespace GProgram.G2.JointTimedObservation
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.ControlledTraceAssembly
open GProgram.G2.ChronologicalPathReadout GProgram.G2.RegisteredPathProjection
open GProgram.G2.EventualPathReadout GProgram.G2.ActualPairCoalescence
open GProgram.G2.RationalAgeReadout GProgram.G2.CalendarHistoryBinding
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.CalendarHistoryBinding.joinedMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable

abbrev TimedObservation (Copy : Type*) :=
  Option (Finset (UnrankedTree Copy)) × (Copy → Copy → Bool × ℝ)

noncomputable def finiteAbsoluteAge (offset : ℝ) (a : ℝ≥0∞) : Bool × ℝ :=
  if a = ⊤ then (false,0) else (true,offset+a.toReal)

lemma finite_absolute_age_measurable (offset : ℝ) : Measurable (finiteAbsoluteAge offset) := by
  exact Measurable.ite (measurableSet_singleton ⊤) measurable_const
    (measurable_const.prodMk (measurable_const.add measurable_id.ennreal_toReal))

noncomputable def timedObservation (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) (path : ℝ≥0 → JoinedIndex N sample keep) : TimedObservation Copy :=
  ((terminalPath path).map (fun q => unrankedForest q.val),fun x y =>
    if x ∈ keep ∧ y ∈ keep then
      if x = y then (true,C.age (N.leaf (sample x))) else
        finiteAbsoluteAge (firstOriginalDate N C) (rationalAge (fun q => sameBlock q.val x y) path)
    else (false,0))

lemma timed_observation_measurable (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) : Measurable (timedObservation N C sample keep) := by
  unfold timedObservation
  apply Measurable.prodMk
  · have ht : Measurable (terminalPath (Q := JoinedIndex N sample keep)) := terminal_path_measurable
    have hm : Measurable (fun z : Option (JoinedIndex N sample keep) =>
        z.map (fun q => unrankedForest q.val)) := measurable_of_countable _
    exact hm.comp ht
  · apply measurable_pi_lambda
    intro x
    apply measurable_pi_lambda
    intro y
    by_cases hxy : x ∈ keep ∧ y ∈ keep
    · by_cases he : x = y
      · simpa only [timedObservation,if_pos hxy,if_pos he] using
          (measurable_const : Measurable (fun _ : ℝ≥0 → JoinedIndex N sample keep => (true,C.age (N.leaf (sample x)))))
      · have hp : MeasurableSet {q : JoinedIndex N sample keep | sameBlock q.val x y} :=
          (measurable_of_countable (fun q : JoinedIndex N sample keep => sameBlock q.val x y)).setOf
        simpa only [if_pos hxy,if_neg he,Function.comp_def] using
          (finite_absolute_age_measurable (firstOriginalDate N C)).comp (rational_age_measurable _ hp)
    · simpa only [if_neg hxy] using (measurable_const : Measurable (fun _ : ℝ≥0 → JoinedIndex N sample keep => (false,(0 : ℝ))))

noncomputable def registeredTimedObservation (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) (z : (V → Bool) × (ℝ≥0 → JoinedIndex N sample keep)) :
    (V → Bool) × TimedObservation Copy := (z.1,timedObservation N C sample keep z.2)

lemma registered_timed_observation_measurable (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) : Measurable (registeredTimedObservation N C sample keep) :=
  measurable_fst.prodMk ((timed_observation_measurable N C sample keep).comp measurable_snd)

/-- Joint complete topology and absolute pair-age law, retaining the SAME
register and same chronological path on every original copy panel. -/
theorem actual_registered_joint_timed_observation_all_panels (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (ρ : PMF (V → Bool)) :
    (registeredTraceLaw N sample r ops ρ).map
      (registeredTimedObservation N C sample keep ∘ registeredChronologicalPath N ops ∘
        registeredPathObservation N sample (fun d => joinedProjection N keep (.inl d)) ops) =
    (registeredTraceLaw N (selectedSample sample keep) r ops ρ).map
      (registeredTimedObservation N C sample keep ∘ registeredChronologicalPath N ops ∘
        registeredPathObservation N (selectedSample sample keep) (fun d => joinedProjection N keep (.inr d)) ops) := by
  have h := congrArg (fun μ : Measure ((V → Bool) × (ℝ≥0 → JoinedIndex N sample keep)) =>
      μ.map (registeredTimedObservation N C sample keep))
    (actual_registered_chronological_path_all_panels N sample r keep ops ρ)
  rw [Measure.map_map (registered_timed_observation_measurable N C sample keep)
      ((registered_chronological_path_measurable N ops).comp (registered_path_observation_measurable N sample _ ops)),
    Measure.map_map (registered_timed_observation_measurable N C sample keep)
      ((registered_chronological_path_measurable N ops).comp (registered_path_observation_measurable N (selectedSample sample keep) _ ops))] at h
  exact h

#print axioms timed_observation_measurable
#print axioms actual_registered_joint_timed_observation_all_panels
end GProgram.G2.JointTimedObservation
