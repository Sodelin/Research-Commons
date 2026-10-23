import G2LiteralTimedObservationPruning

/-!
Actual original-calendar timed genealogy all-panel law under literal pruning.
Contributor: dot (OpenAI), 6 October 2026.
The registers are drawn once. The physical natural and controlled instances
use exactly the admitted original compiler and fixed-ID controls.
-/
namespace GProgram.G2.ActualTimedAllPanelLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.OriginalFixedIDControls
open GProgram.G2.JointTimedObservation GProgram.G2.FaithfulTimedOutput
open GProgram.G2.LiteralTimedObservationPruning GProgram.G2.ControlledTraceAssembly
open GProgram.G2.ChronologicalPathReadout GProgram.G2.RegisteredPathProjection
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompletedPathProjection
open GProgram.G2.CompleteDecoration
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.CalendarHistoryBinding.joinedMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable

deriving instance Encodable for GProgram.SourceForest.Genealogy
instance genealogyCountable : Countable (Genealogy Copy) := by
  letI : Encodable Copy := Encodable.ofCountable Copy
  infer_instance

noncomputable def fullReadout (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) (ops : List (ProgramStep N)) :=
  registeredTimedObservation N C sample keep ∘ registeredChronologicalPath N ops ∘
    registeredPathObservation N sample (fun d => joinedProjection N keep (.inl d)) ops

noncomputable def smallReadout (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) (ops : List (ProgramStep N)) :=
  registeredTimedObservation N C sample keep ∘ registeredChronologicalPath N ops ∘
    registeredPathObservation N (selectedSample sample keep) (fun d => joinedProjection N keep (.inr d)) ops

noncomputable def pruneRegistered (keep : Finset Copy) (z : (V → Bool) × TimedObservation Copy) :=
  (z.1,pruneTimedObservation keep z.2)

lemma full_readout_measurable (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) (ops : List (ProgramStep N)) :
    Measurable (fullReadout N C sample keep ops) :=
  (registered_timed_observation_measurable N C sample keep).comp
    ((registered_chronological_path_measurable N ops).comp (registered_path_observation_measurable N sample _ ops))

lemma prune_registered_measurable (keep : Finset Copy) : Measurable (pruneRegistered (V := V) keep) := by
  apply measurable_fst.prodMk
  apply Measurable.prodMk
  · exact (measurable_of_countable (fun o : Option (Finset (UnrankedTree Copy)) => o.map (pruneForest keep))).comp measurable_snd.fst
  · apply measurable_pi_lambda
    intro x
    apply measurable_pi_lambda
    intro y
    by_cases h : x ∈ keep ∧ y ∈ keep
    · simpa only [pruneTimedObservation,if_pos h,Function.comp_def] using
        (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd.snd)
    · simpa only [pruneTimedObservation,if_neg h] using
        (measurable_const : Measurable (fun _ : (V → Bool) × TimedObservation Copy => (false,(0 : ℝ))))

/-- Literal timed pruning commutes almost surely with the actual source
readout. The full and selected observations come from the same trace. -/
theorem actual_registered_pruning_commutes (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (ρ : PMF (V → Bool)) (keep : Finset Copy) :
    ∀ᵐ z ∂registeredTraceLaw N sample r (compiledCalendarProgram N C H gamma common) ρ,
      pruneRegistered keep (fullReadout N C sample Finset.univ (compiledCalendarProgram N C H gamma common) z) =
        fullReadout N C sample keep (compiledCalendarProgram N C H gamma common) z := by
  let ops := compiledCalendarProgram N C H gamma common
  have hf := (prune_registered_measurable (V := V) keep).comp (full_readout_measurable N C sample Finset.univ ops)
  have hg := full_readout_measurable N C sample keep ops
  have hm : MeasurableSet {z | (pruneRegistered keep ∘ fullReadout N C sample Finset.univ ops) z =
      fullReadout N C sample keep ops z} := by
    have he : ∀ a b : (V → Bool) × TimedObservation Copy, a = b ↔
        a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ ∀ x y, (a.2.2 x y).1 = (b.2.2 x y).1 ∧
          (a.2.2 x y).2 = (b.2.2 x y).2 := by
      intro a b
      simp only [Prod.ext_iff,funext_iff]
    simp only [he]
    apply MeasurableSet.inter (measurableSet_eq_fun hf.fst hg.fst)
    apply MeasurableSet.inter (measurableSet_eq_fun hf.snd.fst hg.snd.fst)
    apply Measurable.setOf
    apply Measurable.forall
    intro x
    apply Measurable.forall
    intro y
    have hfx := (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hf.snd.snd)
    have hgx := (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hg.snd.snd)
    exact (hfx.fst.eq hgx.fst).and (hfx.snd.eq hgx.snd)
  rw [registeredTraceLaw,ae_finsetSum_measure_iff]
  intro reg _
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
  filter_upwards [actual_original_faithful_output N C sample reg H gamma common r Finset.univ,
    actual_original_faithful_output N C sample reg H gamma common r keep] with z hu hk
  apply Prod.ext
  · rfl
  · change pruneTimedObservation keep (timedObservation N C sample Finset.univ _) = timedObservation N C sample keep _
    dsimp only [registeredChronologicalPath,registeredPathObservation,Function.comp_apply,id_eq]
    change pruneTimedObservation keep (timedObservation N C sample Finset.univ
      (chronologicalPath N (compiledCalendarProgram N C H gamma common) (observeCompleted N _ _ _ z))) = _
    rw [hu,hk,prune_matrix_observation]

/-- Complete actual timed all-panel law, including empty and singleton panels,
with no path equality, chronology or finite-age admission assumptions. -/
theorem actual_registered_timed_all_panel_projectivity (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (ρ : PMF (V → Bool)) (keep : Finset Copy) :
    ((registeredTraceLaw N sample r (compiledCalendarProgram N C H gamma common) ρ).map
      (fullReadout N C sample Finset.univ (compiledCalendarProgram N C H gamma common))).map (pruneRegistered keep) =
    (registeredTraceLaw N (selectedSample sample keep) r (compiledCalendarProgram N C H gamma common) ρ).map
      (smallReadout N C sample keep (compiledCalendarProgram N C H gamma common)) := by
  rw [Measure.map_map (prune_registered_measurable keep) (full_readout_measurable N C sample Finset.univ _)]
  exact (Measure.map_congr (actual_registered_pruning_commutes N C sample H gamma common r ρ keep)).trans
    (actual_registered_joint_timed_observation_all_panels N C sample keep r _ ρ)

/-- Exact admitted natural source instance. -/
theorem actual_natural_complete_timed_all_panel_projectivity (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy) :
    ((originalTimedTraceLaw N C sample H p common r).map
      (fullReadout N C sample Finset.univ (compiledCalendarProgram N C H (originalGamma p) common))).map (pruneRegistered keep) =
    (originalTimedTraceLaw N C (selectedSample sample keep) H p common r).map
      (smallReadout N C sample keep (compiledCalendarProgram N C H (originalGamma p) common)) :=
  actual_registered_timed_all_panel_projectivity N C sample H (originalGamma p) common r (originalRegisterPMF N p) keep

/-- Exact fixed-original-ID masks, including their bypassed natural coins. -/
theorem actual_controlled_complete_timed_all_panel_projectivity (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) (keep : Finset Copy) :
    ((controlledTimedTraceLaw N C sample H p common r mask).map
      (fullReadout N C sample Finset.univ (controlledCalendarProgram N C H p common mask))).map (pruneRegistered keep) =
    (controlledTimedTraceLaw N C (selectedSample sample keep) H p common r mask).map
      (smallReadout N C sample keep (controlledCalendarProgram N C H p common mask)) :=
  actual_registered_timed_all_panel_projectivity N C sample H (controlledGamma p mask) (controlledMode common mask)
    r (originalRegisterPMF N p) keep

#print axioms actual_natural_complete_timed_all_panel_projectivity
#print axioms actual_controlled_complete_timed_all_panel_projectivity
end GProgram.G2.ActualTimedAllPanelLaw
