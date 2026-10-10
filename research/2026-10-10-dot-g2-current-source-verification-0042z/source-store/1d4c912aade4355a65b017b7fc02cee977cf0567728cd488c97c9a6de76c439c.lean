import UnifiedLean.Source.SourceCrossCarrierProgram

/-!
# Same ORIGINAL natural calendar and eventual full/small source law

Contributor: dot, 2026-10-02. Instantiates the proved actual programme
comparison at separately constructed original-copy and selected-copy initial
states, with the SAME once-drawn original hybrid register prior. Actual
ancestral limits then derive the completed-law comparison, not an assumed
cross-source terminal equation.
-/
namespace UnifiedLean.Source.SourceCrossCarrierNatural
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Filter
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceNaturalCompletedLimit
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierProgram
open scoped Classical NNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- SAME original register prior and actual independently initialized source
carriers, for every original operation programme. No initial-view premise is
required: it is discharged by the actual original source constructors. -/
theorem original_initialized_register_program_law (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    ((originalRegisterPMF N p).bind (fun register => sourceProgram N r ops
      (initialCode N sample register))).map (fun d => joinedProjection N keep (.inl d)) =
    ((originalRegisterPMF N p).bind (fun register => sourceProgram N r ops
      (initialCode N (selectedSample sample keep) register))).map
        (fun d => joinedProjection N keep (.inr d)) := by
  rw [PMF.map_bind,PMF.map_bind]
  congr 1
  funext register
  exact actual_cross_carrier_program_law N r keep ops _ _
    (actual_initial_copy_carrier_diagram N sample keep register).symm

/-- Actual graph-generated natural calendar has the canonical separately
initialized small-copy source law, preserving every ORIGINAL rate/site/mode. -/
theorem actual_natural_calendar_cross_carrier (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (naturalCalendarLaw N C sample H p common r).map (fun d => joinedProjection N keep (.inl d)) =
      (naturalCalendarLaw N C (selectedSample sample keep) H p common r).map
        (fun d => joinedProjection N keep (.inr d)) :=
  original_initialized_register_program_law N sample keep p r _

lemma natural_after_root_program (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (t : ℝ≥0) :
    naturalSourceAfterRoot N C sample H p common r t =
      (originalRegisterPMF N p).bind (fun register => sourceProgram N r
        (compiledCalendarProgram N C H (originalGamma p) common ++ [.interval t])
          (initialCode N sample register)) := by
  simp only [naturalSourceAfterRoot,naturalCalendarLaw,PMF.bind_bind,sourceProgram_append,
    sourceProgram,sourceProgramStep,PMF.bind_pure]

/-- Actual full/small finite ancestral-time law after the SAME natural original
calendar, not merely a same-copy selected range or an assumed kernel match. -/
theorem actual_natural_after_root_cross_carrier (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (t : ℝ≥0) :
    (naturalSourceAfterRoot N C sample H p common r t).map (fun d => joinedProjection N keep (.inl d)) =
      (naturalSourceAfterRoot N C (selectedSample sample keep) H p common r t).map
        (fun d => joinedProjection N keep (.inr d)) := by
  rw [natural_after_root_program,natural_after_root_program]
  exact original_initialized_register_program_law N sample keep p r _

/-- Eventual ancestral completion commutes with the ACTUAL independently
initialized smaller-copy source. The same-source full programme and the derived
actual limits discharge all stochastic equality premises. -/
theorem actual_natural_completed_cross_carrier (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (hk : keep.Nonempty) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (naturalCompletedLaw N C sample H p common r).map (fun d => joinedProjection N keep (.inl d)) =
      (naturalCompletedLaw N C (selectedSample sample keep) H p common r).map
        (fun d => joinedProjection N keep (.inr d)) := by
  obtain ⟨x,hx⟩ := hk
  letI : Nonempty Copy := ⟨x⟩
  letI : Nonempty (SelectedCopy keep) := ⟨⟨x,hx⟩⟩
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hf := finite_pmf_observer_limit
    (naturalSourceAfterRoot N C sample H p common r) (naturalCompletedLaw N C sample H p common r)
    (fun d => joinedProjection N keep (.inl d)) (natural_source_tendsto_completed N C sample H p common r) v
  have hz := finite_pmf_observer_limit
    (naturalSourceAfterRoot N C (selectedSample sample keep) H p common r)
    (naturalCompletedLaw N C (selectedSample sample keep) H p common r)
    (fun d => joinedProjection N keep (.inr d))
    (natural_source_tendsto_completed N C (selectedSample sample keep) H p common r) v
  have he : ∀ t : ℝ≥0,
      (((naturalSourceAfterRoot N C sample H p common r t).map
        (fun d => joinedProjection N keep (.inl d))) v).toReal =
      (((naturalSourceAfterRoot N C (selectedSample sample keep) H p common r t).map
        (fun d => joinedProjection N keep (.inr d))) v).toReal := by
    intro t
    exact congrArg (fun q : PMF (JoinedIndex N sample keep) => (q v).toReal)
      (actual_natural_after_root_cross_carrier N C sample keep H p common r t)
  exact tendsto_nhds_unique (hf.congr' (Eventually.of_forall he)) hz

#print axioms original_initialized_register_program_law
#print axioms actual_natural_calendar_cross_carrier
#print axioms actual_natural_after_root_cross_carrier
#print axioms actual_natural_completed_cross_carrier
end UnifiedLean.Source.SourceCrossCarrierNatural
