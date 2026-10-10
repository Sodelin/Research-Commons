import G5OriginalSelectedPosterior

/-!
# Actual original-source continuation after selected-singleton conditioning

Contributor: dot, 2026-10-09.
VERIFICATION: see the packet's exact-byte build and owned-declaration audit receipt.

The input is the actual original finite-program law, restricted BEFORE
projection to the selected-singleton event. The output is the actual source
continuation, including its shared register and original populations. Both
carriers use the same original graph, rates and operation word. No posterior
factorization, conditional independence of hidden routes, or future-kernel
identity is an assumption.

This connects the accepted posterior to the actual continuation kernel. It
does not identify arbitrary physical-time cuts or the five-partition closed
formula, and does not by itself conclude the G5 decoder.
-/
namespace GProgram.G5.OriginalConditionedContinuation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierProgram
open GProgram.G5.OriginalProgramSurvival
open GProgram.G5.OriginalSelectedPosterior
open scoped Classical NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The existing actual program factor-through specialized to the full side.
This retains the latent view, rather than redrawing a hybrid register. -/
theorem actual_full_continuation_row (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (future : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r future s).map (fun d => joinedProjection N keep (.inl d)) =
      commonProgram N r keep future (joinedProjection N keep (.inl s)) := by
  have h := joined_actual_program_projection N r keep future (.inl s)
  rw [joined_program_full, PMF.map_comp] at h
  exact h

theorem actual_small_continuation_row (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (future : List (ProgramStep N)) (s : Code N (selectedSample sample keep)) :
    (sourceProgram N r future s).map (fun d => joinedProjection N keep (.inr d)) =
      commonProgram N r keep future (joinedProjection N keep (.inr s)) := by
  have h := joined_actual_program_projection N r keep future (.inr s)
  rw [joined_program_small, PMF.map_comp] at h
  exact h

noncomputable def fullConditionedContinuation (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (past future : List (ProgramStep N)) :
    PMF (JoinedIndex N sample keep) :=
  (((originalProgramLaw N sample p r past).filter
    ((fun d => joinedProjection N keep (.inl d)) ⁻¹' selectedSingletonEvent N sample keep)
    (actual_full_code_event_witness N sample p r keep past)).bind
      (sourceProgram N r future)).map (fun d => joinedProjection N keep (.inl d))

noncomputable def smallConditionedContinuation (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (past future : List (ProgramStep N)) :
    PMF (JoinedIndex N sample keep) :=
  (((originalProgramLaw N (selectedSample sample keep) p r past).filter
    ((fun d => joinedProjection N keep (.inr d)) ⁻¹' selectedSingletonEvent N sample keep)
    (actual_small_code_event_witness N sample p r keep past)).bind
      (sourceProgram N r future)).map (fun d => joinedProjection N keep (.inr d))

/-- The actual source conditional continuation is the posterior mixture of
the derived actual common-view rows. Extra unselected mergers are allowed. -/
theorem actual_full_posterior_continuation (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (past future : List (ProgramStep N)) :
    fullConditionedContinuation N sample p r keep past future =
      (originalFullPosterior N sample p r keep past).bind
        (commonProgram N r keep future) := by
  unfold fullConditionedContinuation originalFullPosterior
  rw [PMF.map_bind, PMF.bind_map]
  simp only [Function.comp_def]
  simp_rw [actual_full_continuation_row]

theorem actual_small_posterior_continuation (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (past future : List (ProgramStep N)) :
    smallConditionedContinuation N sample p r keep past future =
      (originalSmallPosterior N sample p r keep past).bind
        (commonProgram N r keep future) := by
  unfold smallConditionedContinuation originalSmallPosterior
  rw [PMF.map_bind, PMF.bind_map]
  simp only [Function.comp_def]
  simp_rw [actual_small_continuation_row]

/-- Complete conditional future-view equality between the original full
source and its independently initialized selected-copy source. -/
theorem actual_conditioned_continuation_cross_carrier (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (past future : List (ProgramStep N)) :
    fullConditionedContinuation N sample p r keep past future =
      smallConditionedContinuation N sample p r keep past future := by
  rw [actual_full_posterior_continuation, actual_small_posterior_continuation,
    actual_original_program_selected_posterior]

/-- Any final readout of the retained internal view, including genealogy-only
readouts, inherits the actual conditional future law. Hidden coordinates need
not be declared observed. -/
theorem actual_conditioned_observation_cross_carrier {O : Type*}
    (N : RootedBinary V E X) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (keep : Finset Copy)
    (past future : List (ProgramStep N)) (observe : JoinedIndex N sample keep → O) :
    (fullConditionedContinuation N sample p r keep past future).map observe =
      (smallConditionedContinuation N sample p r keep past future).map observe := by
  rw [actual_conditioned_continuation_cross_carrier]

#print axioms actual_full_continuation_row
#print axioms actual_small_continuation_row
#print axioms actual_full_posterior_continuation
#print axioms actual_small_posterior_continuation
#print axioms actual_conditioned_continuation_cross_carrier
#print axioms actual_conditioned_observation_cross_carrier
end GProgram.G5.OriginalConditionedContinuation

