import G2ActualTimedAllPanelLaw

/-!
# Register-hidden actual timed genealogy projectivity
Contributor: GPT-6 Astra Pro, G5 session 7E3B, 2026-10-07.
STATUS: UNCHECKED. This source has not been elaborated or kernel-checked.

This is a consumer of dot's actual original-source timed G2 construction.
The once-drawn register remains in the SOURCE and is marginalized only at the
observation boundary. No register equality or measured population ID is added
to G5's observation contract. This module proves neither frozen-germ support
recovery nor the full M3-to-clusters/splits identification theorem.

Selected provider: G2ActualTimedAllPanelLaw.lean, source SHA256
05ca8311eb01110a0d01d1f12ef6fe744fef51b21f1c3592e90bad3b08f6c376,
from Commons' 2026-10-07 09:41 timed-G2 integration packet. Its additive
terminal-reader context must be retained; the old reader alone is not enough.
-/
namespace GProgram.G5.HiddenRegisterTimedProjectivity
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization
open GProgram.G2.JointTimedObservation GProgram.G2.FaithfulTimedOutput
open GProgram.G2.LiteralTimedObservationPruning GProgram.G2.ControlledTraceAssembly
open GProgram.G2.ChronologicalPathReadout GProgram.G2.RegisteredPathProjection
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompletedPathProjection
open GProgram.G2.CompleteDecoration GProgram.G2.ActualTimedAllPanelLaw
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.CalendarHistoryBinding.joinedMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable

/-- Forget ONLY the latent register, not the topology or calendar ages. -/
def eraseRegister (z : (V → Bool) × TimedObservation Copy) : TimedObservation Copy := z.2

lemma erase_register_measurable :
    Measurable (eraseRegister (V := V) (Copy := Copy)) := measurable_snd

/-- Derive ordinary timed-pruning measurability from the inspected G2 provider.
The constant register is a measurability proof device, NOT a source change. -/
lemma ordinary_prune_measurable (keep : Finset Copy) :
    Measurable (pruneTimedObservation keep) := by
  have hi : Measurable (fun o : TimedObservation Copy => ((fun _ : Unit => false), o)) :=
    measurable_const.prodMk measurable_id
  have hp := measurable_snd.comp
    ((prune_registered_measurable (V := Unit) keep).comp hi)
  simpa only [Function.comp_def, pruneRegistered] using hp

/-- Marginalizing the once-drawn register commutes with literal tip pruning. -/
lemma erasure_pruning_pushforward
    (μ : Measure ((V → Bool) × TimedObservation Copy)) (keep : Finset Copy) :
    (μ.map eraseRegister).map (pruneTimedObservation keep) =
      (μ.map (pruneRegistered keep)).map eraseRegister := by
  rw [Measure.map_map (ordinary_prune_measurable keep)
      erase_register_measurable,
    Measure.map_map erase_register_measurable
      (prune_registered_measurable (V := V) keep)]
  rfl

/-- Genuine original-source timed readout with hidden inheritance registers. -/
noncomputable def naturalObservedFullLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    Measure (TimedObservation Copy) :=
  ((originalTimedTraceLaw N C sample H p common r).map
    (fullReadout N C sample Finset.univ
      (compiledCalendarProgram N C H (originalGamma p) common))).map eraseRegister

/-- Ordinary selected SOURCE law, with the same graph, parameters and register
law. This is not conditioning the full law on an earlier no-merger event. -/
noncomputable def naturalObservedSelectedLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy) :
    Measure (TimedObservation Copy) :=
  ((originalTimedTraceLaw N C (selectedSample sample keep) H p common r).map
    (smallReadout N C sample keep
      (compiledCalendarProgram N C H (originalGamma p) common))).map eraseRegister

/-- Arbitrary admitted inheritance probabilities, every original-label panel,
including empty and singleton panels. The observation no longer contains the
latent register. Uniform COMMON and INDEPENDENT modes are special instances.
No desired observation identity or coupling is supplied as a hypothesis. -/
theorem actual_natural_hidden_timed_all_panel_projectivity
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (keep : Finset Copy) :
    (naturalObservedFullLaw N C sample H p common r).map (pruneTimedObservation keep) =
      naturalObservedSelectedLaw N C sample H p common r keep := by
  unfold naturalObservedFullLaw naturalObservedSelectedLaw
  rw [erasure_pruning_pushforward]
  exact congrArg
    (fun μ : Measure ((V → Bool) × TimedObservation Copy) => μ.map eraseRegister)
    (actual_natural_complete_timed_all_panel_projectivity N C sample H p common r keep)

#print axioms erasure_pruning_pushforward
#print axioms actual_natural_hidden_timed_all_panel_projectivity
end GProgram.G5.HiddenRegisterTimedProjectivity
