import StochasticAbstraction
import UnifiedLean.Source.SourceProgramTransport

/-! Direct application of the older adaptive stochastic-abstraction theorem to
the actual original-source selected-panel kernel. Contributor: dot, 2026-10-09.
The fixed sample panel retains genealogy, locations and the original register.
This covers finite endpoint/action transcripts, not continuous clock paths or
physical admissibility of every state-dependent operation policy. -/
namespace Dot.ActualSourceAdaptiveAbstraction
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_source_exact (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    StochasticAbstraction.Exact
      (sourceProgramStep N r (sample := sample)) (projection N keep)
      (selectedProgramStep N r keep) :=
  actual_program_step_projection N r keep

/-- An adaptive controller can randomize and use the complete selected
endpoint/action history. The same controller lifted to the original source
preserves the full finite selected transcript, from any original initial law. -/
theorem actual_adaptive_selected_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (policy : StochasticAbstraction.Policy (SelectedIndex N sample keep) (ProgramStep N))
    (n : Nat) (mu : PMF (Code N sample)) :
    (StochasticAbstraction.experimentLaw (sourceProgramStep N r)
      (StochasticAbstraction.observationPolicy (projection N keep) policy) n mu).map
        (StochasticAbstraction.view (projection N keep)) =
    StochasticAbstraction.experimentLaw (selectedProgramStep N r keep) policy n
      (mu.map (projection N keep)) := by
  apply StochasticAbstraction.experimentLaw_preserves
    (sourceProgramStep N r) (projection N keep) (selectedProgramStep N r keep)
    (actual_source_exact N r keep)
  intro past s
  rfl

/-- Every declared readout of the selected state can drive the controller.
This does not assert that an arbitrary readout is in the original biological
observation menu. That separate admission obligation remains explicit. -/
theorem actual_adaptive_observed_history {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy)
    (readout : SelectedIndex N sample keep → Obs)
    (policy : StochasticAbstraction.Policy Obs (ProgramStep N))
    (n : Nat) (mu : PMF (Code N sample)) :
    (StochasticAbstraction.experimentLaw (sourceProgramStep N r)
      (StochasticAbstraction.observationPolicy (readout ∘ projection N keep) policy)
      n mu).map (StochasticAbstraction.view (readout ∘ projection N keep)) =
    (StochasticAbstraction.experimentLaw (selectedProgramStep N r keep)
      (StochasticAbstraction.observationPolicy readout policy)
      n (mu.map (projection N keep))).map (StochasticAbstraction.view readout) :=
  StochasticAbstraction.observed_experiment_law
    (sourceProgramStep N r) (projection N keep) (selectedProgramStep N r keep)
    (actual_source_exact N r keep) (readout ∘ projection N keep) readout
    (fun _ => rfl) policy n mu

#print axioms actual_source_exact
#print axioms actual_adaptive_selected_history
#print axioms actual_adaptive_observed_history
end Dot.ActualSourceAdaptiveAbstraction
