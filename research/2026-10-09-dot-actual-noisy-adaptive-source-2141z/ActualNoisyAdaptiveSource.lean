import ActualSourceAdaptiveAbstraction

/-! Actual-source instantiation of the older joint-sensor abstraction theorem.
The declared sensor depends on the action and both selected endpoint states.
It is a mathematical sensor model, not automatic biological menu admission.
Contributor: dot / OpenAI, 2026-10-09. No historical novelty claim. -/
namespace Dot.ActualNoisyAdaptiveSource
open StochasticAbstraction
open scoped Classical
noncomputable section

variable {S R O A : Type*}

def sensed (K : A → S → PMF S) (q : S → R)
    (sensor : A → R → R → PMF O) (a : A) (s : S) : PMF (S × O) :=
  (K a s).bind fun t => (sensor a (q s) (q t)).map fun o => (t,o)

theorem sensed_joint_preserves (K : A → S → PMF S) (q : S → R)
    (L : A → R → PMF R) (h : Exact K q L)
    (sensor : A → R → R → PMF O) (a : A) (s : S) :
    (sensed K q sensor a s).map (sensorCode q) =
      sensed L id sensor a (q s) := by
  unfold sensed
  rw [PMF.map_bind]
  simp only [PMF.map_comp]
  change (K a s).bind (fun t =>
      (sensor a (q s) (q t)).map (fun o => (q t,o))) = _
  calc
    _ = ((K a s).map q).bind (fun t =>
        (sensor a (q s) t).map (fun o => (t,o))) :=
      (PMF.bind_map _ _ _).symm
    _ = _ := by rw [h a s]; rfl

open Nanuq.Source UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Equality of the complete finite noisy observation/action transcript law.
The policy sees only noisy readings. Initial state/reading correlation is allowed.
Future measurement noise follows the explicitly defined endpoint sensor kernel. -/
theorem actual_noisy_adaptive_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (sensor : ProgramStep N → SelectedIndex N sample keep →
      SelectedIndex N sample keep → PMF O)
    (policy : Policy O (ProgramStep N)) (n : Nat)
    (mu : PMF (Code N sample × O)) :
    (experimentLaw (sensorStep (sensed (sourceProgramStep N r)
      (projection N keep) sensor)) (observationPolicy Prod.snd policy) n mu).map
      (view Prod.snd) =
    (experimentLaw (sensorStep (sensed (selectedProgramStep N r keep) id sensor))
      (observationPolicy Prod.snd policy) n (mu.map (sensorCode (projection N keep)))).map
      (view Prod.snd) :=
  joint_sensor_observed_law _ _ _
    (sensed_joint_preserves _ _ _
      (Dot.ActualSourceAdaptiveAbstraction.actual_source_exact N r keep) sensor)
    policy n mu

end
end Dot.ActualNoisyAdaptiveSource

#print axioms Dot.ActualNoisyAdaptiveSource.sensed_joint_preserves
#print axioms Dot.ActualNoisyAdaptiveSource.actual_noisy_adaptive_history
