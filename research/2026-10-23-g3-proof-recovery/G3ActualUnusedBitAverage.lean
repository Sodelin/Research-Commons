import ActualUnusedSeedConditioning
import Mathlib.Tactic.Ring

/-!
UNCOMPILED source-level candidate, 21 October 2026.
Actual unused-seed averaging over an erased causal history event. It reuses
the original initialized source-history measure, not a new independence field
or a refreshed COMMON coin. The literal NoPrivateWordRead obligation remains.
This unnormalized identity also covers a zero-mass event. To identify an
actual post-program no-loss event with this weighted trace mass still needs
the original stored-register/diagonal/entrance/count suppliers.
-/
namespace GProgram.G3.ActualUnusedBitAverage

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceForestPulseMeasure UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterHistory GProgram.G2.SourceFiniteHistory
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open DotG34.ActualUnusedSeedConditioning
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- The seed coordinate is the actual original once-stored hybrid bit;
nonhybrid/default register slots are not substituted for it. -/
theorem original_private_register_value (N : RootedBinary V E X) (P : Finset V)
    (coin : Hybrid N → Bool) (h : PrivateHybrid N P) :
    originalRegister N coin h.val.val = coin h.val := by
  simp [originalRegister,h.val.property]

noncomputable def erasedSeedHistoryMeasure
    (N : RootedBinary V E X) (P : Finset V) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) :=
  (((initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
    (fun a => (a.1, (erasePrivateCode N P a.2.1,
      historyProjection (erasePrivateCode N P) a.2.2)))).toMeasure)

theorem actual_unused_bit_weighted_history_mass
    (N : RootedBinary V E X) (P : Finset V) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops)
    (h : PrivateHybrid N P)
    (B : Set (Code N sample × (Fin ops.length → Code N sample)))
    (x y : ℝ≥0∞) :
    x * (erasedSeedHistoryMeasure N P sample p r ops)
        ({coin | coin h = false} ×ˢ B) +
      y * (erasedSeedHistoryMeasure N P sample p r ops)
        ({coin | coin h = true} ×ˢ B) =
      (x * bitMeasure (originalGamma p h.val) {false} +
        y * bitMeasure (originalGamma p h.val) {true}) *
      (initializedEndpointLaw N r ops
        (outsideInitialCodeLaw N P sample p)).toMeasure B := by
  unfold erasedSeedHistoryMeasure
  rw [actual_unused_seed_event_mass N P sample p r ops hops _ B,
    actual_unused_seed_event_mass N P sample p r ops hops _ B,
    private_seed_bit_mass N P p h false,private_seed_bit_mass N P p h true]
  ring

#print axioms actual_unused_bit_weighted_history_mass
#print axioms original_private_register_value

end GProgram.G3.ActualUnusedBitAverage
