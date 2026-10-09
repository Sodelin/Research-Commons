import PrivateSeedHistoryFactorization
import UnifiedLean.G6.PrivateRegisterCalendarPrefix

/-! Consumer of the previously compiled original-seed/history factorization.
Contributor: dot (OpenAI), 9 October 2026. No new independence premise.
An event of the erased causal endpoint history may be conditioned upon when its
mass is nonzero. This is an internal source event, not a G4 observation decoder. -/
namespace DotG34.ActualUnusedSeedConditioning
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceForestPulseMeasure UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterHistory GProgram.G2.SourceFiniteHistory
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

theorem actual_unused_seed_event_mass (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : NoPrivateWordRead N P ops)
    (A : Set (PrivateHybrid N P → Bool))
    (B : Set (Code N sample × (Fin ops.length → Code N sample))) :
    (((initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
      (fun a => (a.1, (erasePrivateCode N P a.2.1,
        historyProjection (erasePrivateCode N P) a.2.2)))).toMeasure) (A ×ˢ B) =
    privateCoinMeasure N P p A *
      (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p)).toMeasure B := by
  rw [actual_private_seed_erased_history_measure, Measure.prod_prod]

theorem actual_unused_seed_posterior (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : NoPrivateWordRead N P ops)
    (A : Set (PrivateHybrid N P → Bool))
    (B : Set (Code N sample × (Fin ops.length → Code N sample)))
    (hB : (initializedEndpointLaw N r ops
      (outsideInitialCodeLaw N P sample p)).toMeasure B ≠ 0) :
    (((initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
      (fun a => (a.1, (erasePrivateCode N P a.2.1,
        historyProjection (erasePrivateCode N P) a.2.2)))).toMeasure) (A ×ˢ B) /
      (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p)).toMeasure B =
    privateCoinMeasure N P p A := by
  rw [actual_unused_seed_event_mass N P sample p r ops hops A B]
  exact ENNReal.mul_div_cancel_right hB (measure_ne_top _ _)

theorem private_seed_bit_mass (N : RootedBinary V E X)
    (P : Finset V) (p : HybridProbabilities N) (h : PrivateHybrid N P) (b : Bool) :
    privateCoinMeasure N P p {coin | coin h = b} =
      bitMeasure (originalGamma p h.val) {b} := by
  have hm := (measurePreserving_eval
    (μ := fun j : PrivateHybrid N P => bitMeasure (originalGamma p j.val)) h).map_eq
  have he := congrArg (fun μ : Measure Bool => μ {b}) hm
  rw [Measure.map_apply (measurable_pi_apply h) (measurableSet_singleton b)] at he
  exact he

/-- In particular, selecting a positive-mass erased past event does not
replace or bias the original unused site's Bernoulli law. -/
theorem actual_unused_bit_posterior (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : NoPrivateWordRead N P ops) (h : PrivateHybrid N P) (b : Bool)
    (B : Set (Code N sample × (Fin ops.length → Code N sample)))
    (hB : (initializedEndpointLaw N r ops
      (outsideInitialCodeLaw N P sample p)).toMeasure B ≠ 0) :
    (((initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
      (fun a => (a.1, (erasePrivateCode N P a.2.1,
        historyProjection (erasePrivateCode N P) a.2.2)))).toMeasure)
      ({coin | coin h = b} ×ˢ B) /
      (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p)).toMeasure B =
    bitMeasure (originalGamma p h.val) {b} := by
  rw [actual_unused_seed_posterior N P sample p r ops hops _ B hB,
    private_seed_bit_mass]

#print axioms private_seed_bit_mass
#print axioms actual_unused_bit_posterior
#print axioms actual_unused_seed_event_mass
#print axioms actual_unused_seed_posterior
end DotG34.ActualUnusedSeedConditioning
