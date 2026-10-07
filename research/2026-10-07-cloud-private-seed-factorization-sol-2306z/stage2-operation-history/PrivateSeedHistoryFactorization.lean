import PrivateSeedFactorization
import UnifiedLean.G6.PrivateRegisterHistory
import Mathlib.MeasureTheory.Measure.Dirac

/-!
Contributor: Codex, delegated G6 source author, 2026-10-07.
UNCHECKED additive consumer, outside current165. The actual original seed
initializes the same original Code. Its proved private/outside split is then
bound through the actual no-private-read source-history rows. All endpoints,
including the initial one and the empty-word initial record, are retained.
This is not the full literal marked-clock/bin or cross-graph observation law.
-/
namespace CloudG6.PrivateSeedHistoryFactorization
set_option backward.isDefEq.respectTransparency false

universe u v w x y z

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterHistory GProgram.G2.SourceFiniteHistory
open CloudG6.PrivateSeedFactorization
open scoped Classical

/-- Concrete independent PMF: draw its first coordinate, then draw the second
from its own fixed PMF. Its product measure is proved below, not assumed. -/
noncomputable def independentPMF {A : Type y} {B : Type z}
    (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind (fun a => q.map (Prod.mk a))

theorem independentPMF_apply {A : Type y} {B : Type z}
    (p : PMF A) (q : PMF B) (a : A) (b : B) :
    independentPMF p q (a, b) = p a * q b := by
  classical
  have hq (a' : A) : (q.map (Prod.mk a')) (a, b) =
      if a = a' then q b else 0 := by
    by_cases ha : a = a'
    · subst a'
      simp [PMF.map_apply, Prod.mk.injEq]
    · simp [PMF.map_apply, Prod.mk.injEq, ha]
  unfold independentPMF
  rw [PMF.bind_apply]
  simp_rw [hq, mul_ite, mul_zero]
  simp

theorem independentPMF_toMeasure {A : Type y} {B : Type z}
    [Countable A] [Countable B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (p : PMF A) (q : PMF B) :
    (independentPMF p q).toMeasure = p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    independentPMF_apply, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

noncomputable def privateSeedPMF (N : RootedBinary V E X) (P : Finset V)
    (p : HybridProbabilities N) : PMF (PrivateHybrid N P → Bool) :=
  (privateCoinMeasure N P p).toPMF

/-- The actual original seed and its SAME admitted natural initial Code. -/
noncomputable def naturalInitialJoint (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) :
    PMF ((PrivateHybrid N P → Bool) × Code N sample) :=
  (originalRegisterMeasure N p).toPMF.map (fun coin : Hybrid N → Bool =>
    ((fun h : PrivateHybrid N P => coin h.val),
      initialCode N sample (originalRegister N coin)))

/-- Source endpoint history with its entering Code, even for an empty word. -/
noncomputable def initializedEndpointLaw (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) :
    PMF (Code N sample × (Fin ops.length → Code N sample)) :=
  initial.bind (fun s => (sourceHistoryLaw N r ops s).map (fun h => (s, h)))

theorem natural_joint_toMeasure (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) :
    (naturalInitialJoint N P sample p).toMeasure =
      (originalRegisterMeasure N p).map (fun coin : Hybrid N → Bool =>
        ((fun h : PrivateHybrid N P => coin h.val),
          initialCode N sample (originalRegister N coin))) := by
  unfold naturalInitialJoint
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
    Measure.toPMF_toMeasure]

/-- The initial product is derived from the actual original seed measure and
its proved natural initializer erasure. It is not an entering-law hypothesis. -/
theorem actual_natural_joint_initial_product (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N) :
    (naturalInitialJoint N P sample p).map
        (fun a => (a.1, erasePrivateCode N P a.2)) =
      independentPMF (privateSeedPMF N P p) (outsideInitialCodeLaw N P sample p) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
    natural_joint_toMeasure,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    independentPMF_toMeasure]
  unfold privateSeedPMF
  rw [Measure.toPMF_toMeasure]
  change (originalRegisterMeasure N p).map (fun coin : Hybrid N → Bool =>
      ((fun h : PrivateHybrid N P => coin h.val),
        erasePrivateCode N P (initialCode N sample (originalRegister N coin)))) = _
  exact actual_private_seed_erased_initial_product N P sample p

/-- Pure bind algebra for a history kernel that reads only the initial Code.
The actual consumer below obtains its input product from the original seed. -/
theorem initialized_history_independent {Old : Type y}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (old : PMF Old) (initial : PMF (Code N sample)) :
    initializedSourceHistory N r ops (independentPMF old initial) =
      independentPMF old (initializedEndpointLaw N r ops initial) := by
  simp only [independentPMF, initializedSourceHistory, initializedEndpointLaw,
    PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- PRIVATE latent seed times the entire erased initialized original endpoint
vector. Uses actual initialization plus actual no-read history transport;
there is no desired law, entering independence or row equality premise. -/
theorem actual_private_seed_erased_history_product (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : NoPrivateWordRead N P ops) :
    (initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
        (fun a => (a.1, (erasePrivateCode N P a.2.1,
          historyProjection (erasePrivateCode N P) a.2.2))) =
      independentPMF (privateSeedPMF N P p)
        (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p)) := by
  rw [actual_initialized_history_erasure N r P ops hops,
    actual_natural_joint_initial_product, initialized_history_independent]

/-- The same actual joint law as a product of normalized measures, rather
than an informal independence label. The only semantic restriction is no-read. -/
theorem actual_private_seed_erased_history_measure (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : NoPrivateWordRead N P ops) :
    ((initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
        (fun a => (a.1, (erasePrivateCode N P a.2.1,
          historyProjection (erasePrivateCode N P) a.2.2)))).toMeasure =
      (privateCoinMeasure N P p).prod
        (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p)).toMeasure := by
  rw [actual_private_seed_erased_history_product N P sample p r ops hops,
    independentPMF_toMeasure]
  unfold privateSeedPMF
  rw [Measure.toPMF_toMeasure]

/-- Empty words retain the actual initialized Code and an empty endpoint vector. -/
theorem initializedEndpointLaw_nil (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (initial : PMF (Code N sample)) :
    initializedEndpointLaw N r [] initial =
      initial.map (fun s => (s, (fun i : Fin 0 => Fin.elim0 i))) := by
  unfold initializedEndpointLaw sourceHistoryLaw
  simp only [historyLaw, PMF.pure_map]
  rfl

theorem actual_private_seed_erased_history_nil (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) :
    (initializedSourceHistory N r [] (naturalInitialJoint N P sample p)).map
        (fun a => (a.1, (erasePrivateCode N P a.2.1,
          historyProjection (erasePrivateCode N P) a.2.2))) =
      independentPMF (privateSeedPMF N P p)
        ((outsideInitialCodeLaw N P sample p).map
          (fun s => (s, (fun i : Fin 0 => Fin.elim0 i)))) := by
  have hops : NoPrivateWordRead N P [] := by
    intro op hop
    simp at hop
  rw [actual_private_seed_erased_history_product N P sample p r [] hops,
    initializedEndpointLaw_nil]

/-- One joint internal readout of this endpoint vector. Choosing a map does
not admit it as an observed biological menu or marked-clock/bin law. -/
theorem actual_private_seed_erased_history_readout {Obs : Type z}
    (N : RootedBinary V E X) (P : Finset V) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops)
    (readout : (PrivateHybrid N P → Bool) ×
      (Code N sample × (Fin ops.length → Code N sample)) → Obs) :
    (initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
        (readout ∘ (fun a => (a.1, (erasePrivateCode N P a.2.1,
          historyProjection (erasePrivateCode N P) a.2.2)))) =
      (independentPMF (privateSeedPMF N P p)
        (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p))).map
          readout := by
  rw [← PMF.map_comp, actual_private_seed_erased_history_product N P sample p r ops hops]

#print axioms independentPMF_apply
#print axioms independentPMF_toMeasure
#print axioms natural_joint_toMeasure
#print axioms actual_natural_joint_initial_product
#print axioms initialized_history_independent
#print axioms actual_private_seed_erased_history_product
#print axioms actual_private_seed_erased_history_measure
#print axioms initializedEndpointLaw_nil
#print axioms actual_private_seed_erased_history_nil
#print axioms actual_private_seed_erased_history_readout

end CloudG6.PrivateSeedHistoryFactorization
