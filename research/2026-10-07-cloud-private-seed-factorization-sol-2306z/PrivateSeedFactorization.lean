import UnifiedLean.G6.PrivateRegisterProgram
import UnifiedLean.Source.SourceNaturalInitialization
import G2LiteralMarkedClockTrace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Contributor: Codex, delegated original G6 source author, 2026-10-07.
UNCHECKED actual natural-register consumer, outside the current165 freeze.
The original hybrid product and admitted natural initial Code supply every
law below. No entering independence, source kernel equality, chronology,
cross-graph carrier or observed private-bit label is assumed.
-/

namespace CloudG6.PrivateSeedFactorization
set_option backward.isDefEq.respectTransparency false

universe u v w x

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterProgram
open scoped Classical

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

abbrev PrivateHybrid (N : RootedBinary V E X) (P : Finset V) :=
  {h : Hybrid N // h.val ∈ P}

abbrev OutsideHybrid (N : RootedBinary V E X) (P : Finset V) :=
  {h : Hybrid N // h.val ∉ P}

noncomputable def splitOriginalCoins (N : RootedBinary V E X) (P : Finset V) :
    (Hybrid N → Bool) ≃ᵐ
      (PrivateHybrid N P → Bool) × (OutsideHybrid N P → Bool) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Hybrid N => Bool)
    (fun h => h.val ∈ P)

noncomputable def privateCoinMeasure (N : RootedBinary V E X) (P : Finset V)
    (p : HybridProbabilities N) : Measure (PrivateHybrid N P → Bool) :=
  Measure.pi (fun h : PrivateHybrid N P => bitMeasure (originalGamma p h.val))

noncomputable def outsideCoinMeasure (N : RootedBinary V E X) (P : Finset V)
    (p : HybridProbabilities N) : Measure (OutsideHybrid N P → Bool) :=
  Measure.pi (fun h : OutsideHybrid N P => bitMeasure (originalGamma p h.val))

instance privateCoin_probability (N : RootedBinary V E X) (P : Finset V)
    (p : HybridProbabilities N) : IsProbabilityMeasure (privateCoinMeasure N P p) := by
  unfold privateCoinMeasure
  infer_instance

instance outsideCoin_probability (N : RootedBinary V E X) (P : Finset V)
    (p : HybridProbabilities N) : IsProbabilityMeasure (outsideCoinMeasure N P p) := by
  unfold outsideCoinMeasure
  infer_instance

/-- Only outside ORIGINAL hybrid bits survive; all other slots are false. -/
noncomputable def outsideRegister (N : RootedBinary V E X) (P : Finset V)
    (coin : OutsideHybrid N P → Bool) : V → Bool := fun v =>
  if hv : v ∈ P then false
  else if hh : N.graph.IsHybrid v then coin ⟨⟨v, hh⟩, hv⟩ else false

noncomputable def outsideInitialCode (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (coin : OutsideHybrid N P → Bool) : Code N sample :=
  initialCode N sample (outsideRegister N P coin)

/-- Actual natural entry: original once-drawn register mapped through its
existing source-valid initialization, without any posterior replacement. -/
noncomputable def naturalInitialCodeLaw (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) : PMF (Code N sample) :=
  (originalRegisterPMF N p).map (initialCode N sample)

noncomputable def outsideInitialCodeLaw (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) : PMF (Code N sample) :=
  (outsideCoinMeasure N P p).toPMF.map (outsideInitialCode N P sample)

/-- The concrete ORIGINAL hybrid product splits by its actual site indices. -/
theorem actual_original_coin_split (N : RootedBinary V E X) (P : Finset V)
    (p : HybridProbabilities N) :
    (originalRegisterMeasure N p).map (splitOriginalCoins N P) =
      (privateCoinMeasure N P p).prod (outsideCoinMeasure N P p) := by
  have h := measurePreserving_piEquivPiSubtypeProd
    (fun h : Hybrid N => bitMeasure (originalGamma p h)) (fun h => h.val ∈ P)
  simpa only [originalRegisterMeasure, splitOriginalCoins, privateCoinMeasure,
    outsideCoinMeasure] using h.map_eq

/-- Original admitted initialization commutes with register-only erasure;
all initial copy/leaf/population fields and their source validity remain. -/
theorem erase_initialCode (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (register : V → Bool) :
    erasePrivateCode N P (initialCode N sample register) =
      initialCode N sample (fun v => if v ∈ P then false else register v) := by
  apply Subtype.ext
  apply Snapshot.ext <;> rfl

theorem erased_originalRegister_outside (N : RootedBinary V E X) (P : Finset V)
    (coin : Hybrid N → Bool) :
    (fun v => if v ∈ P then false else originalRegister N coin v) =
      outsideRegister N P (fun h => coin h.val) := by
  funext v
  by_cases hv : v ∈ P
  · simp only [outsideRegister, if_pos hv]
  · by_cases hh : N.graph.IsHybrid v <;>
      simp [outsideRegister, originalRegister, hv, hh]

theorem erase_natural_initialCode (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (coin : Hybrid N → Bool) :
    erasePrivateCode N P (initialCode N sample (originalRegister N coin)) =
      outsideInitialCode N P sample (fun h => coin h.val) := by
  rw [erase_initialCode, erased_originalRegister_outside]
  rfl

theorem natural_initial_toMeasure (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) :
    (naturalInitialCodeLaw N sample p).toMeasure =
      (originalRegisterMeasure N p).map
        (fun coin => initialCode N sample (originalRegister N coin)) := by
  unfold naturalInitialCodeLaw originalRegisterPMF
  rw [PMF.map_comp, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    Measure.toPMF_toMeasure]
  rfl

theorem outside_initial_toMeasure (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) :
    (outsideInitialCodeLaw N P sample p).toMeasure =
      (outsideCoinMeasure N P p).map (outsideInitialCode N P sample) := by
  unfold outsideInitialCodeLaw
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), Measure.toPMF_toMeasure]

/-- Derived internal joint law: private latent bits factor from the SAME
erased natural Code. This does not declare those bits measured labels. -/
theorem actual_private_seed_erased_initial_product (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N) :
    (originalRegisterMeasure N p).map (fun coin : Hybrid N → Bool =>
        ((fun h : PrivateHybrid N P => coin h.val),
          erasePrivateCode N P (initialCode N sample (originalRegister N coin)))) =
      (privateCoinMeasure N P p).prod (outsideInitialCodeLaw N P sample p).toMeasure := by
  have hout : Measurable (outsideInitialCode N P sample) := measurable_of_countable _
  have hprod := Measure.map_prod_map (privateCoinMeasure N P p)
    (outsideCoinMeasure N P p) measurable_id hout
  simp only [Measure.map_id] at hprod
  calc
    _ = ((originalRegisterMeasure N p).map (splitOriginalCoins N P)).map
        (Prod.map id (outsideInitialCode N P sample)) := by
      rw [Measure.map_map (measurable_id.prodMap hout) (splitOriginalCoins N P).measurable]
      apply congrArg (fun f => (originalRegisterMeasure N p).map f)
      funext coin
      exact Prod.ext rfl (erase_natural_initialCode N P sample coin)
    _ = ((privateCoinMeasure N P p).prod (outsideCoinMeasure N P p)).map
        (Prod.map id (outsideInitialCode N P sample)) := by
      rw [actual_original_coin_split]
    _ = _ := by
      rw [← hprod, ← outside_initial_toMeasure]

/-- Actual natural initial PMF erasure is obtained by marginalizing the
proved joint product; no arbitrary entering-law independence is a premise. -/
theorem actual_natural_initial_erased_law (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N) :
    (naturalInitialCodeLaw N sample p).map (erasePrivateCode N P) =
      outsideInitialCodeLaw N P sample p := by
  have he := congrArg (fun μ => μ.map Prod.snd)
    (actual_private_seed_erased_initial_product N P sample p)
  rw [Measure.map_map measurable_snd (measurable_of_countable _),
    Measure.map_snd_prod, measure_univ, one_smul] at he
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), natural_initial_toMeasure,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact he

/-- Source-connected causal-word marginal consumer. The explicit no-read
property is on real original operations; chronological admission is separate. -/
theorem actual_no_read_natural_program_erased_law (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : NoPrivateWordRead N P ops) :
    ((naturalInitialCodeLaw N sample p).bind (sourceProgram N r ops)).map
        (erasePrivateCode N P) =
      (outsideInitialCodeLaw N P sample p).bind (sourceProgram N r ops) := by
  rw [PMF.map_bind]
  simp_rw [actual_sourceProgram_erasure N r P ops hops]
  change (naturalInitialCodeLaw N sample p).bind
    (sourceProgram N r ops ∘ erasePrivateCode N P) = _
  rw [← PMF.bind_map, actual_natural_initial_erased_law N P sample p]

#print axioms actual_original_coin_split
#print axioms erase_initialCode
#print axioms erased_originalRegister_outside
#print axioms erase_natural_initialCode
#print axioms natural_initial_toMeasure
#print axioms outside_initial_toMeasure
#print axioms actual_private_seed_erased_initial_product
#print axioms actual_natural_initial_erased_law
#print axioms actual_no_read_natural_program_erased_law

end CloudG6.PrivateSeedFactorization
