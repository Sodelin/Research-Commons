import ActualObservationCorruption
import G6PairedTargetReuse
import UnifiedLean.Source.UnrankedGenealogyObservation
import UnifiedLean.G6.CorruptionClasses

/-!
CLOUD-G6-SOL-ULTRA-20261007. Compiler UNCHECKED, outside179.
Actual native completed-law source image with derived original Q/S labels.
One fixed sample/observable-only reader/bin/mode is shared across the source family. Its
biological menu/pruning/ancestral-rate semantics remain a separate bridge.
No stochastic law, target, net, minimizer or desired approximation is a field.
-/
namespace CloudG6.ActualSourceCorruptionClasses

open Nanuq.Source GProgram.G5 MeasureTheory
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.UnrankedGenealogyObservation
open CloudG3.ActualCutJointLaw CloudG6.ActualObservationCorruption
open UnifiedLean.G6.PairedTargetReuse UnifiedLean.G6.FiniteProbability
open UnifiedLean.G6.CorruptionClasses
open scoped Classical

universe u v w x y z
variable {Copy : Type w} {X : Type x} {Tag : Type y} {O : Type z}
variable [Fintype Copy] [DecidableEq Copy] [Fintype X]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
variable [Fintype O]
variable {sample : Copy → X}

abbrev OriginalTarget (X : Type x) :=
  ((Fin 4 ↪ X) → Finset Nanuq.Quartet.Resolution) × Finset (Finset (Finset X))

/-- Arbitrary finite original raw rooted/LSA/cut-child carrier and one shared
strictly positive parameter bank. Original physical IDs remain in the Source.
No structural core/spine replacement is used here. -/
structure OriginalParameters (Copy : Type w) (X : Type x) (sample : Copy → X)
    [Fintype Copy] [DecidableEq Copy] [Fintype X] where
  original : G1ActualGraphNormalization.Source.{u,v,x} X
  four_taxa : 4 ≤ Fintype.card X
  registry : OriginalParentRegistry original.network
  all_taxa_sampled : Function.Surjective sample
  contemporaneous : ∀ taxon, original.calendar.age (original.network.leaf taxon) = 0
  inheritance : HybridProbabilities original.network
  rates : PositivePairRates original.Edge

/-- A derived source target, never a user-supplied label or law property. -/
noncomputable def sourceTarget (s : OriginalParameters.{u,v,w,x} Copy X sample) :
    OriginalTarget X := originalG6TargetPair s.original.network

/-- A source-independent observation payload. The actual original source
observer quotients tree child order, and the carried full-copy tag matrix is
retained. Physical locations, register bits, rates and graph IDs are excluded.
The payload domain need not be finite; the selected output alphabet O is. -/
abbrev NativeObservedRecord (Copy : Type w) (Tag : Type y) :=
  Finset (UnrankedTree Copy) × (Copy → Copy → Tag)

noncomputable def observedRecord (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (q : TaggedEndpoint (Tag := Tag) s.original.network sample) :
    NativeObservedRecord Copy Tag :=
  (sourceUnrankedForest (state q.1) Finset.univ, q.2)

/-- COMMON=true and INDEPENDENT=false are FIXED for every original hybrid
in this family. The sample, bin and source-independent finite reader are fixed external inputs;
their faithful interpretation as one biological experiment is not assumed. -/
noncomputable def nativeLaw (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) : PMF O :=
  actualCompiledObservation s.original.network s.original.calendar sample
    s.registry s.inheritance (fun _ => mode) s.rates bin hbin (fun q => reader (observedRecord s q))

/-- Exact original-source image for a different specified answer. Parameters
remain arbitrary real positive values; no rational restriction or size bound. -/
noncomputable def wrongNativeImage {Answer : Type*}
    (answer : OriginalTarget X → Answer) (wanted : Answer) (mode : Bool)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) : Set (PMF O) :=
  {q | ∃ s : OriginalParameters.{u,v,w,x} Copy X sample,
    answer (sourceTarget s) ≠ wanted ∧ nativeLaw mode bin hbin reader s = q}

/-- Unknown mechanism means a union of the two separately defined source
images. It does not redraw a COMMON register or switch modes between rows. -/
noncomputable def wrongUnknownModeImage {Answer : Type*}
    (answer : OriginalTarget X → Answer) (wanted : Answer)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) : Set (PMF O) :=
  wrongNativeImage answer wanted false bin hbin reader ∪
    wrongNativeImage answer wanted true bin hbin reader

/-- Source-to-class consumer across arbitrary finite original carriers.
This is exact separation of raw native images; robust certification uses
their closure instead. A strict bound for each raw source is not a uniform gap. -/
theorem actual_source_class_separation_iff {Answer : Type*}
    (answer : OriginalTarget X → Answer) (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) (beta : ℝ) :
    allCorruptionsSeparated (nativeLaw mode bin hbin reader s)
      (wrongNativeImage answer (answer (sourceTarget s)) mode bin hbin reader) beta ↔
      ∀ r : OriginalParameters.{u,v,w,x} Copy X sample,
        answer (sourceTarget r) ≠ answer (sourceTarget s) →
        2 * beta < pmfTV (nativeLaw mode bin hbin reader s)
          (nativeLaw mode bin hbin reader r) := by
  rw [all_corruptions_separated_iff]
  constructor
  · intro h r hr
    exact h (nativeLaw mode bin hbin reader r) ⟨r, hr, rfl⟩
  · intro h q hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact h r hr

/-- The robust-law class is explicitly the WRONG SOURCE IMAGE CLOSURE.
This theorem does not derive a computable distance, compact minimizer, the
corrupted-image closure identity or the statistical finite-read conclusion. -/
theorem actual_source_closure_separation_iff {Answer : Type*}
    (answer : OriginalTarget X → Answer) (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) (beta : ℝ) :
    allCorruptionsSeparated (nativeLaw mode bin hbin reader s)
      (tvClosure (wrongNativeImage answer (answer (sourceTarget s))
        mode bin hbin reader)) beta ↔
      ∀ q ∈ tvClosure (wrongNativeImage answer (answer (sourceTarget s))
          mode bin hbin reader),
        2 * beta < pmfTV (nativeLaw mode bin hbin reader s) q :=
  all_corruptions_separated_iff _ _ beta

#print axioms sourceTarget
#print axioms observedRecord
#print axioms nativeLaw
#print axioms wrongNativeImage
#print axioms wrongUnknownModeImage
#print axioms actual_source_class_separation_iff
#print axioms actual_source_closure_separation_iff

end CloudG6.ActualSourceCorruptionClasses
