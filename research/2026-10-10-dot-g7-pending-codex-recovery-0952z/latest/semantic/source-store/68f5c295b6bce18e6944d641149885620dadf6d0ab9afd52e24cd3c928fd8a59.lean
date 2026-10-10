import G6NaturalCellInverseRates
import UnifiedLean.Source.SourceCalendarCompiler
import UnifiedLean.Source.SourceNaturalInitialization

/-! Shared G6/G7 original-ID chronological schema interface. This file defines
actual instantiation and one physical variable bank. Extraction from a realized
chronology signature and equality with the actual refined calendar remain to
be proved in the companion source adapter. No source-law equality is a field. -/
namespace UnifiedLean.G6.OriginalCalendarSchema
open Nanuq.Source GProgram.G5
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical NNReal

inductive Step (V E : Type*)
  | interval (younger older : AgeAtom V)
  | exit (edge : E)
  | enter (node : V)

def Step.isInterval {V E : Type*} : Step V E → Bool
  | .interval _ _ => true
  | _ => false

def Step.younger {V E : Type*} : Step V E → AgeAtom V
  | .interval a _ => a
  | _ => .fixed 0

def Step.older {V E : Type*} : Step V E → AgeAtom V
  | .interval _ b => b
  | _ => .fixed 0

theorem step_interval_of_flag {V E : Type*} (s : Step V E) (hs : s.isInterval=true) :
    s = .interval s.younger s.older := by
  cases s <;> simp_all [Step.isInterval,Step.younger,Step.older]

abbrev IntervalOccurrence {V E : Type*} (schema : List (Step V E)) :=
  {i : Fin schema.length // (schema.get i).isInterval = true}

def nonnegative {V E : Type*} (schema : List (Step V E)) (a : V → ℝ) : Prop :=
  ∀ i : IntervalOccurrence schema,
    (schema.get i.val).younger.eval a ≤ (schema.get i.val).older.eval a

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def instantiateStep (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) : Step V E → ProgramStep N
  | .interval a b => .interval (Real.toNNReal (b.eval C.age-a.eval C.age))
  | .exit e => .boundary (.exit e)
  | .enter v => .boundary (originalNodeOperation N H (originalGamma p) common v)

noncomputable def instantiate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (schema : List (Step V E)) : List (ProgramStep N) :=
  schema.map (instantiateStep N C H p common)

noncomputable def duration (N : RootedBinary V E X) (C : Calendar N.graph)
    (schema : List (Step V E)) (i : IntervalOccurrence schema) : ℝ≥0 :=
  Real.toNNReal ((schema.get i.val).older.eval C.age-(schema.get i.val).younger.eval C.age)

theorem duration_eq_literal (N : RootedBinary V E X) (C : Calendar N.graph)
    (schema : List (Step V E)) (hc : nonnegative schema C.age)
    (i : IntervalOccurrence schema) :
    (duration N C schema i : ℝ) =
      (schema.get i.val).older.eval C.age-(schema.get i.val).younger.eval C.age :=
  Real.coe_toNNReal _ (sub_nonneg.mpr (hc i))

theorem instantiate_interval (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (schema : List (Step V E))
    (i : IntervalOccurrence schema) :
    instantiateStep N C H p common (schema.get i.val) = .interval (duration N C schema i) := by
  rw [step_interval_of_flag (schema.get i.val) i.property]
  rfl

/-- One finite variable registry: each interval occurrence has the original
physical edge/root coordinates; every hybrid has ONE shared gamma variable. -/
abbrev Variable (N : RootedBinary V E X) (schema : List (Step V E)) :=
  (IntervalOccurrence schema × Option E) ⊕ Hybrid N

noncomputable def physicalVariables (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (p : HybridProbabilities N) (schema : List (Step V E)) :
    Variable N schema → ℝ
  | .inl (i,e) => Real.exp (-(pairRate r e)*(duration N C schema i : ℝ))
  | .inr h => p.gamma h

theorem physical_interval_coordinate (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (p : HybridProbabilities N) (schema : List (Step V E))
    (hc : nonnegative schema C.age) (i : IntervalOccurrence schema) (e : Option E) :
    physicalVariables N C r p schema (.inl (i,e)) =
      Real.exp (-(pairRate r e)*((schema.get i.val).older.eval C.age-
        (schema.get i.val).younger.eval C.age)) := by
  simp only [physicalVariables,duration_eq_literal N C schema hc]

@[simp] theorem physical_gamma_coordinate (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (p : HybridProbabilities N) (schema : List (Step V E))
    (h : Hybrid N) : physicalVariables N C r p schema (.inr h) = p.gamma h := rfl

end UnifiedLean.G6.OriginalCalendarSchema

namespace UnifiedLean.G6.OriginalCalendarSchema
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical NNReal

inductive Symbol (J V E : Type*)
  | interval (slot : J)
  | exit (edge : E)
  | enter (node : V)

noncomputable def symbolAt {V E : Type*} (schema : List (Step V E))
    (i : Fin schema.length) : Symbol (IntervalOccurrence schema) V E :=
  match h : schema.get i with
  | .interval _ _ => .interval ⟨i, by change (schema.get i).isInterval = true; rw [h]; rfl⟩
  | .exit e => .exit e
  | .enter v => .enter v

noncomputable def indexedSymbols {V E : Type*} (schema : List (Step V E)) :=
  List.ofFn (symbolAt schema)

variable {V E X J : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def instantiateSymbol (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (dur : J → ℝ≥0) : Symbol J V E → ProgramStep N
  | .interval j => .interval (dur j)
  | .exit e => .boundary (.exit e)
  | .enter v => .boundary (originalNodeOperation N H (originalGamma p) common v)

 theorem symbolAt_instantiates (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (schema : List (Step V E)) (i : Fin schema.length) :
    instantiateSymbol N H p common (duration N C schema) (symbolAt schema i) =
      instantiateStep N C H p common (schema.get i) := by
  unfold symbolAt
  split <;> rename_i h <;>
    simp only [List.get_eq_getElem] at h <;>
    simp_all [instantiateSymbol, instantiateStep, duration, Step.younger, Step.older,
      List.get_eq_getElem]


 theorem indexedSymbols_instantiates (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (schema : List (Step V E)) :
    (indexedSymbols schema).map (instantiateSymbol N H p common (duration N C schema)) =
      instantiate N C H p common schema := by
  simp only [indexedSymbols, List.map_ofFn, Function.comp_def, symbolAt_instantiates]
  simp [instantiate, ← List.map_ofFn]

end UnifiedLean.G6.OriginalCalendarSchema
