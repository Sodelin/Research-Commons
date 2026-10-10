import G7ControlledWordPolynomial
import G7NaturalCalendarPolynomial

/-! Actual generated calendars under ORIGINAL-ID masks. The shared G6 schema
is instantiated with arbitrary unit-interval node probabilities, permitting
forced endpoints without replacing the strict natural initialization bank. -/
namespace GProgram.G7.ControlledCalendarPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.OriginalCalendarPattern
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.ControlledWordPolynomial
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def instantiateGammaStep (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) : Step V E → ProgramStep N
  | .interval a b => .interval (Real.toNNReal (b.eval C.age-a.eval C.age))
  | .exit e => .boundary (.exit e)
  | .enter v => .boundary (originalNodeOperation N H gamma common v)

lemma indexedSymbols_gamma (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (schema : List (Step V E)) :
    (indexedSymbols schema).map (instantiateGamma N H gamma common (duration N C schema)) =
      schema.map (instantiateGammaStep N C H gamma common) := by
  have he (i : Fin schema.length) :
      instantiateGamma N H gamma common (duration N C schema) (symbolAt schema i) =
        instantiateGammaStep N C H gamma common (schema.get i) := by
    unfold symbolAt
    split <;> rename_i h <;>
      simp only [List.get_eq_getElem] at h <;>
      simp_all [instantiateGamma,instantiateGammaStep,duration,Step.younger,Step.older,
        List.get_eq_getElem]
  simp only [indexedSymbols,List.map_ofFn,Function.comp_def,he]
  simp [← List.map_ofFn]

lemma boundary_gamma (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (v : V) :
    (boundarySchema N C.age v).map (instantiateGammaStep N D H gamma common) =
      boundaryOperations N D H gamma common (D.age v) := by
  rw [boundary_schema_stable N h]
  simp [boundarySchema,boundaryOperations,List.map_map,Function.comp_def,instantiateGammaStep]

lemma tail_gamma (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (v : V) (vs : List V) :
    (tailSchema N C.age v vs).map (instantiateGammaStep N D H gamma common) =
      calendarTail N D H gamma common (D.age v) (vs.map D.age) := by
  induction vs generalizing v with
  | nil => rfl
  | cons w ws ih =>
    simp only [tailSchema,List.map_cons,List.map_append,instantiateGammaStep,
      UnifiedLean.G6.NaturalCellInverseRates.AgeAtom.eval,calendarTail]
    rw [boundary_gamma N C D h H gamma common w,ih w]

lemma actual_gamma_calendar_schema (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    (indexedSymbols (calendarSchema N C)).map
        (instantiateGamma N H gamma common (duration N D (calendarSchema N C))) =
      compiledCalendarProgram N D H gamma common := by
  rw [indexedSymbols_gamma]
  unfold calendarSchema compiledCalendarProgram
  rw [← representatives_retime N C D h]
  cases hv : representatives N C with
  | nil => rfl
  | cons v vs =>
    simp only [List.map_cons,List.map_append]
    exact congrArg₂ (· ++ ·) (boundary_gamma N C D h H gamma common v)
      (tail_gamma N C D h H gamma common v vs)

lemma actual_controlled_schema (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (mask : OriginalMask N)
    (r : PositivePairRates E) :
    controlledWordLaw N sample H p common mask r (duration N D (calendarSchema N C))
      (indexedSymbols (calendarSchema N C)) = controlledCalendarLaw N D sample H p common r mask := by
  unfold controlledWordLaw controlledCalendarLaw controlledCalendarProgram
  rw [actual_gamma_calendar_schema N C D h]

/-- One rational table for every actual controlled original calendar in the
fixed age-order cell. Physical rates and natural register probabilities are
shared across rows; forcing is polynomial substitution at the named nodes. -/
theorem actual_controlled_calendar_polynomial (N : RootedBinary V E X)
    (C D : Calendar N.graph) (h : SameOrder C.age D.age) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (mask : OriginalMask N) (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    wordEval N r (originalGamma p) (duration N D (calendarSchema N C))
      (controlledWordPolynomial N sample H common mask (indexedSymbols (calendarSchema N C)) b) =
      (((controlledCalendarLaw N D sample H p common r mask).map
        (projection N Finset.univ)) b).toReal := by
  rw [← actual_controlled_schema N C D h sample H p common mask r]
  exact actual_controlled_word_polynomial N sample H p common mask r _ _ b

end GProgram.G7.ControlledCalendarPolynomial
