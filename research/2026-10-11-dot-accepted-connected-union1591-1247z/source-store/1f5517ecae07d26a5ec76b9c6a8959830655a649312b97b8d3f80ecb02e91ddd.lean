import G7SymbolicProgramPolynomial
import OriginalCalendarPattern

/-! The actual generated, naturally initialized calendar law has one rational
polynomial table throughout an original vertex-age order cell. The common word
is derived by the existing original calendar compiler, rather than supplied as
a desired-law equality. Coordinates remain actual interval survivals. -/
namespace GProgram.G7.NaturalCalendarPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.OriginalCalendarPattern
open GProgram.G7.SymbolicProgramPolynomial
open UnifiedLean.Source.SourceFiniteProjection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma instantiateGamma_original (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) {J : Type*} (dur : J → ℝ≥0) :
    instantiateGamma N H (originalGamma p) common dur = instantiateSymbol N H p common dur := by
  funext op
  cases op <;> rfl

lemma actual_initialized_schema (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    initializedWordLaw N sample H p common r (duration N D (calendarSchema N C))
      (indexedSymbols (calendarSchema N C)) = naturalCalendarLaw N D sample H p common r := by
  unfold initializedWordLaw naturalCalendarLaw
  rw [instantiateGamma_original,indexedSymbols_instantiates,actual_calendar_schema N C D h]

/-- The same table serves all positive physical banks and all actual calendars
with the reference calendar's weak vertex-age order. Shared physical rates and
original hybrid probabilities are substituted together. -/
theorem actual_natural_calendar_polynomial (N : RootedBinary V E X)
    (C D : Calendar N.graph) (h : SameOrder C.age D.age) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    wordEval N r (originalGamma p) (duration N D (calendarSchema N C))
      (naturalWordPolynomial N sample H common (indexedSymbols (calendarSchema N C)) b) =
      (((naturalCalendarLaw N D sample H p common r).map (projection N Finset.univ)) b).toReal := by
  rw [← actual_initialized_schema N C D h sample H p common r]
  exact actual_natural_word_polynomial N sample H p common r _ _ b

end GProgram.G7.NaturalCalendarPolynomial
