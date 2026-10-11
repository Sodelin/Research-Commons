import G7SelectedCompletionPolynomial
import G7ControlledCalendarPolynomial

/-! Composition of reviewed actual calendar polynomials with actual ancestral
completion, through the full selected carrier and derived source root support.
Natural and controlled source endpoints retain the same original bank. -/
namespace GProgram.G7.CompletedCalendarPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.OriginalCalendarPattern
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.NaturalCalendarPolynomial
open GProgram.G7.ControlledWordPolynomial GProgram.G7.ControlledCalendarPolynomial
open GProgram.G7.SelectedCompletionPolynomial
open scoped Classical BigOperators NNReal
variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

noncomputable def completedPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (q : SelectedIndex N sample Finset.univ → MvPolynomial (WordVariable N J) ℚ)
    (b : SelectedIndex N sample Finset.univ) : MvPolynomial (WordVariable N J) ℚ :=
  ∑ a, q a * MvPolynomial.C (completionRational N a b)

/-- Generic finite algebra assembly. Both law premises are discharged by the
actual original calendar and its derived ancestral support in consumers below. -/
theorem actual_root_law_completed_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (law : PMF (Code N sample)) (hroot : ∀ s ∈ law.support, AncestralRoot N s)
    (q : SelectedIndex N sample Finset.univ → MvPolynomial (WordVariable N J) ℚ)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (hq : ∀ a, wordEval N r gamma dur (q a) = ((law.map (projection N Finset.univ)) a).toReal)
    (b : SelectedIndex N sample Finset.univ) :
    wordEval N r gamma dur (completedPolynomial N q b) =
      (((law.bind (completionKernel N r)).map (projection N Finset.univ)) b).toReal := by
  rw [actual_root_law_completion_projection N r law hroot,bind_probability_real,tsum_fintype]
  simp only [completedPolynomial,wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C,Rat.coe_castHom]
  apply Finset.sum_congr rfl
  intro a _
  change wordEval N r gamma dur (q a) * (completionRational N a b : ℝ) = _
  rw [hq a]
  by_cases ha : a ∈ (law.map (projection N Finset.univ)).support
  · rw [actual_selected_completion_rational N a b (projected_root_support N law hroot ha) r]
  · have hz : (law.map (projection N Finset.univ)) a = 0 := by
      simpa only [PMF.mem_support_iff,not_not] using ha
    simp [hz]

/-- Actual naturally initialized, graph-generated, infinitely completed source
law. Neither polynomial rows nor ancestral support are supplied as hypotheses. -/
theorem actual_natural_completed_calendar_polynomial (N : RootedBinary V E X)
    (C D : Calendar N.graph) (h : SameOrder C.age D.age) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    wordEval N r (originalGamma p) (duration N D (calendarSchema N C))
      (completedPolynomial N (naturalWordPolynomial N sample H common
        (indexedSymbols (calendarSchema N C))) b) =
      (((naturalCompletedLaw N D sample H p common r).map (projection N Finset.univ)) b).toReal := by
  exact actual_root_law_completed_polynomial N (naturalCalendarLaw N D sample H p common r)
    (fun s hs => natural_calendar_ancestral_support N D sample H p common r hs)
    _ r (originalGamma p) _ (fun a => actual_natural_calendar_polynomial N C D h sample H p common r a) b

/-- Actual fixed-original-ID controlled complete calendar law. Only transition
nodes are forced; the natural once-drawn initial register is retained. -/
theorem actual_controlled_completed_calendar_polynomial (N : RootedBinary V E X)
    (C D : Calendar N.graph) (h : SameOrder C.age D.age) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (mask : OriginalMask N) (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    wordEval N r (originalGamma p) (duration N D (calendarSchema N C))
      (completedPolynomial N (controlledWordPolynomial N sample H common mask
        (indexedSymbols (calendarSchema N C))) b) =
      (((controlledCompletedLaw N D sample H p common r mask).map
        (projection N Finset.univ)) b).toReal := by
  exact actual_root_law_completed_polynomial N (controlledCalendarLaw N D sample H p common r mask)
    (fun s hs => controlled_calendar_ancestral_support N D sample H p common r mask hs)
    _ r (originalGamma p) _
    (fun a => actual_controlled_calendar_polynomial N C D h sample H p common mask r a) b

end GProgram.G7.CompletedCalendarPolynomial
