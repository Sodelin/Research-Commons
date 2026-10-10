import G7CalendarFrontierOrder
import G7AncestralRationalCompletion
import UnifiedLean.Source.ControlledUnrankedSourceProjectivity
import UnifiedLean.Source.SourceCompletedUnrankedTree

/-!
# Original whole-edge exposure invariance, including actual completion

Contributor: dot, 2026-10-10. Formalization of the attributed original G7
frontier argument. This candidate is UNCOMPILED. It compares the literal source
laws on the SAME graph, original registry, natural bank and control row, while
allowing arbitrary strict calendars and positive edge-specific rate banks with
the same whole-edge exposures. It supplies no timed or binned retiming claim.
-/
namespace GProgram.G7.WholeEdgeExposureInvariant
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.OriginalFixedIDControls UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.Source.SourceCompletedUnrankedTree
open GProgram.G7.OriginalEdgeGathering GProgram.G7.CalendarExposureClosedForm
open GProgram.G7.OrderedFrontierProduct GProgram.G7.CalendarFrontierOrder
open GProgram.G7.AncestralRationalCompletion
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The original contract's independent positive whole-edge coalescent lengths.
This relation neither separates overlapping calendar intervals into independent
coordinates nor assumes a supplied-word equality. -/
def SameWholeEdgeExposure (N : RootedBinary V E X) (C D : Calendar N.graph)
    (r s : PositivePairRates E) : Prop :=
  ∀ e : E, r.edge e * (C.age (N.graph.source e)-C.age (N.graph.target e)) =
    s.edge e * (D.age (N.graph.source e)-D.age (N.graph.target e))

lemma wholeEdgeBank_eq (N : RootedBinary V E X) (C D : Calendar N.graph)
    (r s : PositivePairRates E) (h : SameWholeEdgeExposure N C D r s) :
    wholeEdgeBank N C r = wholeEdgeBank N D s := by
  funext i
  cases i with
  | none => rfl
  | some e => exact h e

/-- Full generated calendar equality conditional on one fixed original seed.
The endpoint is the inherited full Code, including retained unranked genealogy.
No assumption about calendar order, bridges or nonparallel edges is introduced. -/
theorem actual_initialized_calendar_exposure_invariant (N : RootedBinary V E X)
    (C D : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r s : PositivePairRates E)
    (h : SameWholeEdgeExposure N C D r s) :
    sourceProgram N r (compiledCalendarProgram N C H gamma common) (initialCode N sample register) =
      sourceProgram N s (compiledCalendarProgram N D H gamma common) (initialCode N sample register) := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [actual_initialized_whole_edge_frontier,actual_initialized_whole_edge_frontier,
    wholeEdgeFrontier_matrix_atoms,wholeEdgeFrontier_matrix_atoms,
    wholeEdgeBank_eq N C D r s h,
    actual_calendar_frontier_order_independent N C D H gamma common]

/-- The natural original register is sampled exactly once and remains the same
in both calendar evaluations. -/
theorem actual_natural_calendar_exposure_invariant (N : RootedBinary V E X)
    (C D : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r s : PositivePairRates E)
    (h : SameWholeEdgeExposure N C D r s) :
    naturalCalendarLaw N C sample H p common r = naturalCalendarLaw N D sample H p common s := by
  unfold naturalCalendarLaw
  congr 1
  funext register
  exact actual_initialized_calendar_exposure_invariant N C D sample register H
    (originalGamma p) common r s h

/-- Forced node probabilities are changed only inside the transition word.
The initializer still uses originalRegisterPMF at the natural interior p. -/
theorem actual_controlled_calendar_exposure_invariant (N : RootedBinary V E X)
    (C D : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r s : PositivePairRates E)
    (mask : OriginalMask N) (h : SameWholeEdgeExposure N C D r s) :
    controlledCalendarLaw N C sample H p common r mask =
      controlledCalendarLaw N D sample H p common s mask := by
  unfold controlledCalendarLaw controlledCalendarProgram
  congr 1
  funext register
  exact actual_initialized_calendar_exposure_invariant N C D sample register H
    (controlledGamma p mask) (controlledMode common mask) r s h

/-- Positive ancestral rates have the same actual root-supported completion.
The inherited rational completion theorem handles nonempty panels; the empty
panel is handled directly, so no Nonempty Copy hypothesis is added. -/
theorem actual_completion_rate_invariant (N : RootedBinary V E X) {sample : Copy → X}
    (r s : PositivePairRates E) (d : Code N sample) (hd : AncestralRoot N d) :
    completionKernel N r d = completionKernel N s d := by
  by_cases hc : Nonempty Copy
  · letI : Nonempty Copy := hc
    apply PMF.ext
    intro z
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    exact (actual_completion_rational N d z hd r).symm.trans
      (actual_completion_rational N d z hd s)
  · letI : IsEmpty Copy := ⟨fun x => hc ⟨x⟩⟩
    simp [completionKernel,ancestralCompletion]

/-- Literal completed natural source law, not merely a factorization of a
selected readout. Existing actual calendar support discharges the root premise. -/
theorem actual_natural_completed_exposure_invariant (N : RootedBinary V E X)
    (C D : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r s : PositivePairRates E)
    (h : SameWholeEdgeExposure N C D r s) :
    naturalCompletedLaw N C sample H p common r = naturalCompletedLaw N D sample H p common s := by
  change (naturalCalendarLaw N C sample H p common r).bind (completionKernel N r) =
    (naturalCalendarLaw N D sample H p common s).bind (completionKernel N s)
  rw [actual_natural_calendar_exposure_invariant N C D sample H p common r s h]
  apply bind_congr_on_support
  intro d hd
  exact actual_completion_rate_invariant N r s d
    (natural_calendar_ancestral_support N D sample H p common s hd)

/-- Same-source, original-ID controlled completed law for every legal row. -/
theorem actual_controlled_completed_exposure_invariant (N : RootedBinary V E X)
    (C D : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r s : PositivePairRates E)
    (mask : OriginalMask N) (h : SameWholeEdgeExposure N C D r s) :
    controlledCompletedLaw N C sample H p common r mask =
      controlledCompletedLaw N D sample H p common s mask := by
  unfold controlledCompletedLaw
  rw [actual_controlled_calendar_exposure_invariant N C D sample H p common r s mask h]
  apply bind_congr_on_support
  intro d hd
  exact actual_completion_rate_invariant N r s d
    (controlled_calendar_ancestral_support N D sample H p common s mask hd)

/-- Actual complete rooted unranked forest law, including the empty panel. -/
theorem actual_natural_unranked_exposure_invariant (N : RootedBinary V E X)
    (C D : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r s : PositivePairRates E)
    (h : SameWholeEdgeExposure N C D r s) :
    naturalCompletedUnrankedLaw N C sample H p common r =
      naturalCompletedUnrankedLaw N D sample H p common s := by
  unfold naturalCompletedUnrankedLaw
  rw [actual_natural_completed_exposure_invariant N C D sample H p common r s h]

theorem actual_controlled_unranked_exposure_invariant (N : RootedBinary V E X)
    (C D : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r s : PositivePairRates E)
    (mask : OriginalMask N) (h : SameWholeEdgeExposure N C D r s) :
    controlledCompletedUnrankedLaw N C sample H p common r mask =
      controlledCompletedUnrankedLaw N D sample H p common s mask := by
  unfold controlledCompletedUnrankedLaw
  rw [actual_controlled_completed_exposure_invariant N C D sample H p common r s mask h]

/-- The equality transports every fixed final readout and finite selection of
coordinates. It does not transport a clocked history or timed bin decoder. -/
theorem actual_controlled_readout_exposure_invariant {O : Type*}
    (N : RootedBinary V E X) (C D : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r s : PositivePairRates E) (mask : OriginalMask N) (readout : Code N sample → O)
    (h : SameWholeEdgeExposure N C D r s) :
    (controlledCompletedLaw N C sample H p common r mask).map readout =
      (controlledCompletedLaw N D sample H p common s mask).map readout := by
  rw [actual_controlled_completed_exposure_invariant N C D sample H p common r s mask h]

end GProgram.G7.WholeEdgeExposureInvariant
