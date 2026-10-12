import G5FairRawDisplayedQuartetIdentification

/-!
# Finite original labels need no supplied order for the raw fair-M2 theorem
Contributor: dot / OpenAI, 2026-10-03.
A single order of the shared finite ORIGINAL labels is constructed internally
and used in both source chronologies. It is not an additional source premise.
The target remains the inherited actual raw displayed resolved-quartet union;
normalized pruning/root-suppression semantics are not silently redefined.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativeFairCurrentPosition
open scoped Classical
variable {V E X V₂ E₂ : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

/-- One fixed ordering of the shared original label set, constructed from its
finite enumeration. Neither graph, law nor rate affects the order. -/
noncomputable def sharedOriginalLabelOrder (X : Type*) [Fintype X] : LinearOrder X :=
  LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective

/-- Full ACTUAL RAW displayed-quartet identification, with no supplied label
order or chronology. No diagonal original-tip observations are required. -/
theorem fair_m2_identifies_actual_raw_displayed_quartets
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    {s : ℝ} (htips : ∀ x : X, C.age (N.leaf x) = s) (htips₂ : ∀ x : X, C₂.age (N₂.leaf x) = s)
    (heq : ∀ x y : X, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ∀ q : Fin 4 ↪ X, N.rawDisplayedQuartets q = N₂.rawDisplayedQuartets q := by
  letI : LinearOrder X := sharedOriginalLabelOrder X
  exact equal_fair_pair_calendar_laws_identify_raw_displayed_quartets N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
    htips htips₂ heq

#print axioms fair_m2_identifies_actual_raw_displayed_quartets
#check @fair_m2_identifies_actual_raw_displayed_quartets
end GProgram.G5.AttainedChronology
