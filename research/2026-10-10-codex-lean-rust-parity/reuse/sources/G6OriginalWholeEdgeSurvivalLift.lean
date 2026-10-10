import UnifiedLean.Source.NativePairClockLaw
import UnifiedLean.Source.NativeIndependentPairMixture
import G4OrdinaryTripletReadout

/-!
# Whole-edge survival coordinates realize one actual original physical bank

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
Reuse of the existing positive exponential-duration lift, on a supplied actual
original Calendar. Each original edge occurrence has its own freely assignable
positive rate. All coordinates are realized simultaneously, with ancestral
rate one and supplied interior original hybrid coins.

This image theorem concerns WHOLE original-edge durations. Shared rates across
several cut/bin segments impose additional ties; no arbitrary exposure chart,
calendar existence, observation admission or source-size census is inferred.
The real logarithmic bank is noncomputable, not a native rational extraction.
-/
namespace UnifiedLean.G6.OriginalWholeEdgeSurvivalLift

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open G4OrdinaryTripletReadout

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X) (C : Calendar N.graph)

noncomputable def wholeEdgeDuration (e : E) : ℝ :=
  C.age (N.graph.source e) - C.age (N.graph.target e)

theorem wholeEdgeDuration_positive (e : E) : 0 < wholeEdgeDuration N C e :=
  sub_pos.mpr (C.edge_older e)

noncomputable def wholeEdgeSurvivals (r : PositivePairRates E) (e : E) : ℝ :=
  Real.exp (-(pairRate r (some e) * wholeEdgeDuration N C e))

/-- Positivity of the actual physical bank puts every entire-edge survival
strictly inside the open unit cube. -/
theorem wholeEdgeSurvivals_interior (r : PositivePairRates E) (e : E) :
    0 < wholeEdgeSurvivals N C r e ∧ wholeEdgeSurvivals N C r e < 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  have hm : 0 < pairRate r (some e) * wholeEdgeDuration N C e :=
    mul_pos (pairRate_pos r _) (wholeEdgeDuration_positive N C e)
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hm)

/-- One simultaneous bank on the SAME actual calendar and original edge IDs.
No existence choice or fitted source law is involved in the construction. -/
noncomputable def ratesOfWholeEdgeSurvivals (z : E → ℝ)
    (hpos : ∀ e, 0 < z e) (hone : ∀ e, z e < 1) : PositivePairRates E where
  edge e := canonicalDuration (z e) / wholeEdgeDuration N C e
  edge_pos e := div_pos (canonicalDuration_positive (hpos e) (hone e))
    (wholeEdgeDuration_positive N C e)
  ancestral := 1
  ancestral_pos := zero_lt_one

theorem lifted_whole_edge_exposure (z : E → ℝ)
    (hpos : ∀ e, 0 < z e) (hone : ∀ e, z e < 1) (e : E) :
    pairRate (ratesOfWholeEdgeSurvivals N C z hpos hone) (some e) *
        wholeEdgeDuration N C e = canonicalDuration (z e) := by
  change (canonicalDuration (z e) / wholeEdgeDuration N C e) *
    wholeEdgeDuration N C e = canonicalDuration (z e)
  exact div_mul_cancel₀ _ (ne_of_gt (wholeEdgeDuration_positive N C e))

theorem lifted_whole_edge_survival (z : E → ℝ)
    (hpos : ∀ e, 0 < z e) (hone : ∀ e, z e < 1) (e : E) :
    wholeEdgeSurvivals N C (ratesOfWholeEdgeSurvivals N C z hpos hone) e = z e := by
  rw [wholeEdgeSurvivals, lifted_whole_edge_exposure]
  exact canonicalDuration_survival (hpos e)

theorem lifted_whole_edge_survivals (z : E → ℝ)
    (hpos : ∀ e, 0 < z e) (hone : ∀ e, z e < 1) :
    wholeEdgeSurvivals N C (ratesOfWholeEdgeSurvivals N C z hpos hone) = z := by
  funext e
  exact lifted_whole_edge_survival N C z hpos hone e

theorem lifted_ancestral_rate (z : E → ℝ)
    (hpos : ∀ e, 0 < z e) (hone : ∀ e, z e < 1) :
    pairRate (ratesOfWholeEdgeSurvivals N C z hpos hone) none = 1 := rfl

/-- The inverse also recovers every original edge rate at this fixed calendar.
Whole-edge coordinates alone do not determine the ancestral rate. -/
theorem lift_recovers_edge_rates (r : PositivePairRates E) :
    (ratesOfWholeEdgeSurvivals N C (wholeEdgeSurvivals N C r)
      (fun e => (wholeEdgeSurvivals_interior N C r e).1)
      (fun e => (wholeEdgeSurvivals_interior N C r e).2)).edge = r.edge := by
  funext e
  change (-Real.log (Real.exp (-(r.edge e * wholeEdgeDuration N C e)))) /
    wholeEdgeDuration N C e = r.edge e
  rw [Real.log_exp, neg_neg]
  exact mul_div_cancel_right₀ _ (ne_of_gt (wholeEdgeDuration_positive N C e))

/-- Exact physical image of the WHOLE-edge survival map, on a supplied
calendar with independent positive original-edge rates. -/
theorem whole_edge_image_iff (z : E → ℝ) :
    (∃ r : PositivePairRates E, wholeEdgeSurvivals N C r = z) ↔
      ∀ e, 0 < z e ∧ z e < 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact wholeEdgeSurvivals_interior N C r
  · intro hz
    exact ⟨ratesOfWholeEdgeSurvivals N C z (fun e => (hz e).1) (fun e => (hz e).2),
      lifted_whole_edge_survivals N C z (fun e => (hz e).1) (fun e => (hz e).2)⟩

/-- Actual same-source inheritance coordinates can be supplied jointly with
all entire-edge survivals on the one original graph/calendar bank. -/
theorem whole_edge_and_coin_image_iff (z : E → ℝ) (g : Hybrid N → ℝ) :
    (∃ r : PositivePairRates E, ∃ p : HybridProbabilities N,
      pairRate r none = 1 ∧ wholeEdgeSurvivals N C r = z ∧ p.gamma = g) ↔
      (∀ e, 0 < z e ∧ z e < 1) ∧ (∀ h, 0 < g h ∧ g h < 1) := by
  constructor
  · rintro ⟨r, p, _, hz, hg⟩
    constructor
    · rw [← hz]
      exact wholeEdgeSurvivals_interior N C r
    · rw [← hg]
      exact fun h => ⟨p.positive h, p.below_one h⟩
  · rintro ⟨hz, hg⟩
    refine ⟨ratesOfWholeEdgeSurvivals N C z (fun e => (hz e).1) (fun e => (hz e).2),
      ⟨g, fun h => (hg h).1, fun h => (hg h).2⟩, rfl, ?_, rfl⟩
    exact lifted_whole_edge_survivals N C z (fun e => (hz e).1) (fun e => (hz e).2)

#print axioms wholeEdgeDuration_positive
#print axioms wholeEdgeSurvivals_interior
#print axioms ratesOfWholeEdgeSurvivals
#print axioms lifted_whole_edge_survivals
#print axioms lift_recovers_edge_rates
#print axioms whole_edge_image_iff
#print axioms whole_edge_and_coin_image_iff

end UnifiedLean.G6.OriginalWholeEdgeSurvivalLift
