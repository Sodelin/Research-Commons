import G7WholeEdgeExposureInvariant
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact physical image of the original independent-edge source contract

Contributor: dot, 2026-10-10. Uncompiled full-endpoint candidate. The old G7
hand proof is the source of the rate/length realization argument. A fixed strict
calendar realizes every positive finite original-edge exposure and every point
of the open survival cube. The logarithmic REALIZATION is not asserted to be
algebraic; algebraic policy synthesis acts on the represented cube.
-/
namespace GProgram.G7.OriginalSurvivalCoverage
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.OriginalFixedIDControls UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open GProgram.G7.WholeEdgeExposureInvariant
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def exposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) : ℝ :=
  r.edge e * (C.age (N.graph.source e)-C.age (N.graph.target e))

lemma exposure_pos (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) : 0 < exposure N C r e :=
  mul_pos (r.edge_pos e) (sub_pos.mpr (C.edge_older e))

/-- No equality is imposed between different original edge rates. -/
noncomputable def ratesFromLengths (N : RootedBinary V E X) (C : Calendar N.graph)
    (ell : E → ℝ) (h : ∀ e, 0 < ell e) : PositivePairRates E where
  edge e := ell e / (C.age (N.graph.source e)-C.age (N.graph.target e))
  edge_pos e := div_pos (h e) (sub_pos.mpr (C.edge_older e))
  ancestral := 1
  ancestral_pos := zero_lt_one

lemma ratesFromLengths_exposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (ell : E → ℝ) (h : ∀ e, 0 < ell e) (e : E) :
    exposure N C (ratesFromLengths N C ell h) e = ell e := by
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (C.edge_older e)))

noncomputable def survival (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) : ℝ := Real.exp (-exposure N C r e)

def OpenCube (x : E → ℝ) : Prop := ∀ e, 0 < x e ∧ x e < 1

lemma physical_survival_open_cube (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) : OpenCube (survival N C r) := by
  intro e
  exact ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos (exposure_pos N C r e))⟩

noncomputable def ratesFromSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : E → ℝ) (hx : OpenCube x) : PositivePairRates E :=
  ratesFromLengths N C (fun e => -Real.log (x e))
    (fun e => neg_pos.mpr (Real.log_neg (hx e).1 (hx e).2))

lemma ratesFromSurvival_exposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : E → ℝ) (hx : OpenCube x) (e : E) :
    exposure N C (ratesFromSurvival N C x hx) e = -Real.log (x e) :=
  ratesFromLengths_exposure N C _ _ e

lemma ratesFromSurvival_survival (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : E → ℝ) (hx : OpenCube x) : survival N C (ratesFromSurvival N C x hx) = x := by
  funext e
  rw [survival,ratesFromSurvival_exposure,neg_neg,Real.exp_log (hx e).1]

/-- Equality of survival vectors is precisely equality of whole-edge exposures. -/
lemma survival_eq_iff_exposure (N : RootedBinary V E X) (C D : Calendar N.graph)
    (r s : PositivePairRates E) :
    survival N C r = survival N D s ↔ SameWholeEdgeExposure N C D r s := by
  constructor
  · intro h e
    have he := congrFun h e
    exact neg_injective (Real.exp_injective he)
  · intro h
    funext e
    exact congrArg (fun a : ℝ => Real.exp (-a)) (h e)

/-- Exact image, not merely density or a collection of interval coordinates. -/
theorem fixed_calendar_survival_image (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : E → ℝ) : (∃ r : PositivePairRates E, survival N C r = x) ↔ OpenCube x := by
  constructor
  · rintro ⟨r,rfl⟩
    exact physical_survival_open_cube N C r
  · intro hx
    exact ⟨ratesFromSurvival N C x hx,ratesFromSurvival_survival N C x hx⟩

/-- Every physical source has a representative on any chosen strict calendar,
using the same graph, parent registry, natural parameters and original mask. -/
theorem every_actual_source_has_fixed_calendar_representative (N : RootedBinary V E X)
    (C C₀ : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ∃ r₀ : PositivePairRates E,
      survival N C₀ r₀ = survival N C r ∧
      naturalCompletedLaw N C sample H p common r = naturalCompletedLaw N C₀ sample H p common r₀ ∧
      ∀ mask : OriginalMask N,
        controlledCompletedLaw N C sample H p common r mask =
          controlledCompletedLaw N C₀ sample H p common r₀ mask := by
  let r₀ := ratesFromLengths N C₀ (exposure N C r) (exposure_pos N C r)
  have he : SameWholeEdgeExposure N C C₀ r r₀ := by
    intro e
    exact (ratesFromLengths_exposure N C₀ _ _ e).symm
  refine ⟨r₀,((survival_eq_iff_exposure N C C₀ r r₀).mpr he).symm,?_,?_⟩
  · exact actual_natural_completed_exposure_invariant N C C₀ sample H p common r r₀ he
  · intro mask
    exact actual_controlled_completed_exposure_invariant N C C₀ sample H p common r r₀ mask he

/-- Direct whole-family consumer: a point of the independent open cube names an
actual original source, and every actual source with that point has exactly its
natural and ALL original controlled completed laws. No finite readout or panel
nonemptiness premise is needed. -/
theorem actual_source_survival_chart (N : RootedBinary V E X) (C₀ : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (x : E → ℝ) (hx : OpenCube x) :
    let r₀ := ratesFromSurvival N C₀ x hx
    survival N C₀ r₀ = x ∧
      ∀ (C : Calendar N.graph) (r : PositivePairRates E), survival N C r = x →
        naturalCompletedLaw N C sample H p common r = naturalCompletedLaw N C₀ sample H p common r₀ ∧
        ∀ mask : OriginalMask N,
          controlledCompletedLaw N C sample H p common r mask =
            controlledCompletedLaw N C₀ sample H p common r₀ mask := by
  dsimp only
  have h₀ := ratesFromSurvival_survival N C₀ x hx
  refine ⟨h₀,?_⟩
  intro C r hr
  have he := (survival_eq_iff_exposure N C C₀ r _).mp (hr.trans h₀.symm)
  refine ⟨actual_natural_completed_exposure_invariant N C C₀ sample H p common r _ he,?_⟩
  intro mask
  exact actual_controlled_completed_exposure_invariant N C C₀ sample H p common r _ mask he

end GProgram.G7.OriginalSurvivalCoverage
