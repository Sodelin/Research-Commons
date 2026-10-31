import ResearchCommons.MSCI.JC69Source
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Original observed-locus Fourier/mixture interchange. UNCOMPILED candidate,
31 October 2026. Contributor: dot (OpenAI). Depends only on accepted source
probability and measurability; not on the uncompiled clock composition. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69ObservedFourier
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.NativeParentRouting
open GProgram.G2.CompleteCalendarAttachment
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Source
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Exact full original-label character across sites in ONE locus. -/
def originalCharacter (L : ℕ) (q : Fin L → Copy → Base)
    (p : Fin L → Copy → Base) : ℝ := ∏ j, ∏ x, character (q j x) (p j x)

/-- The observable Fourier coefficient of the actual original locus PMF. -/
def observedFourier (L : ℕ) (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (q : Fin L → Copy → Base) : ℝ :=
  ∑ p, (actualLocusLaw L N C sample register H gamma common r p).toReal *
    originalCharacter L q p

/-- Finite integral is derived from the actual PMF mass, not postulated for
an exponential representation. The fallback kernel is retained off support. -/
theorem original_mass_integrable (L : ℕ) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (p : Fin L → Copy → Base) :
    Integrable (fun z => (conditionalLocusKernel L N
      (fun x => C.age (N.leaf (sample x)))
      (originalPoint N C sample register H gamma common z) p).toReal)
      (completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register)) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact ((conditional_locus_mass_measurable L N _ p).comp
      (original_point_measurable N C sample register H gamma common)).aemeasurable
  · change actualLocusLaw L N C sample register H gamma common r p ≠ ⊤
    exact PMF.apply_ne_top _ _

/-- Genuine observed-mixture interchange. All sites remain inside the SAME
conditional source point. No balanced-charge or artificial occupation law
assumption is needed for this finite linearity identity. -/
theorem actual_observed_fourier_integral (L : ℕ) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (q : Fin L → Copy → Base) :
    observedFourier L N C sample register H gamma common r q =
      ∫ z, ∑ p, (conditionalLocusKernel L N
        (fun x => C.age (N.leaf (sample x)))
        (originalPoint N C sample register H gamma common z) p).toReal *
          originalCharacter L q p
      ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register) := by
  rw [integral_finsetSum Finset.univ (fun p _ =>
    (original_mass_integrable L N C sample register H gamma common r p).mul_const
      (originalCharacter L q p))]
  unfold observedFourier
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_mul_const]
  congr 1
  symm
  change (∫ z, (conditionalLocusKernel L N
    (fun x => C.age (N.leaf (sample x)))
    (originalPoint N C sample register H gamma common z) p).toReal
    ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)) = _
  apply integral_toReal
  · exact ((conditional_locus_mass_measurable L N _ p).comp
      (original_point_measurable N C sample register H gamma common)).aemeasurable
  · exact Filter.Eventually.of_forall (fun z => lt_top_iff_ne_top.mpr (PMF.apply_ne_top _ _))

#print axioms original_mass_integrable
#print axioms actual_observed_fourier_integral
end ResearchCommons.MSCI.JC69ObservedFourier
