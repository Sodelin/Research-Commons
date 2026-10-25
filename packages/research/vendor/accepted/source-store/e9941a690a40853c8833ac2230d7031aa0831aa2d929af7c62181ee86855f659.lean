import G7AncestralRationalCompletion
import G7SelectedKernelPolynomial
import UnifiedLean.Source.SourceNaturalCompletedLimit

/-! Integration adapter from the actual full selected forest to the actual
ancestral completion kernel. Root support is derived from the retained location
coordinates. This does not identify the selected carrier with raw Code. -/
namespace GProgram.G7.SelectedCompletionPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Filter
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceEventualCompletionLimit UnifiedLean.Source.SourceNaturalCompletedLimit
open GProgram.G7.SelectedKernelPolynomial GProgram.G7.AncestralPolynomialKernel
open GProgram.G7.AncestralRationalCompletion
open scoped Classical BigOperators NNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

def FullRoot (N : RootedBinary V E X) {sample : Copy → X}
    (a : SelectedIndex N sample Finset.univ) : Prop :=
  ∀ x, a.val.population x = some (.rootPopulation N.root)

lemma actual_root_projection (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) : FullRoot N (projection N Finset.univ s) := by
  intro x
  simpa [projection,selectedView,selectedLocation] using congrArg some (hs x)

lemma representative_ancestral (N : RootedBinary V E X) {sample : Copy → X}
    (a : SelectedIndex N sample Finset.univ) (ha : FullRoot N a) :
    AncestralRoot N (representative N Finset.univ a) := by
  intro x
  have h := congrArg (fun v : SelectedView V E Copy => v.population x)
    (representative_view N Finset.univ a)
  simp only [selectedView,selectedLocation,Finset.mem_univ,if_true] at h
  exact Option.some.inj (h.trans (ha x))

noncomputable def selectedCompletion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (a : SelectedIndex N sample Finset.univ) :
    PMF (SelectedIndex N sample Finset.univ) :=
  (completionKernel N r (representative N Finset.univ a)).map (projection N Finset.univ)

/-- Representative independence follows from the actual finite-time projection
and actual completion limits, with root support verified on both Codes. -/
theorem actual_source_completion_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (completionKernel N r s).map (projection N Finset.univ) =
      selectedCompletion N r (projection N Finset.univ s) := by
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hl := finite_pmf_observer_limit (fun t => sourceTimeKernel N r t s)
    (completionKernel N r s) (projection N Finset.univ)
    (fun d => actual_ancestral_kernel_tendsto_completion N r s d hs) b
  have hr := finite_pmf_observer_limit
    (fun t => sourceTimeKernel N r t (representative N Finset.univ (projection N Finset.univ s)))
    (completionKernel N r (representative N Finset.univ (projection N Finset.univ s)))
    (projection N Finset.univ)
    (fun d => actual_ancestral_kernel_tendsto_completion N r _ d
      (representative_ancestral N _ (actual_root_projection N s hs))) b
  simp_rw [constructed_source_time_kernel_projection,projection_representative] at hl hr
  exact tendsto_nhds_unique hl hr

noncomputable def completionRational (N : RootedBinary V E X) {sample : Copy → X}
    (a b : SelectedIndex N sample Finset.univ) : ℚ :=
  ∑ d : Code N sample, (ancestralPolynomial N (representative N Finset.univ a) d).coeff 0 *
    (if projection N Finset.univ d = b then 1 else 0)

theorem actual_selected_completion_rational (N : RootedBinary V E X) {sample : Copy → X}
    (a b : SelectedIndex N sample Finset.univ) (ha : FullRoot N a) (r : PositivePairRates E) :
    (completionRational N a b : ℝ) = (selectedCompletion N r a b).toReal := by
  rw [selectedCompletion,map_probability_real]
  simp only [completionRational,Rat.cast_sum,Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [actual_completion_rational N _ d (representative_ancestral N a ha) r]
  by_cases h : projection N Finset.univ d = b <;> simp [h]

/-- Actual source law composition needs only its actual ancestral support;
no equality of raw Code and the finite selected carrier is asserted. -/
theorem actual_root_law_completion_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (law : PMF (Code N sample))
    (hroot : ∀ s ∈ law.support, AncestralRoot N s) :
    (law.bind (completionKernel N r)).map (projection N Finset.univ) =
      (law.map (projection N Finset.univ)).bind (selectedCompletion N r) := by
  rw [PMF.map_bind,PMF.bind_map]
  apply bind_congr_on_support
  intro s hs
  exact actual_source_completion_projection N r s (hroot s hs)

lemma projected_root_support (N : RootedBinary V E X) {sample : Copy → X}
    (law : PMF (Code N sample)) (hroot : ∀ s ∈ law.support, AncestralRoot N s)
    {a : SelectedIndex N sample Finset.univ}
    (ha : a ∈ (law.map (projection N Finset.univ)).support) : FullRoot N a := by
  obtain ⟨s,hs,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  exact actual_root_projection N s (hroot s hs)

end GProgram.G7.SelectedCompletionPolynomial
