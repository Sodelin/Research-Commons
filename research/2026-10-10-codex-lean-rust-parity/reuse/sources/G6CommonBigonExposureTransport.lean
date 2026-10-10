import G1NonrootBigonKernel
import G7SinglePopulationPolynomialKernel

/-!
# Actual COMMON-bigon exposure transport on the original retained state

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
This is a source-specific consumer of the full single-population polynomial,
not a survival-count formula. One original stored bit chooses one original
parent-edge occurrence. Equal physical exposure on that selected arm preserves
the entire original Code law, and hence any full forest/register/past context.
No independence between the entering state and its original register is used.

This does not identify the two arms with a common abstract forest generator,
derive a Bernoulli mixture after private-seed erasure, or construct bounded
positive chains. Calendar retiming here preserves the fragment endpoint law;
absolute merger-age or internal cut observations require their own bridge.
-/
namespace UnifiedLean.G6.CommonBigonExposureTransport

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open G1NonrootBigonKernel
open GProgram.G7.SinglePopulationPolynomialKernel
open G1OpaqueSourceGrafting G1OriginalCurrentRootReconstruction
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The exact original pulse routes every current live owner onto the selected
original parent occurrence; previously formed input genealogies stay carried. -/
theorem actual_constant_pulse_coLocated (N : RootedBinary V E X)
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N)
    (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    (b : Bool) :
    CoLocated N (pulseCode H s (fun _ => b)) (some (H.parent b)) := by
  intro x
  have hx : (state s).ancestor x ∈ (state s).live ∧
      (state s).location ((state s).ancestor x) = .node H.hybrid :=
    ⟨s.property.forest.ancestor_live x,
      hinput _ (s.property.forest.ancestor_live x)⟩
  rw [show copyLocation (state (pulseCode H s (fun _ => b))) x =
      copyLocation (pulse H (state s) (fun _ => b)) x from
    decode_encode_copyLocation N.root _
      (pulse_source_valid H sample _ s.property (fun _ => b)).forest x]
  exact pulse_routes_current_ancestor H (state s) (fun _ => b)
    ⟨(state s).ancestor x, hx⟩

/-- The entire retained-state epoch law depends on the physical product rho*t.
All other original edge/ancestral rates can change at the same time. -/
theorem actual_population_exposure_transport (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E)
    (hs : CoLocated N s i) (r rhat : PositivePairRates E) (t that : ℝ≥0)
    (hexposure : pairRate r i * (t : ℝ) = pairRate rhat i * (that : ℝ)) :
    sourceTimeKernel N r t s = sourceTimeKernel N rhat that s := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [← actual_population_polynomial N s d i hs r t,
    ← actual_population_polynomial N s d i hs rhat that]
  have hz : Real.exp (-(pairRate r i) * (t : ℝ)) =
      Real.exp (-(pairRate rhat i) * (that : ℝ)) := by
    simp only [neg_mul]
    rw [hexposure]
  rw [hz]

/-- Both complete positive original calendar/rate banks have the same COMMON
fragment law if the actually stored original bit selects equal arm exposure.
No marginal-mixture or entering-independence hypothesis is introduced. -/
theorem actual_common_bigon_exposure_transport (N : RootedBinary V E X)
    {sample : Copy → X} (C Chat : Calendar N.graph) (r rhat : PositivePairRates E)
    (B : NonrootBigon N) (gamma gammahat : unitInterval) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live,
      (state s).location l = .node B.parents.hybrid)
    (hexposure :
      pairRate r (some (B.parents.parent ((state s).register B.parents.hybrid))) *
          (bigonDuration N C B : ℝ) =
        pairRate rhat (some (B.parents.parent ((state s).register B.parents.hybrid))) *
          (bigonDuration N Chat B : ℝ)) :
    sourceProgram N r (bigonProgram N C B gamma true) s =
      sourceProgram N rhat (bigonProgram N Chat B gammahat true) s := by
  rw [actual_bigon_program_kernel, actual_bigon_program_kernel]
  simp only [bigonPulse, ite_true, boundaryKernel, PMF.pure_bind]
  have he := actual_population_exposure_transport N
    (pulseCode B.parents s (fun _ => (state s).register B.parents.hybrid))
    (some (B.parents.parent ((state s).register B.parents.hybrid)))
    (actual_constant_pulse_coLocated N B.parents s hinput _)
    r rhat (bigonDuration N C B) (bigonDuration N Chat B) hexposure
  rw [he]

/-- Arbitrary earlier joint history is retained. Exterior use may read the
whole old forest and the same original register. The equality is proved on the
actual entering support, without replacing its correlated law by a product. -/
theorem actual_common_bigon_joint_context_transport (N : RootedBinary V E X)
    {sample : Copy → X} {History Obs : Type*}
    (C Chat : Calendar N.graph) (r rhat : PositivePairRates E)
    (B : NonrootBigon N) (gamma gammahat : unitInterval)
    (prior : PMF (Code N sample × History))
    (hinput : ∀ a ∈ prior.support, ∀ l ∈ (state a.1).live,
      (state a.1).location l = .node B.parents.hybrid)
    (hexposure : ∀ a ∈ prior.support,
      pairRate r (some (B.parents.parent ((state a.1).register B.parents.hybrid))) *
          (bigonDuration N C B : ℝ) =
        pairRate rhat (some (B.parents.parent ((state a.1).register B.parents.hybrid))) *
          (bigonDuration N Chat B : ℝ))
    (exterior : History × (V → Bool) × Finset
      (UnifiedLean.Source.UnrankedGenealogyObservation.UnrankedTree Copy) → PMF Obs) :
    prior.bind (fun a =>
      (sourceProgram N r (bigonProgram N C B gamma true) a.1).bind
        (fun d => exterior (a.2, (state d).register, rootForest N d))) =
      prior.bind (fun a =>
        (sourceProgram N rhat (bigonProgram N Chat B gammahat true) a.1).bind
          (fun d => exterior (a.2, (state d).register, rootForest N d))) := by
  apply PMF.ext
  intro obs
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ prior.support
  · rw [actual_common_bigon_exposure_transport N C Chat r rhat B gamma gammahat
      a.1 (hinput a ha) (hexposure a ha)]
  · have hz : prior a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp [hz]

#print axioms actual_constant_pulse_coLocated
#print axioms actual_population_exposure_transport
#print axioms actual_common_bigon_exposure_transport
#print axioms actual_common_bigon_joint_context_transport

end UnifiedLean.G6.CommonBigonExposureTransport
