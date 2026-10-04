import G1UnrankedActualFuture
import UnifiedLean.Source.SourceNaturalCompletedLimit

/-!
# Actual unbounded ancestral completion descends to the unranked interface

Contributor: dot, 2026-10-03. The finite original-future interface is extended
using the inherited ACTUAL ancestral kernel limit. No desired terminal row or
new completion law is assumed. Natural calendar/root support remains physical.
-/
namespace G1ActualUnrankedAncestralCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Filter
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceEventualCompletionLimit
open UnifiedLean.Source.SourceNaturalCompletedLimit
open G1UnrankedSourceView G1UnrankedActualFuture
open scoped Classical Topology NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_nonempty_unranked_completion_row {Obs : Type*} [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (keep : Finset Copy) (s z : Code N sample)
    (hs : AncestralRoot N s) (hz : AncestralRoot N z)
    (hview : unrankedView (selectedView (state s) keep) =
      unrankedView (selectedView (state z) keep)) (readout : UnrankedView V E Copy → Obs) :
    (completionKernel N r s).map (fun d => readout (unrankedView (selectedView (state d) keep))) =
      (completionKernel N r z).map (fun d => readout (unrankedView (selectedView (state d) keep))) := by
  let obs := fun d : Code N sample => readout (unrankedView (selectedView (state d) keep))
  have he (t : ℝ≥0) : (sourceTimeKernel N r t s).map obs = (sourceTimeKernel N r t z).map obs := by
    have h := actual_unranked_future_row_independent N r keep [.interval t] s z hview readout
    simpa [sourceProgram,sourceProgramStep,obs] using h
  apply PMF.ext
  intro q
  have hS := finite_pmf_observer_limit (fun t => sourceTimeKernel N r t s)
    (completionKernel N r s) obs (fun d => actual_ancestral_kernel_tendsto_completion N r s d hs) q
  have hZ := finite_pmf_observer_limit (fun t => sourceTimeKernel N r t z)
    (completionKernel N r z) obs (fun d => actual_ancestral_kernel_tendsto_completion N r z d hz) q
  have hZ' : Tendsto (fun t : ℝ≥0 => ((sourceTimeKernel N r t s).map obs q).toReal) atTop
      (𝓝 ((completionKernel N r z).map obs q).toReal) := by
    convert hZ using 1
    funext t
    exact congrArg (fun p : PMF Obs => (p q).toReal) (he t)
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    (tendsto_nhds_unique hS hZ')

/-- Empty-copy sources are included explicitly; the completion has zero
winner jumps and the SAME register/unranked interface determines the row. -/
theorem actual_unranked_completion_row {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (keep : Finset Copy) (s z : Code N sample)
    (hs : AncestralRoot N s) (hz : AncestralRoot N z)
    (hview : unrankedView (selectedView (state s) keep) =
      unrankedView (selectedView (state z) keep)) (readout : UnrankedView V E Copy → Obs) :
    (completionKernel N r s).map (fun d => readout (unrankedView (selectedView (state d) keep))) =
      (completionKernel N r z).map (fun d => readout (unrankedView (selectedView (state d) keep))) := by
  by_cases hn : Nonempty Copy
  · letI := hn
    exact actual_nonempty_unranked_completion_row N r keep s z hs hz hview readout
  · letI : IsEmpty Copy := ⟨fun x => hn ⟨x⟩⟩
    simpa [completionKernel,ancestralCompletion,PMF.pure_map] using congrArg (fun v => PMF.pure (readout v)) hview

#print axioms actual_unranked_completion_row
end G1ActualUnrankedAncestralCompletion
