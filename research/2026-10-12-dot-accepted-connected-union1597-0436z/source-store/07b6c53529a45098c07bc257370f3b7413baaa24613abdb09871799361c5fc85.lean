import G4ActualCommonSelectorSupport
import ActualSerialSurvival

/-!
# The actual COMMON-only no-loss event has one original boundary route

Uncompiled source-only composition proposal, 11 October 2026.
Reuses ActualSerialSurvival (02c033b1): its weightedRoute is already the actual
no-loss restriction of sourceProgram, with the proved original holding weights.
No new generator, route recurrence, probability kernel, or observation is defined.
This specializes the existing whole-word mass expansion to the source's
deterministic stored-bit COMMON boundaries. It adds no no-merger conditioning
to the source law: the left side is the unconditional no-loss event probability.

Identifying this exact weight with an exclusive selected-path exposure at a
bank's own meeting is a further temporal/route composition. The completed
crossed-cherry and four-copy comb topology probabilities are also further work.
-/

namespace GProgram.G4.ActualCommonNoLossRoute
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G5.SafePrefixRouteBridge GProgram.G4.ActualCommonSelectorSupport
open DotG34.ActualSerialSurvival
open scoped Classical NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_common_boundary_kernel (N : RootedBinary V E X)
    {sample : Copy → X} (b : BoundaryOperation N)
    (hb : CommonOnlyBoundary N b) (s : Code N sample) :
    boundaryKernel N b s = PMF.pure (fixedRegisterBoundary N b s) := by
  cases b with
  | exit e => rfl
  | ordinary e degree => rfl
  | root => rfl
  | common H => rfl
  | independent H gamma => exact False.elim hb

/-- Every nonzero no-loss route ends at the original deterministic COMMON
prefix's Code. The supported law itself may also contain all merger endpoints. -/
theorem actual_common_weighted_route_other_zero (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hcommon : CommonOnlyWord N ops) (s d : Code N sample)
    (hd : d ≠ fixedRegisterPrefix N ops s) :
    weightedRoute N r ops s d = 0 := by
  induction ops generalizing s with
  | nil =>
      have hds : d ≠ s := hd
      simp [weightedRoute, PMF.pure_apply, hds, Ne.symm hds]
  | cons op ops ih =>
      cases op with
      | interval t =>
          change sourceTimeKernel N r t s s * weightedRoute N r ops s d = 0
          rw [ih hcommon s hd, mul_zero]
      | boundary b =>
          change (∑' m : Code N sample,
            boundaryKernel N b s m * weightedRoute N r ops m d) = 0
          rw [actual_common_boundary_kernel N b hcommon.1 s]
          have hpure : (∑' m : Code N sample,
              PMF.pure (fixedRegisterBoundary N b s) m * weightedRoute N r ops m d) =
              weightedRoute N r ops (fixedRegisterBoundary N b s) d := by
            simp [PMF.pure_apply]
          rw [hpure]
          exact ih hcommon.2 (fixedRegisterBoundary N b s) hd

/-- Exact original whole-program no-loss probability, with no hq/row-constant
premise. All holding factors are those already proved for the actual source.
The bank stays inside the entering Code and is never redrawn by this theorem. -/
theorem actual_common_word_no_loss_mass (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hcommon : CommonOnlyWord N ops) (s : Code N sample) :
    ((sourceProgram N r ops s).map liveCard) (liveCard s) =
      weightedRoute N r ops s (fixedRegisterPrefix N ops s) := by
  rw [actual_no_loss_event]
  apply tsum_eq_single (fixedRegisterPrefix N ops s)
  intro d hd
  exact actual_common_weighted_route_other_zero N r ops hcommon s d hd

end GProgram.G4.ActualCommonNoLossRoute
