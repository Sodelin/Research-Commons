import ActualStoredRegister
import G1NonrootBigonKernel

/-! Direct use of the already compiled original nonroot-bigon source program.
Its arm duration comes from the actual calendar and both original exits are
executed. This consumer does not identify an arbitrary full-calendar segment
with the isolated four-operation fragment. dot (OpenAI), 9 October 2026. -/
namespace DotG34.OriginalBigonProgramDiagonal
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open G1NonrootBigonKernel DotG34.ActualBigonBinomial
open DotG34.ActualCommonBigonSurvival
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Deterministic rejoining exits preserve the complete live-root count law. -/
theorem actual_bigon_count_law (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (common : Bool) (s : Code N sample) :
    (sourceProgram N r (bigonProgram N C B gamma common) s).map liveCard =
      (sourceProgram N r [.boundary (bigonPulse N B gamma common),
        .interval (bigonDuration N C B)] s).map liveCard := by
  rw [actual_bigon_program_kernel, PMF.map_bind]
  simp only [sourceProgram, sourceProgramStep, PMF.bind_pure, PMF.map_bind]
  congr 1
  funext q
  rw [PMF.map_comp]
  rfl

/-- Exact original-source INDEPENDENT diagonal, including the real exit pair.
No arm clock or diagonal formula is an input field of NonrootBigon. -/
theorem actual_original_bigon_independent (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid) :
    let n := Fintype.card (AtNode (state s) B.parents.hybrid)
    (((sourceProgram N r (bigonProgram N C B gamma false) s).map liveCard)
      (liveCard s)).toReal =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*(1-(gamma:ℝ))^k*(gamma:ℝ)^(n-k)*
        (Real.exp (-(pairRate r (some B.parents.parent0)*(bigonDuration N C B:ℝ))))^(k.choose 2)*
        (Real.exp (-(pairRate r (some B.parents.parent1)*(bigonDuration N C B:ℝ))))^((n-k).choose 2) := by
  rw [actual_bigon_count_law]
  exact actual_bigon_binomial N r B.parents gamma (bigonDuration N C B) s hall

/-- Exact original-source COMMON diagonal keeps the entering original bit. -/
theorem actual_original_bigon_common (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid) :
    let n := Fintype.card (AtNode (state s) B.parents.hybrid)
    (((sourceProgram N r (bigonProgram N C B gamma true) s).map liveCard)
      (liveCard s)).toReal =
    if (state s).register B.parents.hybrid then
      (Real.exp (-(pairRate r (some B.parents.parent1)*(bigonDuration N C B:ℝ))))^(n.choose 2)
    else (Real.exp (-(pairRate r (some B.parents.parent0)*(bigonDuration N C B:ℝ))))^(n.choose 2) := by
  rw [actual_bigon_count_law]
  exact actual_common_bigon_survival N r B.parents (bigonDuration N C B) s hall

#print axioms actual_bigon_count_law
#print axioms actual_original_bigon_independent
#print axioms actual_original_bigon_common
end DotG34.OriginalBigonProgramDiagonal
