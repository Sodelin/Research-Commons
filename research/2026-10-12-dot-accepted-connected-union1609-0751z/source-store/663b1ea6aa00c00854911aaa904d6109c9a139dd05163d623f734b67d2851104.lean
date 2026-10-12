import G1ActualJointStageHistory
import UnifiedLean.Source.SourceEpochSemigroup

/-!
# Actual original population epoch recomposition at unrelated dates

Contributor: dot, 2026-10-03. All durations and kernels are from the SAME
original source and rates. No synthetic scalar demographic rate is fitted.
This is the temporal algebra needed after actual exterior-boundary silence.
-/
namespace G1OriginalEpochRecomposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceEpochSemigroup
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual source epochs compose at their original population rate, with no
regard to the number of exterior vertex dates used to subdivide the interval. -/
theorem actual_original_epoch_list_recomposition (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (durations : List ℝ≥0) (s : Code N sample) :
    sourceProgram N r (durations.map ProgramStep.interval) s =
      sourceTimeKernel N r durations.sum s := by
  induction durations generalizing s with
  | nil => simp only [List.map_nil,List.sum_nil,sourceProgram,actual_source_time_zero]
  | cons t ts ih =>
      simp only [List.map_cons,List.sum_cons,sourceProgram,sourceProgramStep]
      rw [actual_source_time_add]
      congr 1
      funext d
      exact ih d

lemma actual_split_duration_sum {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    Real.toNNReal (c-a) + Real.toNNReal (b-c) = Real.toNNReal (b-a) := by
  rw [← Real.toNNReal_add (sub_nonneg.mpr hac) (sub_nonneg.mpr hcb)]
  congr 1
  ring

/-- An ordered split of an ORIGINAL interval. The data consist solely of
actual break dates and durations, never a stochastic identity. -/
inductive OriginalDurationPartition : ℝ → ℝ → List ℝ≥0 → Prop
  | whole {a b : ℝ} (hab : a ≤ b) : OriginalDurationPartition a b [Real.toNNReal (b-a)]
  | split {a b : ℝ} (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) {rest : List ℝ≥0}
      (tail : OriginalDurationPartition c b rest) :
      OriginalDurationPartition a b (Real.toNNReal (c-a) :: rest)

theorem actual_original_partition_duration_sum {a b : ℝ} {durations : List ℝ≥0}
    (h : OriginalDurationPartition a b durations) : durations.sum = Real.toNNReal (b-a) := by
  induction h with
  | whole hab => simp
  | split c hac hcb tail ih => rw [List.sum_cons,ih,actual_split_duration_sum hac hcb]

theorem actual_original_partition_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) {a b : ℝ} {durations : List ℝ≥0}
    (partition : OriginalDurationPartition a b durations) (s : Code N sample) :
    sourceProgram N r (durations.map ProgramStep.interval) s =
      sourceTimeKernel N r (Real.toNNReal (b-a)) s := by
  rw [actual_original_epoch_list_recomposition,actual_original_partition_duration_sum partition]

#print axioms actual_original_epoch_list_recomposition
#print axioms actual_original_partition_kernel
end G1OriginalEpochRecomposition
