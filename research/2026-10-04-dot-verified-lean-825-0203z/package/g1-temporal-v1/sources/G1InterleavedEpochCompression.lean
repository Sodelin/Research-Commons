import G1ExteriorBoundarySilence

/-!
# Recompose an original inside epoch while exterior operations still run

Contributor: dot, 2026-10-03. The full source program remains the ACTUAL
interleaved program. Only its inside readout is compressed. Physical boundary
absence and original date partitions are the input hypotheses, not a supplied
kernel identity. Actual exterior history remains governed by the joint lane.
-/
namespace G1InterleavedEpochCompression
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceEpochSemigroup
open UnifiedLean.Source.SourceProgramTransport
open G1ActualJointProgram G1OriginalEpochRecomposition G1ExteriorBoundarySilence
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def originalIntervalDurations (N : RootedBinary V E X) : List (ProgramStep N) → List ℝ≥0
  | [] => []
  | .interval t :: ops => t :: originalIntervalDurations N ops
  | .boundary _ :: ops => originalIntervalDurations N ops

noncomputable def SilentExteriorAgenda (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) : List (ProgramStep N) → Code N sample → Prop
  | [], _ => True
  | .interval t :: ops, s => ∀ d ∈ (sourceTimeKernel N r t s).support,
      SilentExteriorAgenda N r keep ops d
  | .boundary b :: ops, s => PanelAbsent N b (state s) keep ∧
      ∀ d ∈ (boundaryKernel N b s).support, SilentExteriorAgenda N r keep ops d

/-- The ACTUAL larger-source interleaved inside-view law equals one original
epoch at its original rates and summed original subinterval duration. -/
theorem actual_interleaved_epoch_readout (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample)
    (hsilent : SilentExteriorAgenda N r keep ops s) :
    (sourceProgram N r ops s).map (projection N keep) =
      (sourceTimeKernel N r (originalIntervalDurations N ops).sum s).map (projection N keep) := by
  induction ops generalizing s with
  | nil => simp [sourceProgram,originalIntervalDurations,actual_source_time_zero]
  | cons op ops ih =>
      cases op with
      | interval t =>
          simp only [sourceProgram,sourceProgramStep,PMF.map_bind,originalIntervalDurations,List.sum_cons]
          calc
            _ = (sourceTimeKernel N r t s).bind (fun d =>
                (sourceTimeKernel N r (originalIntervalDurations N ops).sum d).map (projection N keep)) :=
              bind_eq_of_eq_on_support _ _ _ (fun d hd => ih d (hsilent d hd))
            _ = _ := by rw [← PMF.map_bind,← actual_source_time_add]
      | boundary b =>
          obtain ⟨habsent,htail⟩ := hsilent
          simp only [sourceProgram,sourceProgramStep,PMF.map_bind,originalIntervalDurations]
          calc
            _ = (boundaryKernel N b s).bind (fun d =>
                (sourceTimeKernel N r (originalIntervalDurations N ops).sum d).map (projection N keep)) :=
              bind_eq_of_eq_on_support _ _ _ (fun d hd => ih d (htail d hd))
            _ = (boundaryKernel N b s).bind (fun _ =>
                (sourceTimeKernel N r (originalIntervalDurations N ops).sum s).map (projection N keep)) := by
              apply bind_eq_of_eq_on_support
              intro d hd
              rw [constructed_source_time_kernel_projection,constructed_source_time_kernel_projection,
                actual_untouched_boundary_panel N b s keep habsent hd]
            _ = _ := PMF.bind_const _ _

/-- Exterior-only original boundaries can occur at ANY ordered original
break dates, with no fitted rate and no lost inside genealogy/register state. -/
theorem actual_interleaved_original_date_partition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample)
    (hsilent : SilentExteriorAgenda N r keep ops s) {a b : ℝ}
    (partition : OriginalDurationPartition a b (originalIntervalDurations N ops)) :
    (sourceProgram N r ops s).map (projection N keep) =
      (sourceTimeKernel N r (Real.toNNReal (b-a)) s).map (projection N keep) := by
  rw [actual_interleaved_epoch_readout N r keep ops s hsilent,
    actual_original_partition_duration_sum partition]

#print axioms actual_interleaved_epoch_readout
#print axioms actual_interleaved_original_date_partition
end G1InterleavedEpochCompression
