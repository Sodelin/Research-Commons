import UnifiedLean.Source.SourceBoundaryProjection
import UnifiedLean.Source.SourcePoissonKernel

/-!
# Coherent original epoch + node program probability transport

Contributor: dot, 2026-10-02. Composes the CONSTRUCTED actual source interval
and node kernels, including current-owner independent and same-register COMMON
pulses, as genuine normalized PMFs. The entire pruned-state output law is proved
for every finite operation program, hence any later physically compiled calendar
program. No per-step intertwining or desired whole-law field is a source input.
The actual calendar compiler, physical holding-clock path identification,
separate smaller-copy carrier and final passive/unranked observation admission
remain the original source assembly obligations.
-/
namespace UnifiedLean.Source.SourceProgramTransport
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

inductive ProgramStep (N : RootedBinary V E X)
  | interval (duration : ℝ≥0)
  | boundary (operation : BoundaryOperation N)

noncomputable def sourceProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) : PMF (Code N sample) :=
  match op with
  | .interval t => sourceTimeKernel N r t s
  | .boundary b => boundaryKernel N b s

noncomputable def selectedProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (v : SelectedIndex N sample keep) : PMF (SelectedIndex N sample keep) :=
  match op with
  | .interval t => selectedTimeKernel N r keep t v
  | .boundary b => selectedBoundary N keep b v

/-- Both step kinds bind to actual original source operations with DERIVED
whole selected-state laws. -/
theorem actual_program_step_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N) (s : Code N sample) :
    (sourceProgramStep N r op s).map (projection N keep) =
      selectedProgramStep N r keep op (projection N keep s) := by
  cases op with
  | interval t => exact constructed_source_time_kernel_projection N r keep t s
  | boundary b => exact actual_boundary_projection N keep b s

noncomputable def sourceProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N) → Code N sample → PMF (Code N sample)
  | [],s => PMF.pure s
  | op :: ops,s => (sourceProgramStep N r op s).bind (sourceProgram N r ops)

noncomputable def selectedProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    List (ProgramStep N) → SelectedIndex N sample keep → PMF (SelectedIndex N sample keep)
  | [],v => PMF.pure v
  | op :: ops,v => (selectedProgramStep N r keep op v).bind (selectedProgram N r keep ops)

/-- End-to-end PMF transport of the actual finite original operation program.
Independent routing uses CURRENT roots; COMMON retains the SAME original
register across the entire program. -/
theorem actual_source_program_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) :
    (sourceProgram N r ops s).map (projection N keep) =
      selectedProgram N r keep ops (projection N keep s) := by
  induction ops generalizing s with
  | nil => simp only [sourceProgram,selectedProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [sourceProgram,PMF.map_bind]
      simp_rw [ih]
      change (sourceProgramStep N r op s).bind
        (selectedProgram N r keep ops ∘ projection N keep) = _
      rw [← PMF.bind_map,actual_program_step_projection]
      rfl

/-- Any actually selected-state-dependent endpoint readout preserves its whole
probability law. Physical/biological readout and unranked quotient binding are
not smuggled into this statement as an observed-law equality assumption. -/
theorem actual_program_endpoint_law {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (readout : SelectedIndex N sample keep → Obs) :
    (sourceProgram N r ops s).map (readout ∘ projection N keep) =
      (selectedProgram N r keep ops (projection N keep s)).map readout := by
  rw [← PMF.map_comp,actual_source_program_projection]

#print axioms actual_program_step_projection
#print axioms actual_source_program_projection
#print axioms actual_program_endpoint_law
end UnifiedLean.Source.SourceProgramTransport
