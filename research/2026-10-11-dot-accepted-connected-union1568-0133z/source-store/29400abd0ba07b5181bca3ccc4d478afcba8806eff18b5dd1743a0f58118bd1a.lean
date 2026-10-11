import G7SourceStepRelabelling
import UnifiedLean.Source.SourceProgramTransport

/-!
Relabelling of the constructed actual finite-time and finite-program source
law. Contributor: dot, 2026-10-09. A supplied original operation word is mapped
operation by operation. Equality of separately generated tied-calendar agendas
is not assumed or asserted here.
-/
namespace GProgram.G7.ProgramRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open GProgram.G7.OriginalRelabelling GProgram.G7.SnapshotRelabelling
open GProgram.G7.BoundaryRelabelling GProgram.G7.SourceStepRelabelling
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open scoped Classical NNReal
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

theorem iteration (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (k : Nat) (s : Code N sample) :
    (sourceIteration N r k s).map (code N v e) =
      sourceIteration (network N v e) (rates e r) k (code N v e s) := by
  induction k generalizing s with
  | zero => simp only [sourceIteration,PMF.pure_map]
  | succ k ih =>
    rw [sourceIteration,PMF.map_bind]
    simp_rw [ih]
    change (sourceStep N r s).bind
      (sourceIteration (network N v e) (rates e r) k ∘ code N v e) = _
    rw [← PMF.bind_map,source_step]
    rfl

@[simp] theorem global_clock (e : E ≃ F) (r : PositivePairRates E) :
    globalClockRate (Copy:=Copy) (rates e r) = globalClockRate (Copy:=Copy) r := by
  apply Subtype.ext
  exact global_rate e r

theorem time_kernel (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (code N v e) =
      sourceTimeKernel (network N v e) (rates e r) t (code N v e s) := by
  rw [sourceTimeKernel,sourceTimeKernel,PMF.map_bind,global_clock]
  simp_rw [iteration]

noncomputable def programStep (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) :
    ProgramStep N → ProgramStep (network N v e)
  | .interval t => .interval t
  | .boundary b => .boundary (operation N v e b)

theorem program_step (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    (sourceProgramStep N r op s).map (code N v e) =
      sourceProgramStep (network N v e) (rates e r) (programStep N v e op) (code N v e s) := by
  cases op with
  | interval t => exact time_kernel N v e r t s
  | boundary b => exact boundary_kernel N v e s b

/-- Whole endpoint-state law for every finite actual source word, with the
same COMMON register and original parameters throughout all operations. -/
theorem program (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r ops s).map (code N v e) =
      sourceProgram (network N v e) (rates e r) (ops.map (programStep N v e)) (code N v e s) := by
  induction ops generalizing s with
  | nil => simp only [List.map_nil,sourceProgram,PMF.pure_map]
  | cons op ops ih =>
    rw [sourceProgram,PMF.map_bind]
    simp_rw [ih]
    change (sourceProgramStep N r op s).bind
      (sourceProgram (network N v e) (rates e r) (ops.map (programStep N v e)) ∘ code N v e) = _
    rw [← PMF.bind_map,program_step]
    rfl

#print axioms iteration
#print axioms time_kernel
#print axioms program
end GProgram.G7.ProgramRelabelling
