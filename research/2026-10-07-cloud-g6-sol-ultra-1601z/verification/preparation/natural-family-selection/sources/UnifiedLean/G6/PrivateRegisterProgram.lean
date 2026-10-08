import UnifiedLean.G6.PrivateRegisterSourceStep
import UnifiedLean.G6.PrivateRegisterBoundary
import UnifiedLean.Source.SourceProgramTransport

/-!
UNCHECKED SAME-graph original operation-word erasure consumer. Iteration and
Poisson mixing reuse the SAME physical rate bank; boundaries use actual current
owners and the original COMMON bit only at sites outside the erased set.
No desired kernel/program/readout law is a premise. A legal physical no-read
calendar constructor and full marked/bin/cross-graph history remain separate.
Outside frozen16501e3676. CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026.
-/
namespace UnifiedLean.G6.PrivateRegisterProgram
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterErasure
open UnifiedLean.G6.PrivateRegisterSourceStep
open UnifiedLean.G6.PrivateRegisterBoundary
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_sourceIteration_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V) (k : Nat)
    (s : Code N sample) :
    (sourceIteration N r k s).map (erasePrivateCode N P) =
      sourceIteration N r k (erasePrivateCode N P s) := by
  induction k generalizing s with
  | zero => simp only [sourceIteration, PMF.pure_map]
  | succ k ih =>
      rw [sourceIteration, PMF.map_bind]
      simp_rw [ih]
      change (sourceStep N r s).bind
        (sourceIteration N r k ∘ erasePrivateCode N P) = _
      rw [← PMF.bind_map, actual_sourceStep_erasure]
      rfl

theorem actual_sourceTimeKernel_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V) (t : ℝ≥0)
    (s : Code N sample) :
    (sourceTimeKernel N r t s).map (erasePrivateCode N P) =
      sourceTimeKernel N r t (erasePrivateCode N P s) := by
  simp only [sourceTimeKernel, PMF.map_bind, actual_sourceIteration_erasure]

def NoPrivateStepRead (N : RootedBinary V E X) (P : Finset V) :
    ProgramStep N → Prop
  | .interval _ => True
  | .boundary op => NoPrivateRead N P op

def NoPrivateWordRead (N : RootedBinary V E X) (P : Finset V)
    (ops : List (ProgramStep N)) : Prop :=
  ∀ op ∈ ops, NoPrivateStepRead N P op

theorem actual_sourceProgramStep_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (op : ProgramStep N) (s : Code N sample) (hop : NoPrivateStepRead N P op) :
    (sourceProgramStep N r op s).map (erasePrivateCode N P) =
      sourceProgramStep N r op (erasePrivateCode N P s) := by
  cases op with
  | interval t => exact actual_sourceTimeKernel_erasure N r P t s
  | boundary b => exact actual_boundary_erasure N P b s hop

/-- Whole actual endpoint law under an explicit source-operation no-read
property. The property has no probability-law equality in its definition. -/
theorem actual_sourceProgram_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (ops : List (ProgramStep N)) :
    NoPrivateWordRead N P ops → ∀ s : Code N sample,
    (sourceProgram N r ops s).map (erasePrivateCode N P) =
      sourceProgram N r ops (erasePrivateCode N P s) := by
  induction ops with
  | nil =>
      intro _ s
      simp only [sourceProgram, PMF.pure_map]
  | cons op ops ih =>
      intro hops s
      have hhead : NoPrivateStepRead N P op := hops op List.mem_cons_self
      have htail : NoPrivateWordRead N P ops := by
        intro b hb
        exact hops b (List.mem_cons_of_mem op hb)
      rw [sourceProgram, PMF.map_bind]
      simp_rw [ih htail]
      change (sourceProgramStep N r op s).bind
        (sourceProgram N r ops ∘ erasePrivateCode N P) = _
      rw [← PMF.bind_map, actual_sourceProgramStep_erasure N r P op s hhead]
      rfl

/-- One joint readout of the erased finite Code, with no per-coordinate factor.
Physical bin/menu admission is not implied by choosing an arbitrary readout. -/
theorem actual_erased_program_endpoint_law {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (P : Finset V) (ops : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops)
    (s : Code N sample) (readout : Code N sample → Obs) :
    (sourceProgram N r ops s).map (readout ∘ erasePrivateCode N P) =
      (sourceProgram N r ops (erasePrivateCode N P s)).map readout := by
  rw [← PMF.map_comp, actual_sourceProgram_erasure N r P ops hops s]

#print axioms actual_sourceIteration_erasure
#print axioms actual_sourceTimeKernel_erasure
#print axioms actual_sourceProgramStep_erasure
#print axioms actual_sourceProgram_erasure
#print axioms actual_erased_program_endpoint_law

end UnifiedLean.G6.PrivateRegisterProgram
