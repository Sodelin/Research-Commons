import UnifiedLean.Source.SourceProgramTransport
import UnifiedLean.Source.SourceAncestralCompletion
import G2SourceFiniteHistory

/-!
UNCOMPILED source candidate, existing G3 owner,22October2026.
Compare ACTUAL source kernels on two valid sample charts with the SAME raw
Snapshot. Keep the original graph/rates/clock/operators/register unchanged.
The proof couples the literal identical choices, not the dependent Code types.
It does not equate arbitrary natural tip initializers or assert a target M.
-/
namespace G3OriginalSampleParametricity
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceEmbeddedJumpLaw UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.SourceFiniteHistory
open scoped Classical NNReal

variable {V E Copy X Obs : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Identical raw inputs have the SAME current ordered pair catalogue and
choice PMF. Every paired destination has identical raw fields; only the
SourceValid proof belongs to its own actual sample chart. -/
theorem actual_step_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (sourceStep N r sA).bind KA = (sourceStep N r sB).bind KB := by
  rcases sA with ⟨a,ha⟩
  rcases sB with ⟨b,hb⟩
  change a = b at hraw
  subst b
  simp only [sourceStep,PMF.bind_map]
  congr 1
  funext q
  apply hK
  cases q <;> rfl

theorem actual_iteration_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E) (k : Nat)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (sourceIteration N r k sA).bind KA = (sourceIteration N r k sB).bind KB := by
  induction k generalizing sA sB with
  | zero =>
      simp only [sourceIteration,PMF.pure_bind]
      exact hK sA sB hraw
  | succ k ih =>
      simp only [sourceIteration,PMF.bind_bind]
      exact actual_step_bind_same_raw N sampleA sampleB r sA sB hraw
        (fun a => (sourceIteration N r k a).bind KA)
        (fun b => (sourceIteration N r k b).bind KB)
        (fun a b hab => ih a b hab)

/-- Exactly the same Poisson count/global clock: the Copy type, original
graph, rates and time are unchanged. No new normalization or clock is input. -/
theorem actual_time_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E) (t : ℝ≥0)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (sourceTimeKernel N r t sA).bind KA = (sourceTimeKernel N r t sB).bind KB := by
  simp only [sourceTimeKernel,PMF.bind_bind]
  congr 1
  funext k
  exact actual_iteration_bind_same_raw N sampleA sampleB r k sA sB hraw KA KB hK

/-- Actual original exits/entries/current-owner pulses compare directly.
INDEPENDENT uses the same current AtNode coin domain; COMMON reads the same
original register field. No per-original-copy re-coining is introduced. -/
theorem actual_boundary_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (op : BoundaryOperation N)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (boundaryKernel N op sA).bind KA = (boundaryKernel N op sB).bind KB := by
  rcases sA with ⟨a,ha⟩
  rcases sB with ⟨b,hb⟩
  change a = b at hraw
  subst b
  cases op with
  | exit e =>
      simp only [boundaryKernel,PMF.pure_bind]
      apply hK
      rfl
  | ordinary e hd =>
      simp only [boundaryKernel,PMF.pure_bind]
      apply hK
      rfl
  | root =>
      simp only [boundaryKernel,PMF.pure_bind]
      apply hK
      rfl
  | common H =>
      simp only [boundaryKernel,PMF.pure_bind]
      apply hK
      rfl
  | independent H gamma =>
      simp only [boundaryKernel,independentPulseKernel,PMF.bind_map]
      congr 1
      funext coin
      apply hK
      rfl

theorem actual_program_step_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E) (op : ProgramStep N)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (sourceProgramStep N r op sA).bind KA = (sourceProgramStep N r op sB).bind KB := by
  cases op with
  | interval t => exact actual_time_bind_same_raw N sampleA sampleB r t sA sB hraw KA KB hK
  | boundary b => exact actual_boundary_bind_same_raw N sampleA sampleB b sA sB hraw KA KB hK

/-- Entire actual SAME original word, proved by the coupled source rows.
The continuation premise is ordinary mathematical extensionality on raw
fields, not a desired source kernel or observer-law hypothesis. -/
theorem actual_program_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E)
    (ops : List (ProgramStep N))
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (sourceProgram N r ops sA).bind KA = (sourceProgram N r ops sB).bind KB := by
  induction ops generalizing sA sB with
  | nil =>
      simp only [sourceProgram,PMF.pure_bind]
      exact hK sA sB hraw
  | cons op ops ih =>
      simp only [sourceProgram,PMF.bind_bind]
      exact actual_program_step_bind_same_raw N sampleA sampleB r op sA sB hraw
        (fun a => (sourceProgram N r ops a).bind KA)
        (fun b => (sourceProgram N r ops b).bind KB)
        (fun a b hab => ih a b hab)

theorem actual_source_program_raw_sample_transport (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E) (ops : List (ProgramStep N))
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val) :
    (sourceProgram N r ops sA).map Subtype.val =
      (sourceProgram N r ops sB).map Subtype.val := by
  change (sourceProgram N r ops sA).bind (fun a => PMF.pure a.val) =
    (sourceProgram N r ops sB).bind (fun b => PMF.pure b.val)
  exact actual_program_bind_same_raw N sampleA sampleB r ops sA sB hraw _ _
    (fun a b hab => congrArg PMF.pure hab)

#print axioms actual_step_bind_same_raw
#print axioms actual_time_bind_same_raw
#print axioms actual_boundary_bind_same_raw
#print axioms actual_program_bind_same_raw
#print axioms actual_source_program_raw_sample_transport

/-- The actual real-merger jump law compares too, including its zero-rate
absorbing branch. No dummy uniformization hold is counted as a merger. -/
theorem actual_jump_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (sourceJumpStep N r sA).bind KA = (sourceJumpStep N r sB).bind KB := by
  rcases sA with ⟨a,ha⟩
  rcases sB with ⟨b,hb⟩
  change a = b at hraw
  subst b
  simp only [sourceJumpStep,PMF.bind_map]
  congr 1
  funext q
  apply hK
  cases q <;> rfl

theorem actual_completion_bind_same_raw (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E) (k : Nat)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val)
    (KA : Code N sampleA → PMF Obs) (KB : Code N sampleB → PMF Obs)
    (hK : ∀ a b, a.val = b.val → KA a = KB b) :
    (ancestralCompletion N r k sA).bind KA =
      (ancestralCompletion N r k sB).bind KB := by
  induction k generalizing sA sB with
  | zero =>
      simp only [ancestralCompletion,PMF.pure_bind]
      exact hK sA sB hraw
  | succ k ih =>
      simp only [ancestralCompletion,PMF.bind_bind]
      exact actual_jump_bind_same_raw N sampleA sampleB r sA sB hraw
        (fun a => (ancestralCompletion N r k a).bind KA)
        (fun b => (ancestralCompletion N r k b).bind KB)
        (fun a b hab => ih a b hab)

/-- Actual finite word plus actual ancestral completion, with no independent
sample-chart or source-law premise. One common raw observer may be supplied. -/
theorem actual_completed_program_raw_sample_transport (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (k : Nat)
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val) :
    ((sourceProgram N r ops sA).bind (ancestralCompletion N r k)).map Subtype.val =
      ((sourceProgram N r ops sB).bind (ancestralCompletion N r k)).map Subtype.val := by
  change ((sourceProgram N r ops sA).bind (ancestralCompletion N r k)).bind
      (fun a => PMF.pure a.val) =
    ((sourceProgram N r ops sB).bind (ancestralCompletion N r k)).bind
      (fun b => PMF.pure b.val)
  rw [PMF.bind_bind,PMF.bind_bind]
  exact actual_program_bind_same_raw N sampleA sampleB r ops sA sB hraw _ _
    (fun a b hab => actual_completion_bind_same_raw N sampleA sampleB r k a b hab _ _
      (fun c d hcd => congrArg PMF.pure hcd))

/-- EVERY actual finite endpoint is retained, not merely the last state.
This is the existing finite-history word law, not a literal marked-clock
record or a newly authorized observation of hidden fields. -/
theorem actual_source_history_raw_sample_transport (N : RootedBinary V E X)
    (sampleA sampleB : Copy → X) (r : PositivePairRates E)
    (ops : List (ProgramStep N))
    (sA : Code N sampleA) (sB : Code N sampleB) (hraw : sA.val = sB.val) :
    (sourceHistoryLaw N r ops sA).map (historyProjection Subtype.val) =
      (sourceHistoryLaw N r ops sB).map (historyProjection Subtype.val) := by
  induction ops generalizing sA sB with
  | nil =>
      simp only [sourceHistoryLaw,historyLaw,PMF.pure_map]
      congr 1
      funext i
      exact Fin.elim0 i
  | cons op ops ih =>
      change ((sourceProgramStep N r op sA).bind
          (fun a => (sourceHistoryLaw N r ops a).map (Fin.cons a))).map
            (historyProjection Subtype.val) =
        ((sourceProgramStep N r op sB).bind
          (fun b => (sourceHistoryLaw N r ops b).map (Fin.cons b))).map
            (historyProjection Subtype.val)
      rw [PMF.map_bind,PMF.map_bind]
      apply actual_program_step_bind_same_raw N sampleA sampleB r op sA sB hraw
      intro a b hab
      have heA : ((sourceHistoryLaw N r ops a).map (Fin.cons a)).map
          (historyProjection Subtype.val) =
          ((sourceHistoryLaw N r ops a).map (historyProjection Subtype.val)).map
            (Fin.cons a.val) := by
        rw [PMF.map_comp,PMF.map_comp]
        congr 1
        funext z i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      have heB : ((sourceHistoryLaw N r ops b).map (Fin.cons b)).map
          (historyProjection Subtype.val) =
          ((sourceHistoryLaw N r ops b).map (historyProjection Subtype.val)).map
            (Fin.cons b.val) := by
        rw [PMF.map_comp,PMF.map_comp]
        congr 1
        funext z i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [heA,heB,ih a b hab,hab]

#print axioms actual_jump_bind_same_raw
#print axioms actual_completion_bind_same_raw
#print axioms actual_completed_program_raw_sample_transport
#print axioms actual_source_history_raw_sample_transport
end G3OriginalSampleParametricity
