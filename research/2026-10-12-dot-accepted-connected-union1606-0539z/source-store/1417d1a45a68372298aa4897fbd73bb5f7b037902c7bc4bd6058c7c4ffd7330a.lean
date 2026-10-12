import ActualUnusedSeedConditioning
import ActualCommonBigonSurvival

/-! The actual finite-program PMF retains its entering register.
This is the PMF consumer of the inherited source primitive invariant,
not an independence assertion. dot (OpenAI), 9 October 2026. -/
namespace DotG34.ActualStoredRegister
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_step_register (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (sourceStep N r s).map (fun d => (state d).register) = PMF.pure (state s).register := by
  rw [sourceStep, PMF.map_comp]
  have he : (fun d : Code N sample => (state d).register) ∘ stepDestination N s =
      fun _ => (state s).register := by
    funext p
    cases p <;> rfl
  rw [he]
  exact PMF.map_const _ _

theorem actual_iteration_register (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : ℕ) (s : Code N sample) :
    (sourceIteration N r k s).map (fun d => (state d).register) =
      PMF.pure (state s).register := by
  induction k generalizing s with
  | zero => exact PMF.pure_map _ _
  | succ k ih =>
      rw [sourceIteration, PMF.map_bind]
      simp_rw [ih]
      exact actual_step_register N r s

theorem actual_epoch_register (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (fun d => (state d).register) =
      PMF.pure (state s).register := by
  rw [sourceTimeKernel, PMF.map_bind]
  simp_rw [actual_iteration_register]
  simp

theorem actual_boundary_register (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) :
    (boundaryKernel N op s).map (fun d => (state d).register) =
      PMF.pure (state s).register := by
  cases op with
  | exit e => exact PMF.pure_map _ _
  | ordinary e hd => exact PMF.pure_map _ _
  | root => exact PMF.pure_map _ _
  | common H => exact PMF.pure_map _ _
  | independent H gamma =>
      change ((currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
        (pulseCode H s)).map _ = _
      rw [PMF.map_comp]
      change (currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
        (fun _ => (state s).register) = _
      exact PMF.map_const _ _

theorem actual_program_register (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r ops s).map (fun d => (state d).register) =
      PMF.pure (state s).register := by
  induction ops generalizing s with
  | nil => exact PMF.pure_map _ _
  | cons op ops ih =>
      rw [sourceProgram, PMF.map_bind]
      simp_rw [ih]
      change (sourceProgramStep N r op s).map (fun d => (state d).register) = _
      cases op with
      | interval t => exact actual_epoch_register N r t s
      | boundary op => exact actual_boundary_register N op s

theorem actual_program_register_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hd : d ∈ (sourceProgram N r ops s).support) :
    (state d).register = (state s).register := by
  have hm : (state d).register ∈
      ((sourceProgram N r ops s).map (fun z => (state z).register)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨d, hd, rfl⟩
  rw [actual_program_register] at hm
  simpa only [PMF.support_pure, Set.mem_singleton_iff] using hm

/-- A COMMON pulse after any actual finite prefix reads the original entering
register. The all-current-roots entrance is explicit, not inferred from a
formal operation list. No independence or refreshed seed is used here. -/
theorem actual_common_after_prefix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hd : d ∈ (sourceProgram N r ops s).support)
    (H : GProgram.G2.OriginalHybridParents N) (t : ℝ≥0)
    (hall : ∀ l ∈ (state d).live, (state d).location l = .node H.hybrid) :
    let n := Fintype.card (AtNode (state d) H.hybrid)
    (((sourceProgram N r [.boundary (.common H), .interval t] d).map
      UnifiedLean.Source.SourceActualHoldingClocks.liveCard) (UnifiedLean.Source.SourceActualHoldingClocks.liveCard d)).toReal =
    if (state s).register H.hybrid then
      (Real.exp (-(pairRate r (some H.parent1)*(t:ℝ))))^(n.choose 2)
    else (Real.exp (-(pairRate r (some H.parent0)*(t:ℝ))))^(n.choose 2) := by
  rw [DotG34.ActualCommonBigonSurvival.actual_common_bigon_survival N r H t d hall,
    actual_program_register_support N r ops s d hd]

#print axioms actual_program_register_support
#print axioms actual_common_after_prefix
#print axioms actual_step_register
#print axioms actual_iteration_register
#print axioms actual_epoch_register
#print axioms actual_boundary_register
#print axioms actual_program_register
end DotG34.ActualStoredRegister
