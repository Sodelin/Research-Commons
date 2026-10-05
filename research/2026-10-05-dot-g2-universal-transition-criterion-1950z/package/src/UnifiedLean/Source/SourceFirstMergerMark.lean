import UnifiedLean.Source.SourceActualHoldingClocks

/-!
# Genuine source first-merger mark retained without changing source dynamics

Contributor: dot, 2026-10-02. Augments the ACTUAL epoch state by its first actual
original-population CURRENT pair choice. Forgetting the latent mark gives the
existing source step/iteration/Poisson kernel; its marginal is the actual
absorbing first-choice process. This is proof-state instrumentation, not an
added physical control or claim that the original passive menu measures it.
Winning exponential-clock label/time and reset equivalence remain next gates.
-/
namespace UnifiedLean.Source.SourceFirstMergerMark
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- None means no real merger and the actual source is still s. After one
real merger, its actual initial choice and the evolving source state are stored. -/
abbrev FirstState (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :=
  Option (Choice N s × Code N sample)

noncomputable def forgetFirst (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : FirstState N s → Code N sample
  | none => s
  | some q => q.2

noncomputable def firstMark (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : FirstState N s → Option (Choice N s)
  | none => none
  | some q => some q.1

noncomputable def firstDestination (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Option (Choice N s) → FirstState N s
  | none => none
  | some p => some (p,stepDestination N s (some p))

noncomputable def firstSourceStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : FirstState N s → PMF (FirstState N s)
  | none => (choicePMF N r s).map (firstDestination N s)
  | some q => (sourceStep N r q.2).map (fun d => some (q.1,d))

noncomputable def stoppedMarkStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Option (Choice N s) → PMF (Option (Choice N s))
  | none => choicePMF N r s
  | some p => PMF.pure (some p)

/-- The augmented primitive is EXACTLY the original physical source step
when its latent first-choice proof record is forgotten. -/
theorem first_source_step_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (z : FirstState N s) :
    (firstSourceStep N r s z).map (forgetFirst N s) = sourceStep N r (forgetFirst N s z) := by
  cases z with
  | none =>
      rw [firstSourceStep,PMF.map_comp]
      change (choicePMF N r s).map ((forgetFirst N s) ∘ firstDestination N s) = _
      have h : (forgetFirst N s) ∘ firstDestination N s = stepDestination N s := by
        funext p
        cases p <;> rfl
      rw [h]
      rfl
  | some q =>
      rw [firstSourceStep,PMF.map_comp]
      change (sourceStep N r q.2).map id = _
      rw [PMF.map_id]
      rfl

/-- Its actual first-mark marginal uses actual CURRENT original source choices;
there is no desired winner distribution supplied as a source field. -/
theorem first_source_step_mark (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (z : FirstState N s) :
    (firstSourceStep N r s z).map (firstMark N s) = stoppedMarkStep N r s (firstMark N s z) := by
  cases z with
  | none =>
      rw [firstSourceStep,PMF.map_comp]
      change (choicePMF N r s).map ((firstMark N s) ∘ firstDestination N s) = _
      have h : (firstMark N s) ∘ firstDestination N s = id := by
        funext p
        cases p <;> rfl
      rw [h,PMF.map_id]
      rfl
  | some q =>
      rw [firstSourceStep,PMF.map_comp]
      change (sourceStep N r q.2).map (Function.const _ (some q.1)) = _
      rw [PMF.map_const]
      rfl

noncomputable def firstSourceIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Nat → FirstState N s → PMF (FirstState N s)
  | 0,z => PMF.pure z
  | k+1,z => (firstSourceStep N r s z).bind (firstSourceIteration N r s k)

noncomputable def stoppedMarkIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Nat → Option (Choice N s) → PMF (Option (Choice N s))
  | 0,z => PMF.pure z
  | k+1,z => (stoppedMarkStep N r s z).bind (stoppedMarkIteration N r s k)

/-- All actual source iterations are preserved, including real post-first-merger
source evolution and its current-root pair resets. -/
theorem first_iteration_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (z : FirstState N s) :
    (firstSourceIteration N r s k z).map (forgetFirst N s) =
      sourceIteration N r k (forgetFirst N s z) := by
  induction k generalizing z with
  | zero => simp only [firstSourceIteration,sourceIteration,PMF.pure_map]
  | succ k ih =>
      rw [firstSourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (firstSourceStep N r s z).bind (sourceIteration N r k ∘ forgetFirst N s) = _
      rw [← PMF.bind_map,first_source_step_forget]
      rfl

theorem first_iteration_mark (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (z : FirstState N s) :
    (firstSourceIteration N r s k z).map (firstMark N s) =
      stoppedMarkIteration N r s k (firstMark N s z) := by
  induction k generalizing z with
  | zero => simp only [firstSourceIteration,stoppedMarkIteration,PMF.pure_map]
  | succ k ih =>
      rw [firstSourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (firstSourceStep N r s z).bind (stoppedMarkIteration N r s k ∘ firstMark N s) = _
      rw [← PMF.bind_map,first_source_step_mark]
      rfl

noncomputable def firstSourceTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (z : FirstState N s) : PMF (FirstState N s) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind (fun k => firstSourceIteration N r s k z)

noncomputable def firstMarkTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0)
    (z : Option (Choice N s)) : PMF (Option (Choice N s)) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind (fun k => stoppedMarkIteration N r s k z)

/-- Whole original epoch PMF is preserved by this latent first-event record. -/
theorem first_time_kernel_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (z : FirstState N s) :
    (firstSourceTimeKernel N r s t z).map (forgetFirst N s) =
      sourceTimeKernel N r t (forgetFirst N s z) := by
  rw [firstSourceTimeKernel,sourceTimeKernel,PMF.map_bind]
  simp_rw [first_iteration_forget]

/-- First-event marginal derives from the ACTUAL continued source process. -/
theorem first_time_kernel_mark (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (z : FirstState N s) :
    (firstSourceTimeKernel N r s t z).map (firstMark N s) = firstMarkTimeKernel N r s t (firstMark N s z) := by
  rw [firstSourceTimeKernel,firstMarkTimeKernel,PMF.map_bind]
  simp_rw [first_iteration_mark]

#print axioms first_source_step_forget
#print axioms first_source_step_mark
#print axioms first_time_kernel_forget
#print axioms first_time_kernel_mark
end UnifiedLean.Source.SourceFirstMergerMark
