import UnifiedLean.Source.SourceCrossCarrierProgram

/-!
Finite histories of the original source step kernels and their derived common
view law. Contributor: dot (OpenAI), 6 October 2026. This source-level PMF
transport uses the preserved actual epoch/boundary row theorem. Binding it to
literal same-clock histories is a separate required construction.
-/
namespace GProgram.G2.SourceFiniteHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.SourceCrossCarrierEpoch UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceBoundaryKernels
open scoped Classical

noncomputable def historyLaw {S Op : Type*} (K : Op → S → PMF S) :
    (ops : List Op) → S → PMF (Fin ops.length → S)
  | [],_ => PMF.pure (fun i => Fin.elim0 i)
  | op::ops,s => (K op s).bind (fun d => (historyLaw K ops d).map (Fin.cons d))

def historyProjection {S Q : Type*} {n : Nat} (f : S → Q) (z : Fin n → S) : Fin n → Q :=
  fun i => f (z i)

/-- Elementary finite-history transport. In the actual source applications
below its sole one-step hypothesis is discharged by the original proved rows. -/
theorem history_projection {S Q Op : Type*} (K : Op → S → PMF S)
    (L : Op → Q → PMF Q) (f : S → Q)
    (hstep : ∀ op s, (K op s).map f = L op (f s))
    (ops : List Op) (s : S) :
    (historyLaw K ops s).map (historyProjection f) = historyLaw L ops (f s) := by
  induction ops generalizing s with
  | nil =>
      rw [historyLaw,historyLaw,PMF.pure_map]
      congr 1
      funext i
      exact Fin.elim0 i
  | cons op ops ih =>
      rw [historyLaw,PMF.map_bind]
      have he (d : S) : ((historyLaw K ops d).map (Fin.cons d)).map (historyProjection f) =
          ((historyLaw K ops d).map (historyProjection f)).map (Fin.cons (f d)) := by
        rw [PMF.map_comp,PMF.map_comp]
        congr 1
        funext z i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      simp_rw [he,ih]
      change (K op s).bind ((fun q => (historyLaw L ops q).map (Fin.cons q)) ∘ f) = _
      rw [← PMF.bind_map,hstep]
      rfl

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def sourceHistoryLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    PMF (Fin ops.length → Code N sample) := historyLaw (sourceProgramStep N r) ops s

noncomputable def commonHistoryLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : JoinedIndex N sample keep) : PMF (Fin ops.length → JoinedIndex N sample keep) :=
  historyLaw (commonProgramStep N r keep) ops s

lemma full_source_step_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N) (s : Code N sample) :
    (sourceProgramStep N r op s).map (fun d => joinedProjection N keep (.inl d)) =
      commonProgramStep N r keep op (joinedProjection N keep (.inl s)) := by
  have h := joined_actual_program_step N (sample := sample) r keep op (.inl s)
  cases op <;> simpa only [joinedProgramStep,joinedTimeKernel,joinedBoundary,
    sourceProgramStep,PMF.map_comp,Function.comp_def] using h

lemma small_source_step_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (s : Code N (selectedSample sample keep)) :
    (sourceProgramStep N r op s).map (fun d => joinedProjection N keep (.inr d)) =
      commonProgramStep N r keep op (joinedProjection N keep (.inr s)) := by
  have h := joined_actual_program_step N (sample := sample) r keep op (.inr s)
  cases op <;> simpa only [joinedProgramStep,joinedTimeKernel,joinedBoundary,
    sourceProgramStep,PMF.map_comp,Function.comp_def] using h

theorem actual_full_source_history_projection (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceHistoryLaw N r ops s).map
      (historyProjection (fun d => joinedProjection N keep (.inl d))) =
      commonHistoryLaw N r keep ops (joinedProjection N keep (.inl s)) :=
  history_projection _ _ _ (full_source_step_common N r keep) ops s

theorem actual_small_source_history_projection (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N (selectedSample sample keep)) :
    (sourceHistoryLaw N r ops s).map
      (historyProjection (fun d => joinedProjection N keep (.inr d))) =
      commonHistoryLaw N r keep ops (joinedProjection N keep (.inr s)) :=
  history_projection _ _ _ (small_source_step_common N r keep) ops s

/-- Actual full/small source finite histories, preserving every operation,
original parameter and observation coordinate. Empty panels are included. -/
theorem actual_cross_carrier_source_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (sourceHistoryLaw N r ops s).map
      (historyProjection (fun z => joinedProjection N keep (.inl z))) =
    (sourceHistoryLaw N r ops d).map
      (historyProjection (fun z => joinedProjection N keep (.inr z))) := by
  rw [actual_full_source_history_projection,actual_small_source_history_projection]
  have h : joinedProjection N keep (.inl s) = joinedProjection N keep (.inr d) := Subtype.ext hs
  rw [h]

#print axioms history_projection
#print axioms full_source_step_common
#print axioms small_source_step_common
#print axioms actual_full_source_history_projection
#print axioms actual_small_source_history_projection
#print axioms actual_cross_carrier_source_history
end GProgram.G2.SourceFiniteHistory
