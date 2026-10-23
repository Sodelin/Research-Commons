import UnifiedLean.Source.SourceCrossCarrierBoundary

/-!
# Coherent actual full/small source programme transport

Contributor: dot, 2026-10-02. Composes actual cross-carrier epoch and original
boundary laws, rather than assuming a programme comparison. Actual small copy
initialization is separate and proved to share the original labelled view.
-/
namespace UnifiedLean.Source.SourceCrossCarrierProgram
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Matrix NormedSpace MeasureTheory
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierBoundary
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def joinedTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) :
    JoinedCode N sample keep → PMF (JoinedCode N sample keep)
  | .inl s => (sourceTimeKernel N r t s).map Sum.inl
  | .inr s => (sourceTimeKernel N r t s).map Sum.inr

noncomputable def joinedBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) :
    JoinedCode N sample keep → PMF (JoinedCode N sample keep)
  | .inl s => (boundaryKernel N op s).map Sum.inl
  | .inr s => (boundaryKernel N op s).map Sum.inr

lemma joined_time_projected_real (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (s : JoinedCode N sample keep)
    (v : JoinedIndex N sample keep) :
    (((joinedTimeKernel N r keep t s).map (joinedProjection N keep)) v).toReal =
      (exp ((t : ℝ) • commonViewGenerator N r keep)) (joinedProjection N keep s) v := by
  cases s with
  | inl s =>
      simp only [joinedTimeKernel,PMF.map_comp,Function.comp_def]
      exact full_actual_time_common_row N r keep t s v
  | inr s =>
      simp only [joinedTimeKernel,PMF.map_comp,Function.comp_def]
      exact small_actual_time_common_row N r keep t s v

lemma joined_time_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (s z : JoinedCode N sample keep)
    (hs : joinedView N keep s = joinedView N keep z) :
    (joinedTimeKernel N r keep t s).map (joinedProjection N keep) =
      (joinedTimeKernel N r keep t z).map (joinedProjection N keep) := by
  have he : joinedProjection N keep s = joinedProjection N keep z := Subtype.ext hs
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [joined_time_projected_real,joined_time_projected_real,he]

local instance viewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤

lemma small_boundary_view_independent (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s z : Code N (selectedSample sample keep))
    (hs : liftView keep (selectedView (state s) Finset.univ) = liftView keep (selectedView (state z) Finset.univ)) :
    (boundaryKernel N op s).map (fun d => liftView keep (selectedView (state d) Finset.univ)) =
      (boundaryKernel N op z).map (fun d => liftView keep (selectedView (state d) Finset.univ)) := by
  cases op with
  | exit e => simp only [boundaryKernel,PMF.pure_map,exitCode_view,lift_transportView,hs]
  | ordinary e degree => simp only [boundaryKernel,PMF.pure_map,ordinaryCode_view,lift_transportView,hs]
  | root => simp only [boundaryKernel,PMF.pure_map,rootCode_view,lift_transportView,hs]
  | common H => rw [small_common_kernel_view,small_common_kernel_view,hs]
  | independent H gamma =>
      apply PMF.toMeasure_injective
      change ((independentPulseKernel H gamma s).map _).toMeasure =
        ((independentPulseKernel H gamma z).map _).toMeasure
      rw [small_independent_kernel_view_measure,small_independent_kernel_view_measure,hs]

lemma joined_boundary_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s z : JoinedCode N sample keep)
    (hs : joinedView N keep s = joinedView N keep z) :
    (joinedBoundary N keep op s).map (joinedProjection N keep) =
      (joinedBoundary N keep op z).map (joinedProjection N keep) := by
  cases s with
  | inl s =>
      cases z with
      | inl z =>
          apply pmf_map_injective Subtype.val Subtype.val_injective
          simp only [joinedBoundary,PMF.map_comp,Function.comp_def,joinedProjection,joinedView]
          exact boundary_kernel_view_eq_of_same_view N keep op s z hs
      | inr z =>
          simp only [joinedBoundary,PMF.map_comp,Function.comp_def]
          exact actual_cross_carrier_boundary_law N keep op s z hs
  | inr s =>
      cases z with
      | inl z =>
          simp only [joinedBoundary,PMF.map_comp,Function.comp_def]
          exact (actual_cross_carrier_boundary_law N keep op z s hs.symm).symm
      | inr z =>
          apply pmf_map_injective Subtype.val Subtype.val_injective
          simp only [joinedBoundary,PMF.map_comp,Function.comp_def,joinedProjection,joinedView]
          exact small_boundary_view_independent N keep op s z hs

noncomputable def joinedProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (s : JoinedCode N sample keep) : PMF (JoinedCode N sample keep) :=
  match op with
  | .interval t => joinedTimeKernel N r keep t s
  | .boundary b => joinedBoundary N keep b s

noncomputable def commonProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (v : JoinedIndex N sample keep) : PMF (JoinedIndex N sample keep) :=
  (joinedProgramStep N r keep op (joinedRepresentative N keep v)).map (joinedProjection N keep)

lemma joined_actual_program_step (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N) (s : JoinedCode N sample keep) :
    (joinedProgramStep N r keep op s).map (joinedProjection N keep) =
      commonProgramStep N r keep op (joinedProjection N keep s) := by
  have he := (joinedRepresentative_view N keep (joinedProjection N keep s)).symm
  cases op with
  | interval t => exact joined_time_row_independent N r keep t s _ he
  | boundary b => exact joined_boundary_row_independent N keep b s _ he

noncomputable def joinedProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    List (ProgramStep N) → JoinedCode N sample keep → PMF (JoinedCode N sample keep)
  | [],s => PMF.pure s
  | op::ops,s => (joinedProgramStep N r keep op s).bind (joinedProgram N r keep ops)

noncomputable def commonProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    List (ProgramStep N) → JoinedIndex N sample keep → PMF (JoinedIndex N sample keep)
  | [],s => PMF.pure s
  | op::ops,s => (commonProgramStep N r keep op s).bind (commonProgram N r keep ops)

/-- Whole actual two-source finite programme factorization is derived through
actual epoch/boundary rows, including the original shared register. -/
theorem joined_actual_program_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : JoinedCode N sample keep) :
    (joinedProgram N r keep ops s).map (joinedProjection N keep) =
      commonProgram N r keep ops (joinedProjection N keep s) := by
  induction ops generalizing s with
  | nil => simp only [joinedProgram,commonProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [joinedProgram,PMF.map_bind]
      simp_rw [ih]
      change (joinedProgramStep N r keep op s).bind (commonProgram N r keep ops ∘ joinedProjection N keep) = _
      rw [← PMF.bind_map,joined_actual_program_step]
      rfl

lemma joined_program_full (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample) :
    joinedProgram N r keep ops (.inl s) = (sourceProgram N r ops s).map Sum.inl := by
  induction ops generalizing s with
  | nil => simp only [joinedProgram,sourceProgram,PMF.pure_map]
  | cons op ops ih =>
      have hstep : joinedProgramStep N r keep op (.inl s) = (sourceProgramStep N r op s).map Sum.inl := by
        cases op <;> rfl
      rw [joinedProgram,hstep,PMF.bind_map]
      simp only [Function.comp_def]
      simp_rw [ih]
      rw [← PMF.map_bind]
      rfl

lemma joined_program_small (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N (selectedSample sample keep)) :
    joinedProgram N r keep ops (.inr s) = (sourceProgram N r ops s).map Sum.inr := by
  induction ops generalizing s with
  | nil => simp only [joinedProgram,sourceProgram,PMF.pure_map]
  | cons op ops ih =>
      have hstep : joinedProgramStep N r keep op (.inr s) = (sourceProgramStep N r op s).map Sum.inr := by
        cases op <;> rfl
      rw [joinedProgram,hstep,PMF.bind_map]
      simp only [Function.comp_def]
      simp_rw [ih]
      rw [← PMF.map_bind]
      rfl

/-- Actual full and independently initialized small-copy sources have equal
whole original-labelled view laws for ANY same-original operation programme,
from every pair of compatible actual initial states. -/
theorem actual_cross_carrier_program_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample)
    (z : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state z) Finset.univ)) :
    (sourceProgram N r ops s).map (fun d => joinedProjection N keep (.inl d)) =
      (sourceProgram N r ops z).map (fun d => joinedProjection N keep (.inr d)) := by
  have he : joinedProjection N keep (.inl s) = joinedProjection N keep (.inr z) := Subtype.ext hs
  have hf := joined_actual_program_projection N r keep ops (.inl s)
  have hz := joined_actual_program_projection N r keep ops (.inr z)
  rw [joined_program_full,PMF.map_comp] at hf
  rw [joined_program_small,PMF.map_comp] at hz
  exact hf.trans ((he ▸ hz).symm)

#print axioms joined_actual_program_step
#print axioms joined_actual_program_projection
#print axioms actual_cross_carrier_program_law
end UnifiedLean.Source.SourceCrossCarrierProgram
