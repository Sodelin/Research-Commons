import G2UniversalTransitionCriterion
import UnifiedLean.Source.SourceCrossCarrierProgram

/-!
# Original G2 universal operator criterion at actual source matrices
Contributor: dot (OpenAI), 2026-10-05.
The actual generator and pulse identities below are DERIVED from the accepted
original full/small source providers. They are not constructor fields assuming
the desired biological equality. Universal test words must not be confused
with physically available reorderings of one fixed biological chronology.
-/
namespace GProgram.G2.ActualSourceTransitionCriterion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Matrix NormedSpace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierProgram
open GProgram.G2.UniversalTransitionCriterion
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def actualBoundaryMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) :
    Matrix (JoinedCode N sample keep) (JoinedCode N sample keep) ℝ :=
  fun s d => ((joinedBoundary N (sample := sample) keep op s) d).toReal

noncomputable def selectedBoundaryMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) :
    Matrix (JoinedIndex N sample keep) (JoinedIndex N sample keep) ℝ :=
  fun v w => (((joinedBoundary N (sample := sample) keep op (joinedRepresentative N (sample := sample) keep v)).map
    (joinedProjection N (sample := sample) keep)) w).toReal

/-- Actual source pulse intertwining, proved from original live-ancestor pulse
transport and the actual full/small selected-view quotient. -/
theorem actual_boundary_matrix_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (op : BoundaryOperation N) :
    actualBoundaryMatrix N (sample := sample) keep op * joinedProjectionMatrix N (sample := sample) keep =
      joinedProjectionMatrix N (sample := sample) keep * selectedBoundaryMatrix N (sample := sample) keep op := by
  ext s v
  rw [Matrix.mul_apply, Matrix.mul_apply]
  change (∑ d : JoinedCode N sample keep, ((joinedBoundary N (sample := sample) keep op s) d).toReal *
    if joinedProjection N (sample := sample) keep d = v then 1 else 0) =
    ∑ w : JoinedIndex N sample keep,
      (if joinedProjection N (sample := sample) keep s = w then (1 : ℝ) else 0) * selectedBoundaryMatrix N (sample := sample) keep op w v
  have hmap := map_probability_real (joinedBoundary N (sample := sample) keep op s)
    (joinedProjection N keep) v
  have h := joined_boundary_row_independent N (sample := sample) keep op s
    (joinedRepresentative N keep (joinedProjection N keep s))
    (joinedRepresentative_view N keep (joinedProjection N keep s)).symm
  have he : (((joinedBoundary N keep op s).map (joinedProjection N keep)) v).toReal =
      selectedBoundaryMatrix N keep op (joinedProjection N keep s) v :=
    congrArg (fun p => (p v).toReal) h
  have hs : (∑ w : JoinedIndex N sample keep,
      (if joinedProjection N keep s = w then (1 : ℝ) else 0) * selectedBoundaryMatrix N keep op w v) =
      selectedBoundaryMatrix N keep op (joinedProjection N keep s) v := by simp
  convert hmap.symm.trans (he.trans hs.symm) using 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : joinedProjection N keep a = v <;> simp [ha]

/-- Full iff instantiated at the actual original-source matrices. Its left
side is separately discharged below, not left as a source admission premise. -/
theorem actual_source_universal_criterion (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) :
    (joinedGenerator N (sample := sample) r keep * joinedProjectionMatrix N (sample := sample) keep =
        joinedProjectionMatrix N (sample := sample) keep * commonViewGenerator N (sample := sample) r keep ∧
      ∀ op, actualBoundaryMatrix N (sample := sample) keep op * joinedProjectionMatrix N (sample := sample) keep =
        joinedProjectionMatrix N (sample := sample) keep * selectedBoundaryMatrix N (sample := sample) keep op) ↔
    ∀ w : List (TestStep (BoundaryOperation N)),
      programMatrix (joinedGenerator N (sample := sample) r keep) (actualBoundaryMatrix N (sample := sample) keep) w * joinedProjectionMatrix N (sample := sample) keep =
        joinedProjectionMatrix N (sample := sample) keep *
          programMatrix (commonViewGenerator N (sample := sample) r keep) (selectedBoundaryMatrix N (sample := sample) keep) w :=
  generator_and_pulses_iff_all_programs _ _ _ _ _

/-- All operator test programs intertwine because the original source
identities were proved by the accepted providers, not assumed here. -/
theorem actual_source_all_operator_tests (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (w : List (TestStep (BoundaryOperation N))) :
    programMatrix (joinedGenerator N (sample := sample) r keep) (actualBoundaryMatrix N (sample := sample) keep) w *
        joinedProjectionMatrix N (sample := sample) keep =
      joinedProjectionMatrix N (sample := sample) keep *
        programMatrix (commonViewGenerator N (sample := sample) r keep) (selectedBoundaryMatrix N (sample := sample) keep) w :=
  (actual_source_universal_criterion N (sample := sample) r keep).mp
    ⟨actual_cross_carrier_generator_intertwining N (sample := sample) r keep,
      actual_boundary_matrix_intertwining N (sample := sample) keep⟩ w

/-- Syntax adapter only: physical use is restricted to the source's admitted
chronological program, not all algebraically available pulse words. -/
def sourceTestWord (N : RootedBinary V E X) :
    List (ProgramStep N) → List (TestStep (BoundaryOperation N)) :=
  List.map (fun op => match op with
    | .interval t => .inl t
    | .boundary b => .inr b)

/-- The interval matrix is the actual original-source PMF, not a new fitted
semigroup introduced just for the operator criterion. -/
theorem actual_interval_matrix_binding (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) :
    (fun s d : JoinedCode N sample keep => (joinedTimeKernel N (sample := sample) r keep t s d).toReal) =
      exp ((t : ℝ) • joinedGenerator N (sample := sample) r keep) := by
  ext s d
  rw [joined_exponential_blocks]
  cases s <;> cases d <;>
    simp [joinedTimeKernel, PMF.map_apply, source_time_kernel_eq_exponential]

/-- Exact finite-program binding of the criterion to the existing biological
PMF compiler. This does not turn arbitrary operator words into physical access. -/
theorem actual_program_matrix_binding (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s d : JoinedCode N sample keep) :
    programMatrix (joinedGenerator N (sample := sample) r keep) (actualBoundaryMatrix N (sample := sample) keep) (sourceTestWord N ops) s d =
      (joinedProgram N (sample := sample) r keep ops s d).toReal := by
  induction ops generalizing s with
  | nil =>
    by_cases h : d = s <;>
      simp [sourceTestWord, programMatrix, joinedProgram, PMF.pure_apply, eq_comm, h]
  | cons op ops ih =>
    simp only [sourceTestWord, List.map_cons, programMatrix, joinedProgram,
      bind_probability_real, tsum_fintype, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro q _
    apply congrArg₂ (fun a b : ℝ => a * b)
    · cases op with
      | interval t =>
        exact (congrArg (fun M => M s q) (actual_interval_matrix_binding N (sample := sample) r keep t)).symm
      | boundary b => rfl
    · exact ih q

/-- The criterion's actual-source matrix instance and the independently
proved actual PMF transport agree on the SAME admitted source program. This
retains the original parameters and current selected-view initialization.
No full continuous path-measure claim is added. -/
theorem actual_source_criterion_and_program_transport (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (z : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state z) Finset.univ)) :
    (programMatrix (joinedGenerator N (sample := sample) r keep) (actualBoundaryMatrix N (sample := sample) keep) (sourceTestWord N ops) *
        joinedProjectionMatrix N (sample := sample) keep =
      joinedProjectionMatrix N (sample := sample) keep *
        programMatrix (commonViewGenerator N (sample := sample) r keep) (selectedBoundaryMatrix N (sample := sample) keep) (sourceTestWord N ops)) ∧
    ((sourceProgram N r ops s).map (fun d => joinedProjection N (sample := sample) keep (.inl d)) =
      (sourceProgram N r ops z).map (fun d => joinedProjection N (sample := sample) keep (.inr d))) :=
  ⟨actual_source_all_operator_tests N (sample := sample) r keep _, actual_cross_carrier_program_law N r keep ops s z hs⟩

#print axioms actual_interval_matrix_binding
#print axioms actual_program_matrix_binding
#print axioms actual_boundary_matrix_intertwining
#print axioms actual_source_universal_criterion
#print axioms actual_source_all_operator_tests
#print axioms actual_source_criterion_and_program_transport
end GProgram.G2.ActualSourceTransitionCriterion
