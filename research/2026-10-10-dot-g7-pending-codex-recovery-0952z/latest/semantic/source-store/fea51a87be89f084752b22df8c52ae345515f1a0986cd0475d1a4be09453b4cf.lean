import G7NodeActions
import G7BoundaryExitCommutation

/-! Source-derived invariance under permutations WITHIN each original boundary
phase. Exits are never exchanged with node entries. Contributor: dot,2026-10-09. -/
namespace GProgram.G7.BoundaryPhasePermutation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open GProgram.G7.NodeActions GProgram.G7.BoundaryExitCommutation
open scoped Classical
variable {V E Copy X A : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [Fintype Copy] [DecidableEq Copy]

theorem program_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (xs ys : List (ProgramStep N)) (s : Code N sample) :
    sourceProgram N r (xs ++ ys) s =
      (sourceProgram N r xs s).bind (sourceProgram N r ys) := by
  induction xs generalizing s with
  | nil => simp [sourceProgram,PMF.pure_bind]
  | cons op xs ih =>
    simp only [List.cons_append,sourceProgram,PMF.bind_bind]
    congr 1
    funext t
    exact ih t

/-- Generic list induction used below with source-derived commutation laws. -/
theorem boundary_perm (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : A → BoundaryOperation N)
    (comm : ∀ a b (s : Code N sample),
      (boundaryKernel N (f a) s).bind (boundaryKernel N (f b)) =
      (boundaryKernel N (f b) s).bind (boundaryKernel N (f a)))
    {xs ys : List A} (h : xs.Perm ys) (s : Code N sample) :
    sourceProgram N r (xs.map (fun a => .boundary (f a))) s =
      sourceProgram N r (ys.map (fun a => .boundary (f a))) s := by
  induction h generalizing s with
  | nil => rfl
  | cons a h ih =>
    simp only [List.map_cons,sourceProgram]
    congr 1
    funext t
    exact ih t
  | swap a b xs =>
    simp only [List.map_cons,sourceProgram,sourceProgramStep]
    rw [← PMF.bind_bind,comm b a s,PMF.bind_bind]
  | trans h1 h2 ih1 ih2 => exact (ih1 s).trans (ih2 s)

theorem exit_phase_perm (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) {xs ys : List E} (h : xs.Perm ys) (s : Code N sample) :
    sourceProgram N r (xs.map (fun e => .boundary (.exit e))) s =
      sourceProgram N r (ys.map (fun e => .boundary (.exit e))) s := by
  apply boundary_perm N r (fun e => .exit e) ?_ h s
  intro a b t
  simp only [boundaryKernel,PMF.pure_bind]
  by_cases hab : a = b
  · subst b; rfl
  · rw [exit_code_commute N t a b hab]

theorem node_phase_perm (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {xs ys : List V} (h : xs.Perm ys) (s : Code N sample) :
    sourceProgram N r (xs.map (fun v => .boundary (originalNodeOperation N H gamma common v))) s =
      sourceProgram N r (ys.map (fun v => .boundary (originalNodeOperation N H gamma common v))) s := by
  apply boundary_perm N r (originalNodeOperation N H gamma common) ?_ h s
  intro a b t
  by_cases hab : a = b
  · subst b; rfl
  · rw [← original_operation N H gamma common a,← original_operation N H gamma common b]
    exact kernels_commute _ _ (by simpa only [original_site] using hab) t

#print axioms exit_phase_perm
#print axioms node_phase_perm
end GProgram.G7.BoundaryPhasePermutation
