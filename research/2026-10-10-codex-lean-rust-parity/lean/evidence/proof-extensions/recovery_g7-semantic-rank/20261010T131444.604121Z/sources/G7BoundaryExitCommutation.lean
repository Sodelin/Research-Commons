import G7GlobalOwnerCoins

/-! Distinct original edge exits commute on the actual finite source snapshot.
This lemma concerns the exits phase only; it does not permute exits with node
entries. Contributor: dot, 2026-10-09. -/
namespace GProgram.G7.BoundaryExitCommutation
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open scoped Classical
variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [Fintype Copy] [DecidableEq Copy]

theorem exit_location_commute (N : RootedBinary V E X) (a b : E) (h : a ≠ b)
    (l : Location V E) :
    (if (if l = .edge a then .node (N.graph.source a) else l) = .edge b
      then .node (N.graph.source b) else if l = .edge a then .node (N.graph.source a) else l) =
    (if (if l = .edge b then .node (N.graph.source b) else l) = .edge a
      then .node (N.graph.source a) else if l = .edge b then .node (N.graph.source b) else l) := by
  by_cases ha : l = .edge a
  · subst l
    simp [h,Ne.symm h]
  · by_cases hb : l = .edge b
    · subst l
      simp [h,Ne.symm h]
    · simp [ha,hb]

theorem exit_code_commute (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a b : E) (h : a ≠ b) :
    exitCode N (exitCode N s a) b = exitCode N (exitCode N s b) a := by
  apply Subtype.ext
  apply Snapshot.ext
  · rfl
  · rfl
  · funext l
    simp [exitCode,admittedCode,encodeSnapshot,state,decodeSnapshot,exitEdge,transport] <;> rfl
  · funext l
    by_cases hl : l ∈ (state s).live
    · simp only [exitCode,admittedCode,encodeSnapshot,state,decodeSnapshot,exitEdge,transport] at hl ⊢
      simp only [hl,if_pos,Option.some.injEq]
      exact exit_location_commute N a b h _
    · simp [exitCode,admittedCode,encodeSnapshot,state,decodeSnapshot,exitEdge,transport] at hl ⊢
      simp [hl]
  · rfl

#print axioms exit_code_commute
end GProgram.G7.BoundaryExitCommutation
