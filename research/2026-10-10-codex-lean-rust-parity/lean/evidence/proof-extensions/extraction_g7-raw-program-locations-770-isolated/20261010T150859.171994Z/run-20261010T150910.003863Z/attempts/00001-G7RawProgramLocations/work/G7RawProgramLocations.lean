import G7RawEpochLocations
import G7RawBoundaryLocations
import G7EffectiveWordCoefficients

/-!
# Pointwise location trace of every raw original word

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Uses the unchanged original ProgramStep list. Intervals preserve each copied
population and original boundaries satisfy the inherited NodeMovement or
exitLocation relation. Every raw coefficient branch is included, even when
its polynomial vanishes. No new calendar agenda or stochastic support is used.
Draft pending sole-scheduler kernel checking and complete owned audit.
-/
namespace GProgram.G7.RawProgramLocations
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.EffectiveBoundaryCoefficients
open GProgram.G7.FullEpochSupport GProgram.G7.EffectiveNodeCoefficients
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.SparseWordComposition
open GProgram.G7.SymbolicProgramPolynomial
open GProgram.G7.RawEpochLocations GProgram.G7.RawBoundaryLocations
open scoped NNReal

variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- The location consequence of an inherited original operation, rather than
an invented finite-state kernel. -/
def programMovement (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s d : Code N sample) : Prop :=
  match op with
  | .interval _ => ∀ x : Copy, copyLocation (state d) x = copyLocation (state s) x
  | .boundary b => match b with
    | .exit e => ∀ x : Copy,
        copyLocation (state d) x = exitLocation N e (copyLocation (state s) x)
    | .ordinary e _ => ∀ x : Copy,
        NodeMovement N (N.graph.target e) (copyLocation (state s) x) (copyLocation (state d) x)
    | .root => ∀ x : Copy,
        NodeMovement N N.root (copyLocation (state s) x) (copyLocation (state d) x)
    | .independent H _ => ∀ x : Copy,
        NodeMovement N H.hybrid (copyLocation (state s) x) (copyLocation (state d) x)
    | .common H => ∀ x : Copy,
        NodeMovement N H.hybrid (copyLocation (state s) x) (copyLocation (state d) x)

lemma programMovement_original_node (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (s d : Code N sample) :
    programMovement N (.boundary (originalNodeOperation N H gamma common v)) s d ↔
      ∀ x : Copy, NodeMovement N v (copyLocation (state s) x) (copyLocation (state d) x) := by
  classical
  by_cases hr : v = N.root
  · subst v
    simp [originalNodeOperation,programMovement]
  · by_cases hh : N.graph.IsHybrid v
    · cases hc : common ⟨v,hh⟩ <;>
        simp [originalNodeOperation,hr,hh,hc,programMovement,H.original_site]
    · simp only [originalNodeOperation,dif_neg hr,dif_neg hh,programMovement,
        (defaultSelector N).target]

/-- Structural trace through the SAME original ProgramStep list. -/
def programTrace (N : RootedBinary V E X) {sample : Copy → X} :
    List (ProgramStep N) → Code N sample → Code N sample → Prop
  | [],s,d => d = s
  | op::ops,s,d => ∃ m, programMovement N op s m ∧ programTrace N ops m d

lemma programTrace_append (N : RootedBinary V E X) {sample : Copy → X}
    (xs ys : List (ProgramStep N)) (s d : Code N sample) :
    programTrace N (xs ++ ys) s d ↔
      ∃ m, programTrace N xs s m ∧ programTrace N ys m d := by
  induction xs generalizing s with
  | nil => simp [programTrace]
  | cons op xs ih =>
      simp only [List.cons_append,programTrace,ih]
      constructor
      · rintro ⟨z,hz,m,hzm,hmd⟩
        exact ⟨m,⟨z,hz,hzm⟩,hmd⟩
      · rintro ⟨m,⟨z,hz,hzm⟩,hmd⟩
        exact ⟨z,hz,m,hzm,hmd⟩

theorem stepRows_movement (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dur : J → ℝ≥0) (op : Symbol J V E)
    (s : Code N sample) (row : Code N sample × Sparse (WordVariable N J))
    (hrow : row ∈ stepRows N H common op s) :
    programMovement N (instantiateGamma N H gamma common dur op) s row.1 := by
  cases op with
  | interval j =>
      change row ∈ renameRows (fun i => Sum.inl (j,i)) (epochRows N s) at hrow
      unfold renameRows at hrow
      rcases List.mem_map.mp hrow with ⟨a,ha,he⟩
      rw [← he]
      exact fun x => epochRows_copyLocation N s a ha x
  | exit e =>
      change ∀ x : Copy,
        copyLocation (state row.1) x = exitLocation N e (copyLocation (state s) x)
      rw [exitRows_destination N s e row hrow]
      exact exitCode_copyLocation N s e
  | enter v =>
      apply (programMovement_original_node N H gamma common v s row.1).mpr
      change row ∈ renameRows Sum.inr (nodeRows N H common v s) at hrow
      unfold renameRows at hrow
      rcases List.mem_map.mp hrow with ⟨a,ha,he⟩
      rw [← he]
      exact fun x => nodeRows_movement N H common v s a ha x

/-- Entire literal raw support follows the original operation trace.
Coefficient-zero rows are deliberately not removed from the conclusion. -/
theorem wordRows_trace (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dur : J → ℝ≥0) (word : List (Symbol J V E))
    (s : Code N sample) (row : Code N sample × Sparse (WordVariable N J))
    (hrow : row ∈ wordRows N H common word s) :
    programTrace N (word.map (instantiateGamma N H gamma common dur)) s row.1 := by
  induction word generalizing s row with
  | nil =>
      have he : row = (s,single 1) := List.mem_singleton.mp hrow
      exact congrArg Prod.fst he
  | cons op word ih =>
      change row ∈ bindRows (stepRows N H common op s)
        (followRows (stepRows N H common) word) at hrow
      rcases List.mem_flatMap.mp hrow with ⟨a,ha,hrow⟩
      rcases List.mem_map.mp hrow with ⟨b,hb,he⟩
      rw [← he]
      exact ⟨a.1,stepRows_movement N H gamma common dur op s a ha,
        ih a.1 b hb⟩

#print axioms programMovement_original_node
#print axioms programTrace_append
#print axioms stepRows_movement
#print axioms wordRows_trace
end GProgram.G7.RawProgramLocations
