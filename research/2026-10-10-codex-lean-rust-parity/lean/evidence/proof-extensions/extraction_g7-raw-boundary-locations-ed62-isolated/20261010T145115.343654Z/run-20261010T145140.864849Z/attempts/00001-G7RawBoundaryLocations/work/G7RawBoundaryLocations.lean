import G7EffectiveNodeCoefficients
import UnifiedLean.Source.SourceCalendarPhysicalSupport

/-!
# Pointwise original movement of every raw boundary row

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The original pointwise boundary locations and source-node movement are reused
for every enumerated routing coin. No coefficient positivity or PMF support
is assumed. Original register/parent occurrence conventions are unchanged.
Draft pending sole-scheduler kernel checking and complete owned audit.
-/
namespace GProgram.G7.RawBoundaryLocations
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceCalendarCompiler
open GProgram.G7.EffectivePopulationCoefficients GProgram.G7.EffectiveInitializationCoefficients
open GProgram.G7.EffectiveBoundaryCoefficients GProgram.G7.EffectiveNodeCoefficients
open GProgram.G7.SparseRowProducts

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

lemma pureRows_destination {I A : Type*} (a : A) (row : A × Sparse I)
    (hrow : row ∈ pureRows a) : row.1 = a :=
  congrArg Prod.fst (List.mem_singleton.mp hrow)

lemma exitRows_destination {I : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (row : Code N sample × Sparse I)
    (hrow : row ∈ exitRows N s e) : row.1 = exitCode N s e := by
  exact (pureRows_destination (exitCodeEffective N s e) row hrow).trans
    (exitCodeEffective_eq N s e)

theorem nodeRows_movement (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (s : Code N sample) (row : Code N sample × Sparse (Hybrid N))
    (hrow : row ∈ nodeRows N H common v s) (x : Copy) :
    NodeMovement N v (copyLocation (state s) x) (copyLocation (state row.1) x) := by
  classical
  by_cases hr : v = N.root
  · have hm : row ∈ pureRows (rootCodeEffective N s) := by
      simpa only [nodeRows,dif_pos hr] using hrow
    rw [pureRows_destination _ _ hm,rootCodeEffective_eq,rootCode_copyLocation]
    subst v
    unfold NodeMovement rootLocation
    by_cases hn : copyLocation (state s) x = .node N.root <;> simp [hn]
  · by_cases hh : N.graph.IsHybrid v
    · by_cases hc : common ⟨v,hh⟩ = true
      · have hm : row ∈ commonRows (H.parents ⟨v,hh⟩) s := by
          simpa only [nodeRows,dif_neg hr,dif_pos hh,if_pos hc] using hrow
        have hd := pureRows_destination
          (pulseCodeEffective (H.parents ⟨v,hh⟩) s
            (fun _ => (sourceState s).register (H.parents ⟨v,hh⟩).hybrid)) row hm
        rw [hd,pulseCodeEffective_eq]
        exact parent_move_is_node_movement N H ⟨v,hh⟩ hr
          (actual_pulse_code_location (H.parents ⟨v,hh⟩) s _ x)
      · have hm : row ∈ pulseRows ⟨v,hh⟩ (H.parents ⟨v,hh⟩) s := by
          simpa only [nodeRows,dif_neg hr,dif_pos hh,if_neg hc] using hrow
        rcases List.mem_map.mp hm with ⟨coin,_,he⟩
        rw [← he,pulseCodeEffective_eq]
        exact parent_move_is_node_movement N H ⟨v,hh⟩ hr
          (actual_pulse_code_location (H.parents ⟨v,hh⟩) s coin x)
    · have hm : row ∈ pureRows (ordinaryCodeEffective N s (incomingEdgeEffective N v hr)) := by
        simpa only [nodeRows,dif_neg hr,dif_neg hh] using hrow
      rw [pureRows_destination _ _ hm,ordinaryCodeEffective_eq,
        incomingEdgeEffective_eq N v hr hh,ordinaryCode_copyLocation]
      let e := (defaultSelector N).edge ⟨v,hr⟩
      have he : N.graph.target e = v := (defaultSelector N).target _
      change NodeMovement N v (copyLocation (state s) x)
        (ordinaryLocation N e (copyLocation (state s) x))
      unfold NodeMovement ordinaryLocation
      rw [he]
      by_cases hn : copyLocation (state s) x = .node v
      · rw [if_pos hn,if_pos hn,if_neg hr]
        exact ⟨e,he,rfl⟩
      · simp only [if_neg hn]

theorem exitRows_ready {I : Type*} (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X} {a : ℝ}
    (s : Code N sample) (e : E) (he : C.age (N.graph.source e) = a)
    (hs : BoundaryReady N C a (state s)) (row : Code N sample × Sparse I)
    (hrow : row ∈ exitRows N s e) : BoundaryReady N C a (state row.1) := by
  rw [exitRows_destination N s e row hrow]
  exact exit_preserves_ready N C s e he hs

theorem nodeRows_after_exits (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X} {a : ℝ}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (hv : C.age v = a) (s : Code N sample) (hs : AfterExits N C a (state s))
    (row : Code N sample × Sparse (Hybrid N)) (hrow : row ∈ nodeRows N H common v s) :
    AfterExits N C a (state row.1) ∧
      ∀ x : Copy, copyLocation (state row.1) x ≠ .node v := by
  have hm := fun x => nodeRows_movement N H common v s row hrow x
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro x
    exact (node_move_preserves_after_exits N C hv (hs.1 x) (hs.2 x) (hm x)).1
  · intro x
    exact (node_move_preserves_after_exits N C hv (hs.1 x) (hs.2 x) (hm x)).2
  · intro x
    exact node_move_removes_node N (hm x)

#print axioms nodeRows_movement
#print axioms exitRows_ready
#print axioms nodeRows_after_exits
end GProgram.G7.RawBoundaryLocations
