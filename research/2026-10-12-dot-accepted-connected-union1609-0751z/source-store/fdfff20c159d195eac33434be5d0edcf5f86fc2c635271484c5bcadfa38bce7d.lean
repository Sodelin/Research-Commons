import G7RawCalendarRoot
import G7BoundaryPhasePermutation

/-!
# Consume original phase permutations without choosing a new date agenda

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Literal exit and entry lists may have the same finite membership as the
inherited choice-based Finset.toList. The old source phase-Perm law transports
their physical PMFs. The pointwise complete phase invariants also cover every
raw trace, including polynomial-zero rows. These conclusions are kept separate:
physical same-bank equality does not assert an independent-slot polynomial cube.
Draft pending sole-scheduler kernel checking and complete owned audit.
-/
namespace GProgram.G7.CalendarPhaseConsumers
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open GProgram.G7.RawProgramLocations GProgram.G7.RawCalendarRoot
open GProgram.G7.BoundaryPhasePermutation
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

theorem exit_phase_trace_complete (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (a : ℝ) (es : List E)
    (he : es.Perm (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList)
    (s : Code N sample) (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : programTrace N (es.map (fun e => .boundary (.exit e))) s d) :
    AfterExits N C a (state d) := by
  have hh := exit_trace_list N C es [] (by
    intro e hm
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp (he.mem_iff.mp hm))).2)
    s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x e hp
  have hbound := hh.1 x
  rw [hp] at hbound
  have hne : C.age (N.graph.source e) ≠ a := by
    intro hage
    have hm : e ∈ es := he.mem_iff.mpr
      (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hage⟩))
    exact hh.2 x e (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound.2).resolve_right hne.symm

theorem node_phase_trace_complete (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) (vs : List V)
    (hv : vs.Perm (Finset.univ.filter (fun v : V => C.age v = a)).toList)
    (s : Code N sample) (hs : AfterExits N C a (state s)) {d : Code N sample}
    (hd : programTrace N (vs.map (fun v =>
      .boundary (originalNodeOperation N H gamma common v))) s d) :
    AfterNodes N C a (state d) := by
  have hh := node_trace_list N C H gamma common vs [] (by
    intro v hm
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp (hv.mem_iff.mp hm))).2)
    s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x v hp
  have hbound := hh.1.1 x
  rw [hp] at hbound
  have hne : C.age v ≠ a := by
    intro hage
    have hm : v ∈ vs := hv.mem_iff.mpr
      (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hage⟩))
    exact hh.2 x v (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound).resolve_right hne.symm

/-- The structural complete phase conclusion is independent of coefficient
positivity and independent of the original choice-based tie order. -/
theorem boundary_phase_trace_complete (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) (es : List E) (vs : List V)
    (he : es.Perm (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList)
    (hv : vs.Perm (Finset.univ.filter (fun v : V => C.age v = a)).toList)
    (s : Code N sample) (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : programTrace N ((es.map (fun e => .boundary (.exit e))) ++
      (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v)))) s d) :
    AfterNodes N C a (state d) := by
  rw [programTrace_append] at hd
  obtain ⟨m,hm,hdm⟩ := hd
  exact node_phase_trace_complete N C H gamma common a vs hv m
    (exit_phase_trace_complete N C a es he s hs hm) hdm

/-- Reuse the old physical phase permutation theorem. Exits remain before
entries, and the original registry/rate/gamma/mode bank is shared. -/
theorem actual_boundary_phase_program (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ)
    (es : List E) (vs : List V)
    (he : es.Perm (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList)
    (hv : vs.Perm (Finset.univ.filter (fun v : V => C.age v = a)).toList)
    (s : Code N sample) :
    sourceProgram N r ((es.map (fun e => .boundary (.exit e))) ++
      (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v)))) s =
      sourceProgram N r (boundaryOperations N C H gamma common a) s := by
  rw [boundaryOperations,program_append,program_append,exit_phase_perm N r he s]
  congr 1
  funext m
  exact node_phase_perm N r H gamma common hv m

#print axioms exit_phase_trace_complete
#print axioms node_phase_trace_complete
#print axioms boundary_phase_trace_complete
#print axioms actual_boundary_phase_program
end GProgram.G7.CalendarPhaseConsumers
