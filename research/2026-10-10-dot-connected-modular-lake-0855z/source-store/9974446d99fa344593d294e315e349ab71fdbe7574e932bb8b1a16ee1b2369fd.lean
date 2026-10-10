import UnifiedLean.Source.SourceCalendarCompatibility
import UnifiedLean.Source.SourceProgramTransport
import UnifiedLean.Source.NativeParentRouting
import Mathlib.Data.Finset.Sort

/-!
# ORIGINAL graph/calendar compiler to concrete source operation programs

Contributor: dot, 2026-10-02. The agenda is constructed from sorted deduplicated
ORIGINAL vertex ages. All original edge exits at a boundary precede all node
entries/pulses at that boundary; parallel edge IDs are retained. Nonhybrid
nonroot entry indegree one is derived from the actual RootedBinary degrees.
Independent pulses use actual current live-owner PMFs and COMMON reuses the
original register. Physical location preservation through the full generated
agenda, exponential holding-clock path binding and final observation assembly
are still separate source obligations, not premises inserted into this compiler.
-/
namespace UnifiedLean.Source.SourceCalendarCompiler
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma nonhybrid_nonroot_indegree_one (N : RootedBinary V E X) (v : V)
    (hr : v ≠ N.root) (hh : ¬ N.graph.IsHybrid v) : N.graph.inDegree v = 1 := by
  by_cases ht : ∃ x : X, N.leaf x = v
  · obtain ⟨x,hx⟩ := ht
    rw [← hx]
    exact (N.leaf_degrees x).1
  · have htip : ∀ x : X, N.leaf x ≠ v := fun x hx => ht ⟨x,hx⟩
    rcases N.internal_degrees v hr htip with ht | hy
    · exact ht.1
    · exact False.elim (hh hy)

/-- Only source parameters are supplied: one original parent ordering per
actual hybrid, one Bernoulli parameter and one COMMON/independent flag. -/
noncomputable def originalNodeOperation (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) : BoundaryOperation N :=
  if hr : v = N.root then .root
  else if hh : N.graph.IsHybrid v then
    if common ⟨v,hh⟩ then .common (H.parents ⟨v,hh⟩)
    else .independent (H.parents ⟨v,hh⟩) (gamma ⟨v,hh⟩)
  else .ordinary ((defaultSelector N).edge ⟨v,hr⟩) (by
    rw [(defaultSelector N).target]
    exact nonhybrid_nonroot_indegree_one N v hr hh)

/-- The compiled node operation refers to the SAME original node and actual
incoming parent edges, with ordinary-entry legality derived from N's degrees. -/
theorem original_node_is_actual_operation (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) :
    (originalNodeOperation N H gamma common v = .root ∧ v = N.root) ∨
    (∃ hy : Hybrid N, hy.val = v ∧ (H.parents hy).hybrid = v ∧
      (originalNodeOperation N H gamma common v = .common (H.parents hy) ∨
       originalNodeOperation N H gamma common v = .independent (H.parents hy) (gamma hy))) ∨
    (∃ e : E, N.graph.target e = v ∧ ∃ hd : N.graph.inDegree (N.graph.target e) = 1,
      originalNodeOperation N H gamma common v = .ordinary e hd) := by
  by_cases hr : v = N.root
  · exact Or.inl ⟨by simp [originalNodeOperation,hr],hr⟩
  · by_cases hh : N.graph.IsHybrid v
    · refine Or.inr (Or.inl ⟨⟨v,hh⟩,rfl,H.original_site _,?_⟩)
      cases hc : common ⟨v,hh⟩ <;> simp [originalNodeOperation,hr,hh,hc]
    · refine Or.inr (Or.inr ⟨(defaultSelector N).edge ⟨v,hr⟩,
        (defaultSelector N).target _,by
          rw [(defaultSelector N).target]
          exact nonhybrid_nonroot_indegree_one N v hr hh,?_⟩)
      simp [originalNodeOperation,hr,hh]

noncomputable def sortedOriginalDates (N : RootedBinary V E X) (C : Calendar N.graph) : List ℝ :=
  (originalDates N C).sort (· ≤ ·)

noncomputable def boundaryOperations (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) : List (ProgramStep N) :=
  ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList.map
    (fun e => .boundary (.exit e))) ++
  ((Finset.univ.filter (fun v : V => C.age v = a)).toList.map
    (fun v => .boundary (originalNodeOperation N H gamma common v)))

noncomputable def calendarTail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) : ℝ → List ℝ → List (ProgramStep N)
  | _,[] => []
  | a,b::bs => .interval (Real.toNNReal (b-a)) ::
      (boundaryOperations N C H gamma common b ++ calendarTail N C H gamma common b bs)

noncomputable def compiledCalendarProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) : List (ProgramStep N) :=
  match sortedOriginalDates N C with
  | [] => []
  | a::as => boundaryOperations N C H gamma common a ++ calendarTail N C H gamma common a as

/-- Every ORIGINAL vertex date is represented; unrelated equal ages share one
boundary. Sorting creates no new source ages. -/
theorem original_date_scheduled (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) :
    C.age v ∈ sortedOriginalDates N C := by
  simp only [sortedOriginalDates,Finset.mem_sort]
  exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩

/-- Actual source chronology is nondecreasing and original dates are unique. -/
theorem original_dates_ordered (N : RootedBinary V E X) (C : Calendar N.graph) :
    (sortedOriginalDates N C).Pairwise (· ≤ ·) ∧ (sortedOriginalDates N C).Nodup := by
  exact ⟨Finset.pairwise_sort _ _,Finset.sort_nodup _ _⟩

/-- Constructed graph/calendar program has the already-proved whole selected
internal-state PMF law. Temporal location admission is not inferred merely
from this probability transport identity. -/
theorem compiled_original_program_projection (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) :
    (sourceProgram N r (compiledCalendarProgram N C H gamma common) s).map (projection N keep) =
      selectedProgram N r keep (compiledCalendarProgram N C H gamma common) (projection N keep s) :=
  actual_source_program_projection N r keep _ s

#print axioms nonhybrid_nonroot_indegree_one
#print axioms originalNodeOperation
#print axioms original_date_scheduled
#print axioms original_dates_ordered
#print axioms compiled_original_program_projection
end UnifiedLean.Source.SourceCalendarCompiler
