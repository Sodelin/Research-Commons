import G6SpineBoundaryCarrier
import G1InitializedFrontierPrefix

/-!
Actual initialized lower-interface support, and its exact phase boundary.
Cloud literature/organization structural lane, 8 October 2026, 04:28 UTC.
Original calendar/source providers are attributed to Dot. Compiler UNCHECKED;
outside the current compiler selection. No provider or workflow is changed.

At the child interface AFTER exits / BEFORE its node batch, every copy's
actual current location has a witness in the common retained raw carrier.
The original node kernel then sends its actual descendants into the removed
child edge. Strictly older private vertices therefore do not justify raw
carrier support throughout a guarded prefix that crosses this entry date.
These theorems neither construct a reduced Code nor equate source kernels.
-/

namespace UnifiedLean.G6.GuardedEntrySupport

open Nanuq.Source GProgram.SourceForest GProgram.G5
open G1BigonSpliceGraph G1BigonFootprint G1ExtractedComponentProgram
open G1NaturalCalendarNodes G1InitializedFrontierPrefix
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.G6.OriginalSpliceAdapter
open UnifiedLean.G6.SpineBoundaryCarrier
open scoped Classical

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- The premises are inherited physical/natural invariants, not a desired
cross-graph support field. The next theorem derives them from initialization. -/
theorem natural_child_frontier_in_raw_boundary (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) {sample : Copy → X} (s : Code N sample)
    (hphysical : AfterExits N C
      (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)) (state s))
    (hnatural : NaturalNodes N C sample
      (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)) (state s))
    (hentered : StrictEnteredEdges N C
      (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)) (state s)) :
    ∀ x : Copy, ∃ q : BoundaryLocation N hcut b hb hp,
      intoOriginalBoundary N hcut b hb hp q = copyLocation (state s) x := by
  let A := derivedBigon N hcut b hb hp
  have hage := boundary_original_private_age_order N hcut b hb hp C
  change C.age (N.graph.target A.child) < C.age A.fragment.parents.hybrid ∧
    C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
    C.age A.fragment.upper < C.age (N.graph.source A.entry) at hage
  intro x
  cases hx : copyLocation (state s) x with
  | node z =>
      have hz : z ≠ A.fragment.upper ∧ z ≠ A.fragment.parents.hybrid := by
        rcases hnatural x z hx with hf | ht
        · rw [hf]
          exact actual_taxon_vertices_retained N b A (sample x)
        · constructor
          · intro heq
            rw [heq] at ht
            exact (not_le_of_gt (hage.1.trans hage.2.1)) ht
          · intro heq
            rw [heq] at ht
            exact (not_le_of_gt hage.1) ht
      exact ⟨.node ⟨z, hz⟩, rfl⟩
  | edge e =>
      have ht := hentered x e hx
      have he : e ∉ removedEdges N b A := by
        intro hremoved
        have hor : e = A.entry ∨ e = A.child ∨
            e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
          simpa only [removedEdges, Finset.mem_insert, Finset.mem_singleton] using hremoved
        rcases hor with rfl | rfl | rfl | rfl
        · rw [A.entry_target] at ht
          exact (not_lt_of_ge (hage.1.trans hage.2.1).le) ht
        · exact (lt_irrefl _) ht
        · rw [A.fragment.parents.target0] at ht
          exact (not_lt_of_ge hage.1.le) ht
        · rw [A.fragment.parents.target1] at ht
          exact (not_lt_of_ge hage.1.le) ht
      exact ⟨.edge ⟨e, he⟩, rfl⟩
  | rootPopulation z =>
      have hr := hphysical.1 x
      rw [hx] at hr
      change z = N.root ∧ C.age N.root ≤ C.age (N.graph.target A.child) at hr
      have hz : z ≠ A.fragment.upper ∧ z ≠ A.fragment.parents.hybrid := by
        rw [hr.1]
        exact actual_root_vertex_retained N b hb A
      exact ⟨.rootPopulation ⟨z, hz⟩, rfl⟩

/-- Every supported FULL-copy initialized source endpoint, for every original
register assignment, is in the shared raw carrier at this exact BEFORE-node
phase. Full forests/registers are not projected, reset or refitted here. -/
theorem actual_initialized_child_frontier_in_raw_boundary (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common
        (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)))
      (initialCode N sample register)).support) :
    ∀ x : Copy, ∃ q : BoundaryLocation N hcut b hb hp,
      intoOriginalBoundary N hcut b hb hp q = copyLocation (state d) x := by
  have h := actual_initialized_frontier_support N C sample register H gamma common r
    (N.graph.target (derivedBigon N hcut b hb hp).child) hd
  exact natural_child_frontier_in_raw_boundary N hcut b hb hp C d h.1 h.2.1 h.2.2

/-- The child's original population ID is genuinely removed from the raw
carrier; storing its original span on a synthetic spine is a separate recipe. -/
theorem removed_child_not_in_raw_boundary (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    ¬ ∃ q : BoundaryLocation N hcut b hb hp,
      intoOriginalBoundary N hcut b hb hp q =
        .edge (derivedBigon N hcut b hb hp).child := by
  let A := derivedBigon N hcut b hb hp
  rintro ⟨q, hq⟩
  cases q with
  | node z =>
      change Location.node z.val = Location.edge A.child at hq
      cases hq
  | edge e =>
      change Location.edge e.val = Location.edge A.child at hq
      have he := Location.edge.inj hq
      apply e.property
      rw [he]
      simp [removedEdges]
  | rootPopulation z =>
      change Location.rootPopulation z.val = Location.edge A.child at hq
      cases hq

/-- A lower guard can lie below BOTH private vertices while the removed
original child population is physically active at that very guard. -/
theorem removed_child_active_below_private_vertices (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (guard : ℝ)
    (hlower : C.age (N.graph.target (derivedBigon N hcut b hb hp).child) ≤ guard)
    (hupper : guard < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid) :
    C.Active guard (derivedBigon N hcut b hb hp).child ∧
      guard < C.age (derivedBigon N hcut b hb hp).fragment.upper := by
  let A := derivedBigon N hcut b hb hp
  have hage := boundary_original_private_age_order N hcut b hb hp C
  change C.age (N.graph.target A.child) < C.age A.fragment.parents.hybrid ∧
    C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
    C.age A.fragment.upper < C.age (N.graph.source A.entry) at hage
  refine ⟨⟨hlower, ?_⟩, hupper.trans hage.2.1⟩
  rw [A.child_source]
  exact hupper

/-- This obstruction is a derived ACTUAL node-kernel destination. A copy
descended from the child interface in the genuine initialized prefix enters
the removed child edge at that node, for every positive-mass destination.
No arbitrary desired location law or fabricated Code is supplied. -/
theorem actual_child_node_enters_removed_population (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {d z : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common
        (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)))
      (initialCode N sample register)).support)
    (hz : z ∈ (boundaryKernel N
      (originalNodeOperation N H gamma common
        (N.graph.target (derivedBigon N hcut b hb hp).child)) d).support)
    (x : Copy)
    (hdesc : N.graph.DReach
      (N.graph.target (derivedBigon N hcut b hb hp).child) (N.leaf (sample x))) :
    copyLocation (state z) x = .edge (derivedBigon N hcut b hb hp).child ∧
      ¬ ∃ q : BoundaryLocation N hcut b hb hp,
        intoOriginalBoundary N hcut b hb hp q = copyLocation (state z) x := by
  let A := derivedBigon N hcut b hb hp
  have hcopy : copyLocation (state d) x = .node (N.graph.target A.child) :=
    ((actual_initialized_cut_frontier N C sample register H gamma common r
      A.child A.child_bridge hd).1 x).mp hdesc
  have hm := actual_original_node_kernel_movement N H gamma common
    (N.graph.target A.child) d hz x
  unfold NodeMovement at hm
  rw [hcopy, if_pos rfl, if_neg (N.edge_target_ne_root A.child)] at hm
  obtain ⟨e, ht, hnew⟩ := hm
  obtain ⟨f, _, hf⟩ := N.incoming_unique_of_indegree_one (extracted_child_ordinary N b A)
  have he : e = A.child := (hf e ht).trans (hf A.child rfl).symm
  rw [he] at hnew
  refine ⟨hnew, ?_⟩
  rw [hnew]
  exact removed_child_not_in_raw_boundary N hcut b hb hp

#print axioms natural_child_frontier_in_raw_boundary
#print axioms actual_initialized_child_frontier_in_raw_boundary
#print axioms removed_child_not_in_raw_boundary
#print axioms removed_child_active_below_private_vertices
#print axioms actual_child_node_enters_removed_population

end UnifiedLean.G6.GuardedEntrySupport
