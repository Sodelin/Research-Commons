import G6GuardedEntrySupport
import G1OriginalDecoratedSpan

/-!
The actual original child population retained at a guarded read cut.
Cloud literature/organization structural lane, 8 October 2026, 04:41 UTC.
Original source/calendar/span providers: Dot. Compiler UNCHECKED; no change
to shared providers, workflows or any current compiler selection.

This is a finite PHASE LOCATION carrier on the original graph, not a new
RootedBinary source or a scalar-rate interpretation of a synthetic spine.
One support/physical-epoch body uses actual initialization, ALL tied original
node operations and the SAME original sourceTimeKernel. No law is assumed.
The upper endpoint of the protected child is still looked up in the original
graph; this location subtype is not an EdgeGraph on the retained vertices.
The interval endpoint is before any new guard-date boundary batch. Old tagged
history is a separate carrier, not reconstructed from the decoded Code.
-/

namespace UnifiedLean.G6.ProtectedChildCarrier

open Nanuq.Source GProgram.SourceForest GProgram.G5
open G1BigonSpliceGraph G1BigonFootprint G1NaturalCalendarNodes
open G1InitializedFrontierPrefix
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.G6.OriginalSpliceAdapter
open UnifiedLean.G6.SpineBoundaryCarrier
open UnifiedLean.G6.GuardedEntrySupport
open scoped Classical

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Outside ORIGINAL edge IDs plus the distinguished ORIGINAL child ID.
No newly inserted spine ID or guessed rate is admitted by this subtype. -/
abbrev ChildGuardedEdge (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :=
  {e : E // e ∉ removedEdges N b (derivedBigon N hcut b hb hp) ∨
    e = (derivedBigon N hcut b hb hp).child}

abbrev ChildGuardedLocation (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :=
  Location (SplicedVertex N b (derivedBigon N hcut b hb hp))
    (ChildGuardedEdge N hcut b hb hp)

/-- Both constructor tags and every original physical occurrence are kept. -/
noncomputable def intoOriginalChildGuarded (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    ChildGuardedLocation N hcut b hb hp ↪ Location V E :=
  locationEmbedding ⟨Subtype.val, Subtype.val_injective⟩
    ⟨Subtype.val, Subtype.val_injective⟩

/-- This is the actual old child occurrence. Its source/target dates and rate
are therefore C.age (N.graph.source/target child.val) and r.edge child.val. -/
noncomputable def protectedChild (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    ChildGuardedEdge N hcut b hb hp :=
  ⟨(derivedBigon N hcut b hb hp).child, Or.inr rfl⟩

/-- Actual initialized FULL-copy source support after the COMPLETE child-date
node batch, then a true calendar-gap interval ending below the private hybrid.
The entire original Code/register/forest is retained. The gap is an original
calendar constraint, not a support/kernel-equality premise. This supplies a
phase witness only, not a projected two-graph state or tagged-history law. -/
theorem actual_initialized_protected_child_phase (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (guard : ℝ)
    (hlower : C.age (N.graph.target (derivedBigon N hcut b hb hp).child) ≤ guard)
    (hupper : guard < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid)
    (hgap : ∀ v : V,
      C.age (N.graph.target (derivedBigon N hcut b hb hp).child) < C.age v →
        guard ≤ C.age v)
    {d z w : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common
        (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)))
      (initialCode N sample register)).support)
    (hz : z ∈ (sourceProgram N r
      ((Finset.univ.filter (fun v : V =>
        C.age v = C.age (N.graph.target (derivedBigon N hcut b hb hp).child))).toList.map
          (fun v => .boundary (originalNodeOperation N H gamma common v))) d).support)
    (hw : w ∈ (sourceTimeKernel N r
      (Real.toNNReal (guard - C.age (N.graph.target (derivedBigon N hcut b hb hp).child))) z).support) :
    EpochCompatible N C
      (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)) guard (state w) ∧
    C.Active guard (protectedChild N hcut b hb hp).val ∧
    guard < C.age (derivedBigon N hcut b hb hp).fragment.upper ∧
    (∀ x : Copy, ∃ q : ChildGuardedLocation N hcut b hb hp,
      intoOriginalChildGuarded N hcut b hb hp q = copyLocation (state w) x) := by
  let A := derivedBigon N hcut b hb hp
  let a := C.age (N.graph.target A.child)
  let vs := (Finset.univ.filter (fun v : V => C.age v = a)).toList
  have hfront := actual_initialized_frontier_support N C sample register H gamma common r
    (N.graph.target A.child) hd
  have hnat : NaturalState N C sample a (state d) :=
    ⟨hfront.2.1, fun x e he => (hfront.2.2 x e he).le⟩
  have hnz := actual_node_list_natural N C H gamma common r vs a (by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2) d hnat hz
  have haz := actual_node_batch_support N C H gamma common r a d hfront.1 hz
  have hepoch := actual_source_time_epoch_support N C r
    (Real.toNNReal (guard - a)) z (after_nodes_to_epoch N C haz hgap) hw
  have hnw := actual_time_natural N C r (Real.toNNReal (guard - a)) z a hnz hw
  have hage := boundary_original_private_age_order N hcut b hb hp C
  change a < C.age A.fragment.parents.hybrid ∧
    C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
    C.age A.fragment.upper < C.age (N.graph.source A.entry) at hage
  have hactive := removed_child_active_below_private_vertices N hcut b hb hp C guard hlower hupper
  refine ⟨hepoch, hactive.1, hactive.2, ?_⟩
  intro x
  cases hx : copyLocation (state w) x with
  | node v =>
      have hv : v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid := by
        rcases hnw.1 x v hx with hf | ht
        · rw [hf]
          exact actual_taxon_vertices_retained N b A (sample x)
        · constructor
          · intro heq
            rw [heq] at ht
            exact (not_le_of_gt (hage.1.trans hage.2.1)) ht
          · intro heq
            rw [heq] at ht
            exact (not_le_of_gt hage.1) ht
      exact ⟨.node ⟨v, hv⟩, rfl⟩
  | edge e =>
      have he : e ∉ removedEdges N b A ∨ e = A.child := by
        by_cases hchild : e = A.child
        · exact Or.inr hchild
        · refine Or.inl ?_
          intro hremoved
          have hor : e = A.entry ∨ e = A.child ∨
              e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
            simpa only [removedEdges, Finset.mem_insert, Finset.mem_singleton] using hremoved
          have ht := hnw.2 x e hx
          rcases hor with rfl | hchild' | rfl | rfl
          · rw [A.entry_target] at ht
            exact (not_le_of_gt (hage.1.trans hage.2.1)) ht
          · exact hchild hchild'
          · rw [A.fragment.parents.target0] at ht
            exact (not_le_of_gt hage.1) ht
          · rw [A.fragment.parents.target1] at ht
            exact (not_le_of_gt hage.1) ht
      exact ⟨.edge ⟨e, he⟩, rfl⟩
  | rootPopulation v =>
      have hr := hepoch x
      rw [hx] at hr
      change v = N.root ∧ C.age N.root ≤ a at hr
      have hv : v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid := by
        rw [hr.1]
        exact actual_root_vertex_retained N b hb A
      exact ⟨.rootPopulation ⟨v, hv⟩, rfl⟩

#print axioms intoOriginalChildGuarded
#print axioms protectedChild
#print axioms actual_initialized_protected_child_phase

end UnifiedLean.G6.ProtectedChildCarrier
