import G6OriginalSpliceAdapter
import G1DecoratedSpliceConstruction

/-!
Actual original population-ID boundary of the constructed decorated splice.
Cloud literature/organization structural lane, 8 October 2026, 03:34 UTC.
Compiler UNCHECKED; outside current176. Existing splice/word code is reused.

The common carrier has retained vertices, retained original edges and the
original root-population tag. The new spine is NOT a raw outside population.
These are injective carrier maps and calendar facts, not a Code/program/law
intertwining premise or a stochastic ordinary-spine replacement assertion.
-/

namespace UnifiedLean.G6.SpineBoundaryCarrier

open Nanuq.Source GProgram.SourceForest GProgram.G5
open G1ActualTwoPortBlob G1BigonSpliceGraph G1SplicedSourceAdmission
open UnifiedLean.G6.OriginalSpliceAdapter
open scoped Classical

/-- Constructor tags distinguish a node, an edge and the ancestral population.
Embedding their original IDs therefore gives an actual location embedding. -/
def locationEmbedding {V₁ V₂ E₁ E₂ : Type*} (f : V₁ ↪ V₂) (g : E₁ ↪ E₂) :
    Location V₁ E₁ ↪ Location V₂ E₂ where
  toFun
    | .node v => .node (f v)
    | .edge e => .edge (g e)
    | .rootPopulation v => .rootPopulation (f v)
  inj' a b h := by
    cases a with
    | node a =>
        cases b with
        | node b => exact congrArg Location.node (f.injective (Location.node.inj h))
        | edge b => cases h
        | rootPopulation b => cases h
    | edge a =>
        cases b with
        | node b => cases h
        | edge b => exact congrArg Location.edge (g.injective (Location.edge.inj h))
        | rootPopulation b => cases h
    | rootPopulation a =>
        cases b with
        | node b => cases h
        | edge b => cases h
        | rootPopulation b =>
            exact congrArg Location.rootPopulation (f.injective (Location.rootPopulation.inj h))

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- No private removed vertex/edge ID and no synthetic spine belongs to this
raw boundary carrier. Its genuine bigon is DERIVED from the incident count. -/
abbrev BoundaryLocation (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :=
  Location (SplicedVertex N b (derivedBigon N hcut b hb hp))
    (RetainedEdge N b (derivedBigon N hcut b hb hp))

/-- Into the actual original source: retain each underlying original ID. -/
noncomputable def intoOriginalBoundary (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    BoundaryLocation N hcut b hb hp ↪ Location V E :=
  locationEmbedding ⟨Subtype.val, Subtype.val_injective⟩
    ⟨Subtype.val, Subtype.val_injective⟩

/-- Into the constructed splice: raw retained edges use the .inl occurrence.
The .inr spine stores a separate original physical span, not a raw edge ID. -/
noncomputable def intoSplicedBoundary (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    BoundaryLocation N hcut b hb hp ↪
      Location (SplicedVertex N b (derivedBigon N hcut b hb hp))
        (SplicedEdge N b (derivedBigon N hcut b hb hp)) :=
  locationEmbedding (Function.Embedding.refl _) ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

theorem boundary_excludes_spine (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (q : BoundaryLocation N hcut b hb hp) :
    intoSplicedBoundary N hcut b hb hp q ≠ .edge (Sum.inr ()) := by
  cases q <;> simp [intoSplicedBoundary, locationEmbedding]

/-- Both graph embeddings use the derived endpoints of the SAME retained
original occurrence. This does not assert a full source boundary-kernel law. -/
theorem boundary_retained_endpoints (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (e : RetainedEdge N b (derivedBigon N hcut b hb hp)) :
    intoOriginalBoundary N hcut b hb hp
      (.node (retainedSource N hcut b (derivedBigon N hcut b hb hp) e)) =
        .node (N.graph.source e.val) ∧
    intoOriginalBoundary N hcut b hb hp
      (.node (retainedTarget N hcut b (derivedBigon N hcut b hb hp) e)) =
        .node (N.graph.target e.val) ∧
    intoSplicedBoundary N hcut b hb hp
      (.node (retainedSource N hcut b (derivedBigon N hcut b hb hp) e)) =
        .node ((suppressedNetwork N hcut b hb hp).graph.source (Sum.inl e)) ∧
    intoSplicedBoundary N hcut b hb hp
      (.node (retainedTarget N hcut b (derivedBigon N hcut b hb hp) e)) =
        .node ((suppressedNetwork N hcut b hb hp).graph.target (Sum.inl e)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem boundary_original_leaf (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) (x : X) :
    intoOriginalBoundary N hcut b hb hp
      (.node ((suppressedNetwork N hcut b hb hp).leaf x)) = .node (N.leaf x) := rfl

/-- The ancestral population keeps the actual original ROOT vertex tag. -/
theorem boundary_original_root_population (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    intoOriginalBoundary N hcut b hb hp
      (.rootPopulation (suppressedNetwork N hcut b hb hp).root) =
        .rootPopulation N.root := rfl

theorem boundary_retained_calendar (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (a : SplicedVertex N b (derivedBigon N hcut b hb hp)) :
    (splicedCalendar N hcut b hb (derivedBigon N hcut b hb hp) C).age a =
      C.age a.val := rfl

/-- The original word is child interval, two-arm interval, entry interval.
All three endpoint inequalities are DERIVED from the actual original edges.
A claim that the open interval contains no observation cut is separate. -/
theorem boundary_original_private_age_order (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) :
    let A := derivedBigon N hcut b hb hp
    C.age (N.graph.target A.child) < C.age A.fragment.parents.hybrid ∧
      C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
      C.age A.fragment.upper < C.age (N.graph.source A.entry) := by
  let A := derivedBigon N hcut b hb hp
  have hc := C.edge_older A.child
  rw [A.child_source] at hc
  have ha := C.edge_older A.fragment.parents.parent0
  rw [A.fragment.parents.target0,
    show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false] at ha
  have he := C.edge_older A.entry
  rw [A.entry_target] at he
  exact ⟨hc, ha, he⟩

#print axioms locationEmbedding
#print axioms intoOriginalBoundary
#print axioms intoSplicedBoundary
#print axioms boundary_excludes_spine
#print axioms boundary_retained_endpoints
#print axioms boundary_original_leaf
#print axioms boundary_original_root_population
#print axioms boundary_retained_calendar
#print axioms boundary_original_private_age_order

end UnifiedLean.G6.SpineBoundaryCarrier
