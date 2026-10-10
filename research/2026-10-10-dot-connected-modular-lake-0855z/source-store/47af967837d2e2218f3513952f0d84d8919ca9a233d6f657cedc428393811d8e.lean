import BlobIncidentPorts
import G1SplicedSourceAdmission

/-!
Thin G6 consumer of Dot's existing actual G1 splice constructor.
Cloud literature/organization structural lane, 8 October 2026, 03:04 UTC.
Compiler UNCHECKED; outside actual166/proposed176. No splice code rebuilt.

The only new carrier bridge is the occurrence-preserving equivalence from
Cloud IncidentPorts to original G1 allPorts. The existing extractedBigon,
splice graph, source admission and incident-fibre degree proofs stay unchanged.
RootedBinary is a derived constructor OUTPUT, never a supplied replacement
field. No Q/S, parameter, history, kernel or full G6 equality is asserted.
-/

namespace UnifiedLean.G6.OriginalSpliceAdapter

open Nanuq.Source
open G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1SplicedSourceAdmission G1SpliceDegrees
open scoped Classical

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Original G1's premise is literally the explicit original child-cut contract. -/
theorem cutChild_iff (N : RootedBinary V E X) :
    CutChild N ↔ ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e := Iff.rfl

/-- Both carriers count the SAME individual original incident bridge IDs. -/
noncomputable def originalPortEquiv (N : RootedBinary V E X) (b : N.graph.Blob) :
    BlobIncidentPorts.IncidentPorts N b ≃ (allPorts N b) where
  toFun p := by
    refine ⟨p.val, ?_⟩
    rcases p.property.2 with ht | hs
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p.property.1, ht⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p.property.1, hs⟩))
  invFun p := by
    refine ⟨p.val, ?_⟩
    rcases Finset.mem_union.mp p.property with hs | ht
    · have he := (Finset.mem_filter.mp hs).2
      exact ⟨he.1, Or.inr he.2⟩
    · have he := (Finset.mem_filter.mp ht).2
      exact ⟨he.1, Or.inl he.2⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl

theorem original_port_card (N : RootedBinary V E X) (b : N.graph.Blob) :
    (allPorts N b).card = Nat.card (BlobIncidentPorts.IncidentPorts N b) := by
  calc
    (allPorts N b).card = Nat.card (allPorts N b) := (Nat.card_eq_finsetCard _).symm
    _ = Nat.card (BlobIncidentPorts.IncidentPorts N b) :=
      (Nat.card_congr (originalPortEquiv N b)).symm

/-- Original G1 extraction derives ALL internal IDs and both exterior interfaces. -/
noncomputable def derivedBigon (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) : ActualBlobBigon N b :=
  extractedBigon N hcut b hb ((original_port_card N b).trans hp)

/-- Reuse the constructed admitted graph, with its derived degree/root/acyclic/LSA
fields. This is not an assumed desired reduced network. Its spine is decorated. -/
noncomputable def suppressedNetwork (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    RootedBinary (SplicedVertex N b (derivedBigon N hcut b hb hp))
      (SplicedEdge N b (derivedBigon N hcut b hb hp)) X :=
  splicedNetwork N hcut b hb (derivedBigon N hcut b hb hp)

theorem derived_external_vertices (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    let A := derivedBigon N hcut b hb hp
    (N.graph.source A.entry ≠ A.fragment.upper ∧
      N.graph.source A.entry ≠ A.fragment.parents.hybrid) ∧
    (N.graph.target A.child ≠ A.fragment.upper ∧
      N.graph.target A.child ≠ A.fragment.parents.hybrid) :=
  actual_external_interface_vertices N b (derivedBigon N hcut b hb hp)

theorem derived_interfaces_outside_blob (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    let A := derivedBigon N hcut b hb hp
    N.graph.blobOf (N.graph.source A.entry) ≠ b ∧
      N.graph.blobOf (N.graph.target A.child) ≠ b :=
  ⟨(derivedBigon N hcut b hb hp).entry_source_outside,
    (derivedBigon N hcut b hb hp).child_target_outside⟩

theorem suppressed_spine_endpoints (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    let A := derivedBigon N hcut b hb hp
    ((suppressedNetwork N hcut b hb hp).graph.source (Sum.inr ())).val =
      N.graph.source A.entry ∧
    ((suppressedNetwork N hcut b hb hp).graph.target (Sum.inr ())).val =
      N.graph.target A.child := ⟨rfl, rfl⟩

theorem suppressed_retained_endpoints (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (e : RetainedEdge N b (derivedBigon N hcut b hb hp)) :
    ((suppressedNetwork N hcut b hb hp).graph.source (Sum.inl e)).val =
      N.graph.source e.val ∧
    ((suppressedNetwork N hcut b hb hp).graph.target (Sum.inl e)).val =
      N.graph.target e.val := ⟨rfl, rfl⟩

/-- Every retained vertex has its actual original indegree and outdegree,
proved by original G1's incoming/outgoing OCCURRENCE bijections. -/
theorem suppressed_degrees (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (a : SplicedVertex N b (derivedBigon N hcut b hb hp)) :
    (suppressedNetwork N hcut b hb hp).graph.inDegree a = N.graph.inDegree a.val ∧
      (suppressedNetwork N hcut b hb hp).graph.outDegree a = N.graph.outDegree a.val :=
  ⟨actual_splice_indegree N hcut b (derivedBigon N hcut b hb hp) a,
    actual_splice_outdegree N hcut b (derivedBigon N hcut b hb hp) a⟩

#print axioms original_port_card
#print axioms derived_external_vertices
#print axioms derived_interfaces_outside_blob
#print axioms suppressed_spine_endpoints
#print axioms suppressed_retained_endpoints
#print axioms suppressed_degrees

end UnifiedLean.G6.OriginalSpliceAdapter
