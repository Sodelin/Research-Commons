import Astra.PhysicalSpliceRates
import Astra.PhysicalSpliceRegistry

/-! Proposed, uncompiled coordinate frame for an eligible actual splice.
The external label types and original maps are inputs. New maps are constructed;
no output law, reduced target, closed dependency footprint or size bound is an
input or conclusion. Fully expanded dependency eligibility remains separate. -/
namespace Astra.PhysicalSpliceProtectedCoordinates

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.NativeCommonPairGerm
open G1ActualTwoPortBlob G1BigonSpliceGraph G1SplicedSourceAdmission
open Astra.PhysicalSpliceRates Astra.PhysicalSpliceRegistry
open scoped Classical

variable {V E X PV PE PH : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def vertexMap (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (mark : PV → V)
    (avoid : ∀ a, mark a ≠ A.fragment.upper ∧ mark a ≠ A.fragment.parents.hybrid) :
    PV → SplicedVertex N b A := fun a => ⟨mark a, avoid a⟩

theorem vertexMap_injective (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (mark : PV → V)
    (avoid : ∀ a, mark a ≠ A.fragment.upper ∧ mark a ≠ A.fragment.parents.hybrid)
    (hinj : Function.Injective mark) : Function.Injective (vertexMap N b A mark avoid) := by
  intro a c h
  exact hinj (congrArg Subtype.val h)

theorem vertex_age (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (C : Calendar N.graph) (mark : PV → V)
    (avoid : ∀ a, mark a ≠ A.fragment.upper ∧ mark a ≠ A.fragment.parents.hybrid) (a : PV) :
    (splicedCalendar N hc b hb A C).age (vertexMap N b A mark avoid a) =
      C.age (mark a) := rfl

noncomputable def edgeMap (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (mark : PE → E)
    (avoid : ∀ a, mark a ∉ G1BigonFootprint.removedEdges N b A) :
    PE → SplicedEdge N b A := fun a => .inl ⟨mark a, avoid a⟩

/-- Raw occurrence projection; the synthetic edge has no old occurrence. -/
def originalEdge (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : SplicedEdge N b A → Option E
  | .inl e => some e.val
  | .inr _ => none

theorem edgeMap_original (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (mark : PE → E)
    (avoid : ∀ a, mark a ∉ G1BigonFootprint.removedEdges N b A) (a : PE) :
    originalEdge N b A (edgeMap N b A mark avoid a) = some (mark a) := rfl

theorem edgeMap_injective (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (mark : PE → E)
    (avoid : ∀ a, mark a ∉ G1BigonFootprint.removedEdges N b A)
    (hinj : Function.Injective mark) : Function.Injective (edgeMap N b A mark avoid) := by
  intro a c h
  exact hinj (congrArg Subtype.val (Sum.inl.inj h))

theorem edge_rate (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (C : Calendar N.graph) (r : PositivePairRates E)
    (mark : PE → E) (avoid : ∀ a, mark a ∉ G1BigonFootprint.removedEdges N b A) (a : PE) :
    (splicedRates N C r b A).edge (edgeMap N b A mark avoid a) = r.edge (mark a) := rfl

theorem edge_source_age (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (C : Calendar N.graph) (mark : PE → E)
    (avoid : ∀ a, mark a ∉ G1BigonFootprint.removedEdges N b A) (a : PE) :
    (splicedCalendar N hc b hb A C).age
        ((splicedNetwork N hc b hb A).graph.source (edgeMap N b A mark avoid a)) =
      C.age (N.graph.source (mark a)) := rfl

theorem edge_target_age (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (C : Calendar N.graph) (mark : PE → E)
    (avoid : ∀ a, mark a ∉ G1BigonFootprint.removedEdges N b A) (a : PE) :
    (splicedCalendar N hc b hb A C).age
        ((splicedNetwork N hc b hb A).graph.target (edgeMap N b A mark avoid a)) =
      C.age (N.graph.target (mark a)) := rfl

noncomputable def hybridMap (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mark : PH → Hybrid N) (avoid : ∀ a, mark a ≠ removedHybrid N b A) :
    PH → Hybrid (splicedNetwork N hc b hb A) :=
  fun a => survivingHybrid N hc b hb A (mark a) (avoid a)

theorem hybridMap_original (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mark : PH → Hybrid N) (avoid : ∀ a, mark a ≠ removedHybrid N b A) (a : PH) :
    retainedHybrid N hc b hb A (hybridMap N hc b hb A mark avoid a) = mark a :=
  retained_surviving_hybrid N hc b hb A (mark a) (avoid a)

theorem hybridMap_injective (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mark : PH → Hybrid N) (avoid : ∀ a, mark a ≠ removedHybrid N b A)
    (hinj : Function.Injective mark) :
    Function.Injective (hybridMap N hc b hb A mark avoid) := by
  intro a c h
  apply hinj
  have he := congrArg (retainedHybrid N hc b hb A) h
  simpa only [hybridMap_original] using he

theorem hybrid_gamma (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) (mark : PH → Hybrid N)
    (avoid : ∀ a, mark a ≠ removedHybrid N b A) (a : PH) :
    (splicedProbabilities N hc b hb A p).gamma (hybridMap N hc b hb A mark avoid a) =
      p.gamma (mark a) := by
  rw [splicedProbabilities_gamma, hybridMap_original]

theorem hybrid_parent_occurrence (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) (mark : PH → Hybrid N)
    (avoid : ∀ a, mark a ≠ removedHybrid N b A) (a : PH) (bit : Bool) :
    originalEdge N b A (((splicedRegistry N hc b hb A H).parents
        (hybridMap N hc b hb A mark avoid a)).parent bit) =
      some ((H.parents (mark a)).parent bit) := by
  rw [splicedRegistry_parent]
  simp only [originalEdge, retainedParent_val, hybridMap_original]

theorem hybrid_bank_bit (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mark : PH → Hybrid N) (avoid : ∀ a, mark a ≠ removedHybrid N b A)
    (coin : CommonSeed N) (a : PH) :
    restrictBank N hc b hb A coin (hybridMap N hc b hb A mark avoid a) = coin (mark a) := by
  change coin (retainedHybrid N hc b hb A (hybridMap N hc b hb A mark avoid a)) = _
  rw [hybridMap_original]

-- Unexecuted audit requests. Expanded dependency closure/count remains unproved.
#check vertexMap
#check edgeMap
#check hybridMap
#print axioms vertexMap_injective
#print axioms vertex_age
#print axioms edgeMap_original
#print axioms edgeMap_injective
#print axioms edge_rate
#print axioms edge_source_age
#print axioms edge_target_age
#print axioms hybridMap_original
#print axioms hybridMap_injective
#print axioms hybrid_gamma
#print axioms hybrid_parent_occurrence
#print axioms hybrid_bank_bit

end Astra.PhysicalSpliceProtectedCoordinates
