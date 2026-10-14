import Astra.ProtectedPhysicalIteration
import G1ActualTwoPortBlob
import G1BigonFootprint

/-!
Source-only incidence charging for actual external primitive labels.
Both endpoints of each marked edge are included. This finite label expression
has not been identified with the accepted expanded-protection parameter h.
The conclusion supplies local avoidance only, not equal arm exposure.
-/
namespace Astra.ProtectedBlobIncidence

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source G1ActualTwoPortBlob G1BigonFootprint
open Astra.PhysicalCommonStep Astra.PhysicalSpliceRegistry
open Astra.ProtectedPhysicalIteration
open scoped Classical

universe u v w a b c

variable {X : Type w} [Fintype X]
variable {PV : Type a} {PE : Type b} {PH : Type c}
variable [Fintype PV] [Fintype PE] [Fintype PH]

/-- Four literal incidence kinds. The two PE copies refer respectively to
the original source and target of the same marked edge occurrence. -/
def incidenceBlob (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    PV ⊕ (PE ⊕ (PE ⊕ PH)) → S.physical.source.network.graph.Blob
  | .inl z => S.physical.source.network.graph.blobOf (S.vertices z)
  | .inr (.inl z) => S.physical.source.network.graph.blobOf
      (S.physical.source.network.graph.source (S.edges z))
  | .inr (.inr (.inl z)) => S.physical.source.network.graph.blobOf
      (S.physical.source.network.graph.target (S.edges z))
  | .inr (.inr (.inr z)) => S.physical.source.network.graph.blobOf (S.hybrids z).val

/-- An image set, so repeated labels incident with one blob charge it once. -/
noncomputable def blockerBlobs (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    Finset S.physical.source.network.graph.Blob :=
  Finset.univ.image (incidenceBlob S)

theorem blockerBlobs_card_le (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    (blockerBlobs S).card ≤ Fintype.card PV + 2 * Fintype.card PE + Fintype.card PH := by
  calc
    (blockerBlobs S).card ≤
        (Finset.univ : Finset (PV ⊕ (PE ⊕ (PE ⊕ PH)))).card :=
      Finset.card_image_le
    _ = Fintype.card PV + 2 * Fintype.card PE + Fintype.card PH := by
      simp only [Finset.card_univ, Fintype.card_sum]
      omega

lemma vertex_blob_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (z : PV) :
    S.physical.source.network.graph.blobOf (S.vertices z) ∈ blockerBlobs S :=
  Finset.mem_image.mpr ⟨.inl z, Finset.mem_univ _, rfl⟩

lemma edge_source_blob_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (z : PE) :
    S.physical.source.network.graph.blobOf
      (S.physical.source.network.graph.source (S.edges z)) ∈ blockerBlobs S :=
  Finset.mem_image.mpr ⟨.inr (.inl z), Finset.mem_univ _, rfl⟩

lemma edge_target_blob_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (z : PE) :
    S.physical.source.network.graph.blobOf
      (S.physical.source.network.graph.target (S.edges z)) ∈ blockerBlobs S :=
  Finset.mem_image.mpr ⟨.inr (.inr (.inl z)), Finset.mem_univ _, rfl⟩

lemma hybrid_blob_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (z : PH) :
    S.physical.source.network.graph.blobOf (S.hybrids z).val ∈ blockerBlobs S :=
  Finset.mem_image.mpr ⟨.inr (.inr (.inr z)), Finset.mem_univ _, rfl⟩

/-- Exact membership characterizes all four incidence kinds; there are no
additional protected, controlled or dependency-generated blobs hidden here. -/
theorem mem_blockerBlobs_iff (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob) :
    b ∈ blockerBlobs S ↔
      (∃ z, S.physical.source.network.graph.blobOf (S.vertices z) = b) ∨
      (∃ z, S.physical.source.network.graph.blobOf
        (S.physical.source.network.graph.source (S.edges z)) = b) ∨
      (∃ z, S.physical.source.network.graph.blobOf
        (S.physical.source.network.graph.target (S.edges z)) = b) ∨
      (∃ z, S.physical.source.network.graph.blobOf (S.hybrids z).val = b) := by
  constructor
  · intro hb
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hb
    rcases z with z | z
    · exact Or.inl ⟨z, hz⟩
    rcases z with z | z
    · exact Or.inr (Or.inl ⟨z, hz⟩)
    rcases z with z | z
    · exact Or.inr (Or.inr (Or.inl ⟨z, hz⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨z, hz⟩))
  · rintro (⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩)
    · exact hz ▸ vertex_blob_mem S z
    · exact hz ▸ edge_source_blob_mem S z
    · exact hz ▸ edge_target_blob_mem S z
    · exact hz ▸ hybrid_blob_mem S z

lemma vertex_blob_ne (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob) (hb : b ∉ blockerBlobs S) (z : PV) :
    S.physical.source.network.graph.blobOf (S.vertices z) ≠ b := by
  intro he
  exact hb (he ▸ vertex_blob_mem S z)

lemma edge_source_blob_ne (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob) (hb : b ∉ blockerBlobs S) (z : PE) :
    S.physical.source.network.graph.blobOf
      (S.physical.source.network.graph.source (S.edges z)) ≠ b := by
  intro he
  exact hb (he ▸ edge_source_blob_mem S z)

lemma edge_target_blob_ne (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob) (hb : b ∉ blockerBlobs S) (z : PE) :
    S.physical.source.network.graph.blobOf
      (S.physical.source.network.graph.target (S.edges z)) ≠ b := by
  intro he
  exact hb (he ▸ edge_target_blob_mem S z)

lemma hybrid_blob_ne (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob) (hb : b ∉ blockerBlobs S) (z : PH) :
    S.physical.source.network.graph.blobOf (S.hybrids z).val ≠ b := by
  intro he
  exact hb (he ▸ hybrid_blob_mem S z)

theorem vertex_avoid_of_not_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob)
    (A : ActualBlobBigon S.physical.source.network b) (hb : b ∉ blockerBlobs S) :
    ∀ z, S.vertices z ≠ A.fragment.upper ∧ S.vertices z ≠ A.fragment.parents.hybrid := by
  intro z
  constructor
  · intro he
    exact vertex_blob_ne S b hb z
      ((congrArg S.physical.source.network.graph.blobOf he).trans A.upper_in_blob)
  · intro he
    exact vertex_blob_ne S b hb z
      ((congrArg S.physical.source.network.graph.blobOf he).trans A.hybrid_in_blob)

/-- The entry is blocked at its target, the child at its source, and each
ordered parent occurrence at its hybrid target. No occurrence is identified
with another and no external interface endpoint is discarded. -/
theorem edge_avoid_of_not_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob)
    (A : ActualBlobBigon S.physical.source.network b) (hb : b ∉ blockerBlobs S) :
    ∀ z, S.edges z ∉ removedEdges S.physical.source.network b A := by
  intro z hm
  have hm' : S.edges z = A.entry ∨ S.edges z = A.child ∨
      S.edges z = A.fragment.parents.parent0 ∨ S.edges z = A.fragment.parents.parent1 := by
    simpa only [removedEdges, Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hm' with he | he | he | he
  · apply edge_target_blob_ne S b hb z
    rw [he, A.entry_target]
    exact A.upper_in_blob
  · apply edge_source_blob_ne S b hb z
    rw [he, A.child_source]
    exact A.hybrid_in_blob
  · apply edge_target_blob_ne S b hb z
    rw [he, A.fragment.parents.target0]
    exact A.hybrid_in_blob
  · apply edge_target_blob_ne S b hb z
    rw [he, A.fragment.parents.target1]
    exact A.hybrid_in_blob

theorem hybrid_avoid_of_not_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob)
    (A : ActualBlobBigon S.physical.source.network b) (hb : b ∉ blockerBlobs S) :
    ∀ z, S.hybrids z ≠ removedHybrid S.physical.source.network b A := by
  intro z he
  have hv : (S.hybrids z).val = A.fragment.parents.hybrid := congrArg Subtype.val he
  exact hybrid_blob_ne S b hb z
    ((congrArg S.physical.source.network.graph.blobOf hv).trans A.hybrid_in_blob)

/-- Exactly the three avoidance fields of the existing EligibleCell on its
actual stepBigon. EqualArmExposure is deliberately absent from the conclusion:
being outside the marked incidence set does not establish that scalar fact. -/
theorem local_avoidance_of_not_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (b : S.physical.source.network.graph.Blob)
    (hroot : b ≠ S.physical.source.network.graph.blobOf S.physical.source.network.root)
    (hports : Fintype.card (S.physical.source.network.BlobPort b) = 2)
    (hb : b ∉ blockerBlobs S) :
    (∀ z, S.vertices z ≠ (stepBigon S.physical b hroot hports).fragment.upper ∧
      S.vertices z ≠ (stepBigon S.physical b hroot hports).fragment.parents.hybrid) ∧
    (∀ z, S.edges z ∉ removedEdges S.physical.source.network b
      (stepBigon S.physical b hroot hports)) ∧
    (∀ z, S.hybrids z ≠ removedHybrid S.physical.source.network b
      (stepBigon S.physical b hroot hports)) :=
  ⟨vertex_avoid_of_not_mem S b (stepBigon S.physical b hroot hports) hb,
    edge_avoid_of_not_mem S b (stepBigon S.physical b hroot hports) hb,
    hybrid_avoid_of_not_mem S b (stepBigon S.physical b hroot hports) hb⟩

#print axioms blockerBlobs_card_le
#print axioms mem_blockerBlobs_iff
#print axioms local_avoidance_of_not_mem

end Astra.ProtectedBlobIncidence
