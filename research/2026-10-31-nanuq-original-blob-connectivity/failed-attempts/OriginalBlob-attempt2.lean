import BridgeRetraction
import BinaryDegree
namespace Nanuq.RawBlock
open Nanuq.Source
variable {V E : Type*} (G : EdgeGraph V E)

def BlobVertex (b : G.Blob) := {v : V // G.blobOf v = b}
def BlobEdge (b : G.Blob) := {e : E // ¬ G.IsBridge e ∧ G.blobOf (G.source e) = b}
instance [Finite E] (b : G.Blob) : Finite (BlobEdge G b) := by
  unfold BlobEdge
  infer_instance

def originalBlob (b : G.Blob) : EdgeGraph (BlobVertex G b) (BlobEdge G b) where
  source e := ⟨G.source e.val,e.property.2⟩
  target e := ⟨G.target e.val,(Quotient.sound (G.nonbridge_sameBlob e.property.1)).symm.trans e.property.2⟩

/-- Lifts the actual original walk, not a switching or a chosen simple graph. -/
theorem blob_walk_lift (b : G.Blob) {keep : E → Prop} {a c : V}
    (h : G.UReach (fun e => ¬ G.IsBridge e ∧ keep e) a c) :
    ∀ ha : G.blobOf a = b, ∀ hc : G.blobOf c = b,
    (originalBlob G b).UReach (fun e => keep e.val) ⟨a,ha⟩ ⟨c,hc⟩ := by
  induction h with
  | refl => intro ha hc; exact .refl
  | @tail c d h hs ih =>
    intro ha hd
    obtain ⟨e,he,hi⟩ := hs
    have hcd : G.blobOf c = G.blobOf d :=
      Quotient.sound (G.ureach_single ⟨e,he.1,hi⟩)
    have hc := hcd.trans hd
    have hp := ih ha hc
    have hsrc : G.blobOf (G.source e) = b := by
      rcases hi with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact hs ▸ hc
      · exact hs ▸ hd
    apply hp.tail
    refine ⟨⟨e,he.1,hsrc⟩,he.2,?_⟩
    rcases hi with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨Subtype.ext hs,Subtype.ext ht⟩
    · exact Or.inr ⟨Subtype.ext hs,Subtype.ext ht⟩

theorem original_blob_connected (b : G.Blob) (a c : BlobVertex G b) :
    (originalBlob G b).UReach (fun _ => True) a c := by
  have h : G.SameBlob a.val c.val := Quotient.exact (a.property.trans c.property.symm)
  have hh := blob_walk_lift G b
    (G.ureach_mono (fun e he => ⟨he,True.intro⟩) h) a.property c.property
  exact hh

theorem original_blob_bridgeless [Fintype E] (b : G.Blob) (e : BlobEdge G b) :
    ¬ (originalBlob G b).IsBridge e := by
  apply EdgeGraph.not_bridge_of_detour
  have h := blob_walk_lift G b (internal_nonbridge_detour G e.property.1)
    e.property.2 ((originalBlob G b).target e).property
  exact (originalBlob G b).ureach_mono
    (fun f hf heq => hf (congrArg Subtype.val heq)) h

theorem original_blob_incidence_bound [Fintype E]
    (hd : ∀ v, Set.ncard {e | G.source e = v ∨ G.target e = v} ≤ 3)
    (b : G.Blob) (v : BlobVertex G b) :
    Set.ncard {e | (originalBlob G b).source e = v ∨ (originalBlob G b).target e = v} ≤ 3 := by
  let S : Set (BlobEdge G b) := {e | (originalBlob G b).source e = v ∨ (originalBlob G b).target e = v}
  have hsub : Subtype.val '' S ⊆ {e | G.source e = v.val ∨ G.target e = v.val} := by
    rintro e ⟨f,hf,rfl⟩
    rcases hf with hs | ht
    · exact Or.inl (congrArg Subtype.val hs)
    · exact Or.inr (congrArg Subtype.val ht)
  have hh := Set.ncard_le_ncard hsub
  have hcard : ((fun e : BlobEdge G b => (e.val : E)) '' S).ncard = S.ncard :=
    Set.ncard_image_of_injective S (fun _ _ h => Subtype.ext h)
  rw [hcard] at hh
  exact hh.trans (hd v.val)

/-- Actual unswitched source blob: vertex deletion remains connected.
This does not yet assert supplier IsTwoConnected, which also needs ≥3 vertices. -/
theorem original_blob_delete_vertex_connected [Fintype E]
    (hd : ∀ v, Set.ncard {e | G.source e = v ∨ G.target e = v} ≤ 3)
    (b : G.Blob) {v a c : BlobVertex G b} (ha : a ≠ v) (hc : c ≠ v) :
    (originalBlob G b).UReach (Avoid (originalBlob G b) v) a c := by
  classical
  letI : Fintype (BlobEdge G b) := Fintype.ofFinite _
  exact delete_vertex_connected (originalBlob G b)
    (original_blob_connected G b) (original_blob_bridgeless G b)
    (original_blob_incidence_bound G hd b) ha hc

#print axioms original_blob_bridgeless
#print axioms original_blob_delete_vertex_connected
end Nanuq.RawBlock
