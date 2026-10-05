import guards.NanuqActualSelectedBlobGraph

set_option debug.skipKernelTC false

/-! Literal local choices on original internal edge occurrences and their
restriction/extension. Every local hybrid choice extends to an actual original
source switching; fixed exterior choices are kept only outside this blob.
This does not yet construct the capped graph's quartet readout or anchor sum. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

abbrev OriginalBlobArc (b : N.graph.Blob) :=
  {e : E // N.graph.blobOf (N.graph.source e) = b ∧
    N.graph.blobOf (N.graph.target e) = b}

@[ext] structure OriginalBlobSwitching (b : N.graph.Blob) where
  keep : N.OriginalBlobArc b → Prop
  ordinary : ∀ e, ¬ N.graph.IsHybrid (N.graph.target e.val) → keep e
  hybrid_unique : ∀ a : N.OriginalBlobVertex b, N.graph.IsHybrid a.val →
    ∃ e : N.OriginalBlobArc b, N.graph.target e.val = a.val ∧ keep e ∧
      ∀ f : N.OriginalBlobArc b, N.graph.target f.val = a.val → keep f → f = e

theorem original_hybrid_arc_internal (b : N.graph.Blob) (e : E)
    (ht : N.graph.blobOf (N.graph.target e) = b)
    (hh : N.graph.IsHybrid (N.graph.target e)) :
    N.graph.blobOf (N.graph.source e) = b ∧ N.graph.blobOf (N.graph.target e) = b := by
  have hn := GProgram.G6.BridgeEntry.incoming_hybrid_edge_not_bridge N hh
  have hs : N.graph.blobOf (N.graph.source e) = N.graph.blobOf (N.graph.target e) :=
    Quotient.sound (N.graph.nonbridge_sameBlob hn)
  exact ⟨hs.trans ht,ht⟩

namespace Switching
variable {N} (S : N.Switching)

def restrictOriginalBlobSwitching (b : N.graph.Blob) : N.OriginalBlobSwitching b where
  keep e := S.keep e.val
  ordinary e hh := S.ordinary e.val hh
  hybrid_unique a hh := by
    obtain ⟨e, he, hk, hu⟩ := S.hybrid_unique a.val hh
    have he0 : N.graph.blobOf (N.graph.source e) = b ∧
        N.graph.blobOf (N.graph.target e) = b :=
      N.original_hybrid_arc_internal b e (by rw [he]; exact a.property) (by rw [he]; exact hh)
    exact ⟨⟨e,he0⟩,he,hk,fun f hf hkf => Subtype.ext (hu f.val hf hkf)⟩
end Switching

namespace OriginalBlobSwitching
variable {N} {b : N.graph.Blob} (L : N.OriginalBlobSwitching b)

noncomputable def extendOriginalBlobSwitching (S0 : N.Switching) : N.Switching := by
  let keep : E → Prop := fun e =>
    if he : N.graph.blobOf (N.graph.source e) = b ∧
        N.graph.blobOf (N.graph.target e) = b then L.keep ⟨e,he⟩ else S0.keep e
  refine ⟨keep, ?_, ?_⟩
  · intro e hh
    dsimp only [keep]
    split
    · exact L.ordinary _ hh
    · exact S0.ordinary e hh
  · intro a hh
    by_cases hb : N.graph.blobOf a = b
    · obtain ⟨e, he, hk, hu⟩ := L.hybrid_unique ⟨a,hb⟩ hh
      refine ⟨e.val, he, ?_, ?_⟩
      · simpa only [keep, dif_pos e.property] using hk
      · intro f hf hkf
        have hf0 : N.graph.blobOf (N.graph.source f) = b ∧
            N.graph.blobOf (N.graph.target f) = b :=
          N.original_hybrid_arc_internal b f (by rw [hf]; exact hb) (by rw [hf]; exact hh)
        have hkf0 : L.keep ⟨f,hf0⟩ := by simpa only [keep, dif_pos hf0] using hkf
        exact congrArg Subtype.val (hu ⟨f,hf0⟩ hf hkf0)
    · have hnot (f : E) (hf : N.graph.target f = a) :
          ¬ (N.graph.blobOf (N.graph.source f) = b ∧
            N.graph.blobOf (N.graph.target f) = b) := by
        intro h
        apply hb
        rw [← hf]
        exact h.2
      obtain ⟨e, he, hk, hu⟩ := S0.hybrid_unique a hh
      refine ⟨e,he,?_,?_⟩
      · simpa only [keep, dif_neg (hnot e he)] using hk
      · intro f hf hkf
        exact hu f hf (by simpa only [keep, dif_neg (hnot f hf)] using hkf)

@[simp] theorem restriction_extension_keep (S0 : N.Switching) (e : N.OriginalBlobArc b) :
    ((L.extendOriginalBlobSwitching S0).restrictOriginalBlobSwitching b).keep e = L.keep e := by
  simp only [extendOriginalBlobSwitching, Switching.restrictOriginalBlobSwitching, dif_pos e.property]

theorem restriction_extension_roundtrip (S0 : N.Switching) :
    (L.extendOriginalBlobSwitching S0).restrictOriginalBlobSwitching b = L := by
  apply OriginalBlobSwitching.ext
  funext e
  exact L.restriction_extension_keep S0 e
end OriginalBlobSwitching

theorem actual_blob_switching_restriction_surjective (b : N.graph.Blob) :
    Function.Surjective (fun S : N.Switching => S.restrictOriginalBlobSwitching b) := by
  intro L
  let S0 : N.Switching := Classical.choice inferInstance
  exact ⟨L.extendOriginalBlobSwitching S0,L.restriction_extension_roundtrip S0⟩
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.OriginalBlobSwitching.restriction_extension_roundtrip
#print axioms Nanuq.Source.RootedBinary.actual_blob_switching_restriction_surjective
