import TaggedSourceIteration
import Mathlib.Data.Quot
import Mathlib.Data.Finset.Image

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
EXPERIMENTAL SOURCE/HAND; all new bodies compiler UNCHECKED.
Only primitive coordinate bijections onto finite encoded images are inputs.
The full forest/register encoding and its injection are DERIVED. This is not
a serialized Python decoder, backend row equality or observed-panel injection.
-/
namespace CloudG6.FullJointCoordinateEncoding
open CloudG3.FiniteTagDecoder CloudG6.TaggedSourceIteration
open scoped Classical

variable {Copy Label Tag Bin Place Pop Vertex RegisterID : Type*}

/-- Relabel actual leaf/tag coordinates recursively; retain every graft. -/
def relabelTree (leaf : Copy → Label) (tag : Tag → Bin) :
    TaggedTree Copy Tag → TaggedTree Label Bin
  | .leaf x => .leaf (leaf x)
  | .graft t a b => .graft (tag t) (relabelTree leaf tag a) (relabelTree leaf tag b)

theorem relabelTree_respects (leaf : Copy → Label) (tag : Tag → Bin)
    {a b : TaggedTree Copy Tag} (h : TaggedEquiv a b) :
    TaggedEquiv (relabelTree leaf tag a) (relabelTree leaf tag b) := by
  induction h with
  | refl a => exact TaggedEquiv.refl _
  | symm _ ih => exact TaggedEquiv.symm ih
  | trans _ _ ih₁ ih₂ => exact TaggedEquiv.trans ih₁ ih₂
  | graft t _ _ ih₁ ih₂ => exact TaggedEquiv.graft (tag t) ih₁ ih₂
  | swap t a b => exact TaggedEquiv.swap (tag t) _ _

/-- Primitive injective string/Nat codes become bijections onto their images.
Those image carriers, rather than all strings or all naturals, are used here. -/
theorem relabelTree_inverse (leaf : Copy ≃ Label) (tag : Tag ≃ Bin)
    (a : TaggedTree Copy Tag) :
    relabelTree leaf.symm tag.symm (relabelTree leaf tag a) = a := by
  induction a with
  | leaf x => simp [relabelTree]
  | graft t a b ha hb => simp only [relabelTree, Equiv.symm_apply_apply, ha, hb]

noncomputable def relabelQuotient (leaf : Copy → Label) (tag : Tag → Bin) :
    Quotient (taggedTreeSetoid Copy Tag) → Quotient (taggedTreeSetoid Label Bin) :=
  Quotient.map' (relabelTree leaf tag) (fun _ _ h => relabelTree_respects leaf tag h)

theorem relabelQuotient_inverse (leaf : Copy ≃ Label) (tag : Tag ≃ Bin)
    (a : Quotient (taggedTreeSetoid Copy Tag)) :
    relabelQuotient leaf.symm tag.symm (relabelQuotient leaf tag a) = a := by
  refine Quotient.inductionOn a ?_
  intro tree
  change Quotient.mk (taggedTreeSetoid Copy Tag)
    (relabelTree leaf.symm tag.symm (relabelTree leaf tag tree)) =
      Quotient.mk (taggedTreeSetoid Copy Tag) tree
  rw [relabelTree_inverse]

theorem relabelQuotient_injective (leaf : Copy ≃ Label) (tag : Tag ≃ Bin) :
    Function.Injective (relabelQuotient leaf tag) :=
  Function.LeftInverse.injective (relabelQuotient_inverse leaf tag)

abbrev FullRecord (Place Vertex Copy Tag : Type*) :=
  (Place → Finset (Quotient (taggedTreeSetoid Copy Tag))) × (Vertex → Bool)

/-- Every original Location and every original register coordinate is kept.
The Bool is copied literally, not complemented or resampled. -/
noncomputable def encodeFullRecord (place : Place ≃ Pop) (vertex : Vertex ≃ RegisterID)
    (leaf : Copy ≃ Label) (tag : Tag ≃ Bin) (a : FullRecord Place Vertex Copy Tag) :
    FullRecord Pop RegisterID Label Bin :=
  ((fun p => (a.1 (place.symm p)).image (relabelQuotient leaf tag)),
    fun v => a.2 (vertex.symm v))

/-- No desired decoder correctness or law equality is supplied as a field. -/
theorem encodeFullRecord_injective (place : Place ≃ Pop) (vertex : Vertex ≃ RegisterID)
    (leaf : Copy ≃ Label) (tag : Tag ≃ Bin) :
    Function.Injective (encodeFullRecord place vertex leaf tag) := by
  intro a b hab
  apply Prod.ext
  · funext p
    apply Finset.image_injective (relabelQuotient_injective leaf tag)
    have h := congrArg (fun q : FullRecord Pop RegisterID Label Bin => q.1 (place p)) hab
    simpa only [encodeFullRecord, Equiv.symm_apply_apply] using h
  · funext v
    have h := congrArg (fun q : FullRecord Pop RegisterID Label Bin => q.2 (vertex v)) hab
    simpa only [encodeFullRecord, Equiv.symm_apply_apply] using h

theorem encodeFullRecord_register (place : Place ≃ Pop) (vertex : Vertex ≃ RegisterID)
    (leaf : Copy ≃ Label) (tag : Tag ≃ Bin)
    (a : FullRecord Place Vertex Copy Tag) (v : Vertex) :
    (encodeFullRecord place vertex leaf tag a).2 (vertex v) = a.2 v := by
  simp only [encodeFullRecord, Equiv.symm_apply_apply]

end CloudG6.FullJointCoordinateEncoding
