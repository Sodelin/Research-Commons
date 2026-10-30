import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option debug.skipKernelTC false
namespace Nanuq.CoordinateFace
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact coordinate transport; no redrawing or contour assertion. -/
theorem component_image (e : E ≃L[ℝ] F) (S : Set E) (x : E) (hx : x ∉ S) :
    e '' connectedComponentIn Sᶜ x =
      connectedComponentIn (e '' S)ᶜ (e x) := by
  have h := e.toHomeomorph.image_connectedComponentIn (s := Sᶜ) hx
  change e '' connectedComponentIn Sᶜ x = connectedComponentIn (e '' Sᶜ) (e x) at h
  have hc : e '' Sᶜ = (e '' S)ᶜ := e.toEquiv.image_compl S
  rw [hc] at h
  exact h

/-- A bounded inverse prohibits loss of unboundedness. -/
theorem unbounded_image (e : E ≃L[ℝ] F) (S : Set E)
    (hS : ¬ Bornology.IsBounded S) : ¬ Bornology.IsBounded (e '' S) := by
  intro hb
  have h := e.symm.toContinuousLinearMap.lipschitz.isBounded_image hb
  have he : e.symm '' (e '' S) = S := by ext x; simp
  change Bornology.IsBounded (e.symm '' (e '' S)) at h
  exact hS (he ▸ h)

/-- Transfers the exact given complementary face and taxon incidence.
No assertion that an arbitrary polygonal redrawing preserves this face. -/
theorem outer_face_transfer {X : Type*} (e : E ≃L[ℝ] F)
    (S : Set E) (x : E) (labels : X → E)
    (hx : x ∉ S)
    (hu : ¬ Bornology.IsBounded (connectedComponentIn Sᶜ x))
    (hl : ∀ a, labels a ∈ closure (connectedComponentIn Sᶜ x)) :
    e x ∉ e '' S ∧
    ¬ Bornology.IsBounded (connectedComponentIn (e '' S)ᶜ (e x)) ∧
    ∀ a, e (labels a) ∈ closure (connectedComponentIn (e '' S)ᶜ (e x)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hx
  · rw [← component_image e S x hx]
    exact unbounded_image e _ hu
  · intro a
    rw [← component_image e S x hx]
    have hc : e '' closure (connectedComponentIn Sᶜ x) =
        closure (e '' connectedComponentIn Sᶜ x) :=
      e.toHomeomorph.image_closure _
    rw [← hc]
    exact ⟨labels a, hl a, rfl⟩

#print axioms component_image
#print axioms unbounded_image
#print axioms outer_face_transfer
end Nanuq.CoordinateFace
