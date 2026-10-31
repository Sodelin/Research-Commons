import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Bounded

set_option debug.skipKernelTC false
namespace Nanuq.AmbientTransport
open Set
variable {E F : Type*} [MetricSpace E] [MetricSpace F]
  [ProperSpace E] [ProperSpace F]

/-- Properness, not a Lipschitz bound, preserves bounded sets under a homeomorphism. -/
theorem bounded_image (e : E ≃ₜ F) {S : Set E} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (e '' S) :=
  (hS.isCompact_closure.image e.continuous).isBounded.subset (image_mono subset_closure)

theorem bounded_image_iff (e : E ≃ₜ F) (S : Set E) :
    Bornology.IsBounded (e '' S) ↔ Bornology.IsBounded S := by
  refine ⟨fun h => ?_, bounded_image e⟩
  have h' := bounded_image e.symm h
  have he : e.symm '' (e '' S) = S := by ext x; simp
  exact he ▸ h'

/-- Transports the SAME complementary component, not an arbitrarily chosen face. -/
theorem component_image (e : E ≃ₜ F) (S : Set E) (x : E) (hx : x ∉ S) :
    e '' connectedComponentIn Sᶜ x = connectedComponentIn (e '' S)ᶜ (e x) := by
  have h := e.image_connectedComponentIn (s := Sᶜ) hx
  have hc : e '' Sᶜ = (e '' S)ᶜ := e.toEquiv.image_compl S
  rw [hc] at h
  exact h

/-- Literal predicate used in the supplier's `inside` definition. -/
theorem inside_predicate_iff (e : E ≃ₜ F) (S : Set E) (x : E) :
    (e x ∉ e '' S ∧ Bornology.IsBounded (connectedComponentIn (e '' S)ᶜ (e x))) ↔
    (x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)) := by
  have hn : e x ∉ e '' S ↔ x ∉ S := by simp
  constructor
  · rintro ⟨hx, hb⟩
    have hx' := hn.mp hx
    refine ⟨hx', ?_⟩
    rw [← component_image e S x hx'] at hb
    exact (bounded_image_iff e _).mp hb
  · rintro ⟨hx, hb⟩
    refine ⟨hn.mpr hx, ?_⟩
    rw [← component_image e S x hx]
    exact bounded_image e hb

/-- Literal predicate used in the supplier's `outside` definition. -/
theorem outside_predicate_iff (e : E ≃ₜ F) (S : Set E) (x : E) :
    (e x ∉ e '' S ∧ ¬ Bornology.IsBounded (connectedComponentIn (e '' S)ᶜ (e x))) ↔
    (x ∉ S ∧ ¬ Bornology.IsBounded (connectedComponentIn Sᶜ x)) := by
  have hn : e x ∉ e '' S ↔ x ∉ S := by simp
  constructor
  · rintro ⟨hx, hb⟩
    have hx' := hn.mp hx
    refine ⟨hx', ?_⟩
    rw [← component_image e S x hx'] at hb
    exact fun h => hb (bounded_image e h)
  · rintro ⟨hx, hb⟩
    refine ⟨hn.mpr hx, ?_⟩
    rw [← component_image e S x hx]
    exact fun h => hb ((bounded_image_iff e _).mp h)

/-- Exact pullback of the labelled closure-incidence conclusion of the crosscut theorem. -/
theorem closure_inter_pullback (e : E ≃ₜ F) (D C A : Set E)
    (h : closure (e '' D) ∩ e '' C = e '' A) : closure D ∩ C = A := by
  apply e.injective.image_injective
  rw [image_inter e.injective, e.image_closure]
  exact h

/-- The original outside point and ALL original labelled closure incidences are retained. -/
theorem outer_face_transfer {X : Type*} (e : E ≃ₜ F)
    (S : Set E) (x : E) (labels : X → E)
    (hx : x ∉ S)
    (hu : ¬ Bornology.IsBounded (connectedComponentIn Sᶜ x))
    (hl : ∀ a, labels a ∈ closure (connectedComponentIn Sᶜ x)) :
    e x ∉ e '' S ∧
    ¬ Bornology.IsBounded (connectedComponentIn (e '' S)ᶜ (e x)) ∧
    ∀ a, e (labels a) ∈ closure (connectedComponentIn (e '' S)ᶜ (e x)) := by
  have ho := (outside_predicate_iff e S x).mpr ⟨hx, hu⟩
  refine ⟨ho.1, ho.2, fun a => ?_⟩
  rw [← component_image e S x hx, ← e.image_closure]
  exact mem_image_of_mem e (hl a)

#print axioms bounded_image
#print axioms bounded_image_iff
#print axioms component_image
#print axioms inside_predicate_iff
#print axioms outside_predicate_iff
#print axioms closure_inter_pullback
#print axioms outer_face_transfer
end Nanuq.AmbientTransport
