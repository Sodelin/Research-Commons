import Mathlib.Topology.Connected.Basic

/-! Minimal component merger at an actually removed frontier point.
No Jordan shape, local radius, face count or contour/order is assumed or derived. -/
namespace Nanuq.RemovedPointMerge
open Set
variable {A : Type*} [TopologicalSpace A]

/-- Adding a closure point to a preconnected old face joins it to that point's new component. -/
theorem subset_component_of_closure {F U : Set A} {x : A}
    (hF : IsPreconnected F) (hFU : F ⊆ U) (hxF : x ∈ closure F) (hxU : x ∈ U) :
    F ⊆ connectedComponentIn U x := by
  have hi : IsPreconnected (insert x F) := hF.subset_closure
    (subset_insert x F) (insert_subset_iff.mpr ⟨hxF,subset_closure⟩)
  exact (subset_insert x F).trans (hi.subset_connectedComponentIn
    (mem_insert x F) (insert_subset_iff.mpr ⟨hxU,hFU⟩))

/-- Old complement component enters the new component through the removed point.
The point must REALLY be absent from the new drawing. -/
theorem old_face_subset_new_component {old new : Set A} (hnew : new ⊆ old)
    {a x : A} (hx : x ∉ new) (hfront : x ∈ closure (connectedComponentIn oldᶜ a)) :
    connectedComponentIn oldᶜ a ⊆ connectedComponentIn newᶜ x := by
  apply subset_component_of_closure isPreconnected_connectedComponentIn _ hfront hx
  exact (connectedComponentIn_subset oldᶜ a).trans (compl_subset_compl.mpr hnew)

/-- Explicit basepoint hypotheses make the two old faces' new components equal. -/
theorem two_old_faces_merge {old new : Set A} (hnew : new ⊆ old)
    {a b x : A} (ha : a ∉ old) (hb : b ∉ old) (hx : x ∉ new)
    (hxa : x ∈ closure (connectedComponentIn oldᶜ a))
    (hxb : x ∈ closure (connectedComponentIn oldᶜ b)) :
    connectedComponentIn newᶜ a = connectedComponentIn newᶜ b := by
  have hA := old_face_subset_new_component hnew hx hxa
  have hB := old_face_subset_new_component hnew hx hxb
  have ha' : a ∈ connectedComponentIn newᶜ x := hA (mem_connectedComponentIn ha)
  have hb' : b ∈ connectedComponentIn newᶜ x := hB (mem_connectedComponentIn hb)
  exact (connectedComponentIn_eq ha').symm.trans (connectedComponentIn_eq hb')

#print axioms subset_component_of_closure
#print axioms old_face_subset_new_component
#print axioms two_old_faces_merge
end Nanuq.RemovedPointMerge
