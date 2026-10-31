import TrivalentLocal
import BinaryDegree

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies Nanuq.Source
open scoped Graph

 theorem binary_three_incident_exhausts {V E X : Type*}
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
    (N : RootedBinary V E X) (es : Fin 3 → E) (ws : Fin 3 → V) (v : V)
    (hinc : ∀ i, N.graph.Inc (es i) v (ws i)) (hids : Function.Injective es) :
    ∀ e, N.graph.source e = v ∨ N.graph.target e = v → ∃ i, es i = e := by
  classical
  let B := Finset.univ.filter (fun e : E => N.graph.source e = v ∨ N.graph.target e = v)
  let R := Finset.univ.image es
  have hiB : ∀ i, es i ∈ B := by
    intro i
    have he : N.graph.source (es i) = v ∨ N.graph.target (es i) = v := by
      rcases hinc i with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact Or.inl hs
      · exact Or.inr ht
    simpa [B] using he
  have hsub : R ⊆ B := by
    intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    exact hiB i
  have hRcard : R.card = 3 := by
    change (Finset.univ.image es).card = 3
    rw [Finset.card_image_of_injective _ hids]
    norm_num
  have hBcard : B.card ≤ 3 := by
    have hh := Nanuq.RawBlock.binary_incidence_bound N v
    have heq : {e | N.graph.source e = v ∨ N.graph.target e = v} = (B : Set E) := by
      ext e; simp [B]
    rw [heq,Set.ncard_coe_finset] at hh
    exact hh
  have hRB : R = B := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro e he
  have heB : e ∈ B := by simpa [B] using he
  have heR : e ∈ R := hRB.symm ▸ heB
  obtain ⟨i,_,hei⟩ := Finset.mem_image.mp heR
  exact ⟨i,hei⟩

/-- Actual finite rooted-binary source theorem at three distinct original
incident IDs. The degree bound DERIVES exhaustiveness; no star/face/order
certificate or polygonal drawing is an input. Coordinates are the existing
faithful coordinate equivalence, and the original whole drawing is retained. -/
theorem actual_binary_trivalent_star {V E X : Type*}
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
    (N : RootedBinary V E X) (D : G1OuterLabelledMultigraphCurves.PlanarCurves N.graph)
    (es : Fin 3 → E) (ws : Fin 3 → V) (v : V)
    (hinc : ∀ i, N.graph.Inc (es i) v (ws i)) (hids : Function.Injective es) :
    ∃ (H : Plane ≃ₜ Plane) (ε : ℝ) (q : Plane),
      0 < ε ∧ ε < ‖q‖ ∧ 0 < q 1 ∧
      H (NanuqFaithfulSupplierDrawing.vertex D v) = 0 ∧
      (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D)) ∩ Metric.ball 0 ε =
        ({z : Plane | z 1 = 0} ∪ segment ℝ (0:Plane) q) ∩ Metric.ball 0 ε := by
  let G := NanuqFaithfulSupplierDrawing.graph D
  haveI : G.Finite := by
    refine ⟨?_,?_⟩
    · change (range (NanuqFaithfulSupplierDrawing.vertex D)).Finite
      exact Set.finite_range _
    · change (univ : Set E).Finite
      exact Set.toFinite _
  have he : ∀ i, G.IsLink (es i) (NanuqFaithfulSupplierDrawing.vertex D v)
      (NanuqFaithfulSupplierDrawing.vertex D (ws i)) := by
    intro i
    rcases hinc i with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm⟩
    · exact Or.inr ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm⟩
  have hcover : ∀ e ∈ E(G), G.Inc e (NanuqFaithfulSupplierDrawing.vertex D v) →
      ∃ i, es i = e := by
    intro e _ heinc
    obtain ⟨w,hw⟩ := heinc
    have hor : N.graph.source e = v ∨ N.graph.target e = v := by
      rcases hw with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact Or.inl ((NanuqFaithfulSupplierDrawing.vertex_injective D) hs).symm
      · exact Or.inr ((NanuqFaithfulSupplierDrawing.vertex_injective D) hs).symm
    exact binary_three_incident_exhausts N es ws v hinc hids e hor
  have h := trivalent_local_drawing (NanuqFaithfulSupplierDrawing.isDrawing D)
    es (fun i => NanuqFaithfulSupplierDrawing.vertex D (ws i))
    (NanuqFaithfulSupplierDrawing.vertex D v) he hids hcover
  simpa only [NanuqFaithfulSupplierDrawing.pointSet_eq D] using h

#print axioms actual_binary_trivalent_star
end Nanuq.ActualStar
