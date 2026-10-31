import OriginalGermLoops

set_option debug.skipKernelTC false
/-! UNCOMPILED actual-ID family supplier for the star construction.
Parallel IDs are retained; interior halves exclude the shared far endpoint. -/
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval
open scoped Graph

 theorem short_arm_family_of_isDrawing {E ι : Type*} {G : Graph Plane E}
    {drawing : E → ℝ → Plane} (hD : G.IsDrawing drawing)
    (es : ι → E) (ws : ι → Plane) (v : Plane)
    (hinc : ∀ i, G.IsLink (es i) v (ws i)) (hids : Function.Injective es) :
    ∃ f : ι → ℝ → Plane,
      (∀ i, ContinuousOn (f i) I ∧ InjOn (f i) I ∧
        f i '' I = Graph.edgeArc drawing (es i) ∧ f i 0 = v ∧ f i 1 = ws i) ∧
      (∀ i j, i ≠ j → ∀ z ∈ (fun t : ℝ => f i (t/2)) '' I,
        z ∈ (fun t : ℝ => f j (t/2)) '' I → z = v) := by
  have hparam : ∀ i, ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧
      f '' I = Graph.edgeArc drawing (es i) ∧ f 0 = v ∧ f 1 = ws i :=
    fun i => hD.edge_isArcBetween (hinc i)
  choose f hfc hfi hfim hf0 hf1 using hparam
  refine ⟨f,fun i => ⟨hfc i,hfi i,hfim i,hf0 i,hf1 i⟩,?_⟩
  intro i j hij z hz hz'
  obtain ⟨t,ht,rfl⟩ := hz
  obtain ⟨u,hu,he⟩ := hz'
  have hh : ∀ s ∈ I, s/2 ∈ I := by
    intro s hs; exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have he₁ : f i (t/2) ∈ Graph.edgeArc drawing (es i) := hfim i ▸ ⟨t/2,hh t ht,rfl⟩
  have he₂ : f i (t/2) ∈ Graph.edgeArc drawing (es j) := hfim j ▸ ⟨u/2,hh u hu,he⟩
  have hne : es i ≠ es j := fun he => hij (hids he)
  have hv := hD.arcs_meet_at_vertex (hinc i).edge_mem (hinc j).edge_mem hne he₁ he₂
  rcases hD.vertex_mem_edgeArc (hinc i) hv he₁ with hz | hz
  · exact hz
  · have ht1 : t/2 = 1 := hfi i (hh t ht) one_mem_I (hz.trans (hf1 i).symm)
    linarith [ht.2]

 theorem actual_short_arm_family {V E ι : Type*} {G : Nanuq.Source.EdgeGraph V E}
    (D : G1OuterLabelledMultigraphCurves.PlanarCurves G)
    (es : ι → E) (ws : ι → V) (v : V)
    (hinc : ∀ i, G.Inc (es i) v (ws i)) (hids : Function.Injective es) :
    ∃ f : ι → ℝ → Plane,
      (∀ i, ContinuousOn (f i) I ∧ InjOn (f i) I ∧
        f i '' I = Graph.edgeArc (NanuqFaithfulSupplierDrawing.curve D) (es i) ∧
        f i 0 = NanuqFaithfulSupplierDrawing.vertex D v ∧
        f i 1 = NanuqFaithfulSupplierDrawing.vertex D (ws i)) ∧
      (∀ i j, i ≠ j → ∀ z ∈ (fun t : ℝ => f i (t/2)) '' I,
        z ∈ (fun t : ℝ => f j (t/2)) '' I → z = NanuqFaithfulSupplierDrawing.vertex D v) := by
  have he : ∀ i, (NanuqFaithfulSupplierDrawing.graph D).IsLink (es i)
      (NanuqFaithfulSupplierDrawing.vertex D v) (NanuqFaithfulSupplierDrawing.vertex D (ws i)) := by
    intro i
    rcases hinc i with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm⟩
    · exact Or.inr ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm⟩
  exact short_arm_family_of_isDrawing (NanuqFaithfulSupplierDrawing.isDrawing D)
    es (fun i => NanuqFaithfulSupplierDrawing.vertex D (ws i))
    (NanuqFaithfulSupplierDrawing.vertex D v) he hids

#print axioms actual_short_arm_family
end Nanuq.ActualStar
