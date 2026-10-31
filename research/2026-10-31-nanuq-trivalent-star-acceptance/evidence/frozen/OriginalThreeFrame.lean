import ThreeGermFrame
import OriginalShortArms

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval
open scoped Graph

 theorem half_image_interval (f : ℝ → Plane) (a : ℝ) :
    (fun t : ℝ => f (t/2)) '' Icc 0 a = f '' Icc 0 (a/2) := by
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨t/2,⟨by linarith [ht.1],by linarith [ht.2]⟩,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    refine ⟨2*t,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    congr 1
    ring

 theorem three_frame_of_isDrawing {E : Type*} {G : Graph Plane E}
    {drawing : E → ℝ → Plane} (hD : G.IsDrawing drawing)
    (es : Fin 3 → E) (ws : Fin 3 → Plane) (v : Plane)
    (hinc : ∀ i, G.IsLink (es i) v (ws i)) (hids : Function.Injective es) :
    ∃ (f : Fin 3 → ℝ → Plane) (H : Plane ≃ₜ Plane) (c s : ℝ) (q : Plane),
      (∀ i, ContinuousOn (f i) I ∧ InjOn (f i) I ∧
        f i '' I = Graph.edgeArc drawing (es i) ∧ f i 0 = v ∧ f i 1 = ws i) ∧
      |c| < 2 ∧ 0 < s ∧ s ≤ 1/2 ∧ 0 < q 1 ∧ H v = 0 ∧
      H '' (f 0 '' Icc 0 (1/6) ∪ f 1 '' Icc 0 (1/6)) = centeredCarrier c ∧
      H '' (f 2 '' Icc 0 s) = segment ℝ (0:Plane) q ∧
      H (f 0 (1/6)) = Plane.mk (2-c) 0 ∧
      H (f 1 (1/6)) = Plane.mk (-2-c) 0 ∧ H (f 2 s) = q := by
  obtain ⟨f,hf,hshort⟩ := short_arm_family_of_isDrawing hD es ws v hinc hids
  let g := fun i t => f i (t/2)
  have hh : ∀ t ∈ I, t/2 ∈ I := by
    intro t ht; exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hc : ∀ i, ContinuousOn (g i) I := fun i =>
    (hf i).1.comp (by fun_prop) hh
  have hi : ∀ i, InjOn (g i) I := by
    intro i t ht u hu he
    have := (hf i).2.1 (hh t ht) (hh u hu) he
    linarith
  have h0 : ∀ i, g i 0 = g 0 0 := by
    intro i
    simp only [g,zero_div,(hf i).2.2.2.1,(hf 0).2.2.2.1]
  have hm : ∀ i j, i ≠ j → ∀ z ∈ g i '' I, z ∈ g j '' I → z = g 0 0 := by
    intro i j hij z hz hz'
    simpa only [g,zero_div,(hf 0).2.2.2.1] using hshort i j hij z hz hz'
  obtain ⟨H,c,t,q,hcabs,ht,htp,hqy,hH0,hHA,hHthird,hend0,hend1,hend2⟩ := three_continued_germ_frame g hc hi h0 hm
  have hg0 : g 0 0 = v := by simp only [g,zero_div,(hf 0).2.2.2.1]
  rw [hg0] at hH0
  have hhalf : (1/3:ℝ)/2 = 1/6 := by norm_num
  change H '' ((fun u => f 0 (u/2)) '' Icc 0 (1/3) ∪
    (fun u => f 1 (u/2)) '' Icc 0 (1/3)) = _ at hHA
  rw [half_image_interval,half_image_interval,hhalf] at hHA
  change H '' ((fun u => f 2 (u/2)) '' Icc 0 t) = _ at hHthird
  rw [half_image_interval] at hHthird
  have hend0' : H (f 0 (1/6)) = Plane.mk (2-c) 0 := by
    simpa only [g,hhalf] using hend0
  have hend1' : H (f 1 (1/6)) = Plane.mk (-2-c) 0 := by
    simpa only [g,hhalf] using hend1
  exact ⟨f,H,c,t/2,q,hf,hcabs,by linarith,by linarith [ht.2],hqy,hH0,hHA,hHthird,
    hend0',hend1',hend2⟩

 theorem actual_three_incident_frame {V E : Type*} {G : Nanuq.Source.EdgeGraph V E}
    (D : G1OuterLabelledMultigraphCurves.PlanarCurves G)
    (es : Fin 3 → E) (ws : Fin 3 → V) (v : V)
    (hinc : ∀ i, G.Inc (es i) v (ws i)) (hids : Function.Injective es) :
    ∃ (f : Fin 3 → ℝ → Plane) (H : Plane ≃ₜ Plane) (c s : ℝ) (q : Plane),
      (∀ i, ContinuousOn (f i) I ∧ InjOn (f i) I ∧
        f i '' I = Graph.edgeArc (NanuqFaithfulSupplierDrawing.curve D) (es i) ∧
        f i 0 = NanuqFaithfulSupplierDrawing.vertex D v ∧
        f i 1 = NanuqFaithfulSupplierDrawing.vertex D (ws i)) ∧
      |c| < 2 ∧ 0 < s ∧ s ≤ 1/2 ∧ 0 < q 1 ∧
      H (NanuqFaithfulSupplierDrawing.vertex D v) = 0 ∧
      H '' (f 0 '' Icc 0 (1/6) ∪ f 1 '' Icc 0 (1/6)) = centeredCarrier c ∧
      H '' (f 2 '' Icc 0 s) = segment ℝ (0:Plane) q ∧
      H (f 0 (1/6)) = Plane.mk (2-c) 0 ∧
      H (f 1 (1/6)) = Plane.mk (-2-c) 0 ∧ H (f 2 s) = q := by
  have he : ∀ i, (NanuqFaithfulSupplierDrawing.graph D).IsLink (es i)
      (NanuqFaithfulSupplierDrawing.vertex D v) (NanuqFaithfulSupplierDrawing.vertex D (ws i)) := by
    intro i
    rcases hinc i with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm⟩
    · exact Or.inr ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) ht.symm,
        congrArg (NanuqFaithfulSupplierDrawing.vertex D) hs.symm⟩
  exact three_frame_of_isDrawing (NanuqFaithfulSupplierDrawing.isDrawing D)
    es (fun i => NanuqFaithfulSupplierDrawing.vertex D (ws i))
    (NanuqFaithfulSupplierDrawing.vertex D v) he hids

#print axioms actual_three_incident_frame
end Nanuq.ActualStar
