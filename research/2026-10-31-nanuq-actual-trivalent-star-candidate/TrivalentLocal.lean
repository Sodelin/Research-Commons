import FiniteTrace

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval Metric
open scoped Graph

 theorem trivalent_local_drawing {E : Type*} {G : Graph Plane E} [G.Finite]
    {drawing : E → ℝ → Plane} (hD : G.IsDrawing drawing)
    (es : Fin 3 → E) (ws : Fin 3 → Plane) (v : Plane)
    (hinc : ∀ i, G.IsLink (es i) v (ws i)) (hids : Function.Injective es)
    (hcover : ∀ e ∈ E(G), G.Inc e v → ∃ i, es i = e) :
    ∃ (H : Plane ≃ₜ Plane) (ε : ℝ) (q : Plane),
      0 < ε ∧ ε < ‖q‖ ∧ 0 < q 1 ∧ H v = 0 ∧
      (H '' Graph.pointSet G drawing) ∩ ball 0 ε =
        ({z : Plane | z 1 = 0} ∪ segment ℝ (0:Plane) q) ∩ ball 0 ε := by
  obtain ⟨f,H,c,s,q,hf,hc,hsp,hs,hqy,hHv,hHA,hHQ,_,_,_⟩ :=
    three_frame_of_isDrawing hD es ws v hinc hids
  let a : Fin 3 → ℝ := ![1/6,1/6,s]
  have ha : ∀ i, 0 < a i ∧ a i ≤ 1 := by
    intro i
    fin_cases i <;> simp [a]
    exact ⟨hsp,by linarith⟩
  obtain ⟨K,hK,hvK,hdecomp⟩ := finite_discarded_trace hD es ws v hinc hcover f hf a ha
  have hprefix : (⋃ i, f i '' Icc 0 (a i)) =
      (f 0 '' Icc 0 (1/6) ∪ f 1 '' Icc 0 (1/6)) ∪ f 2 '' Icc 0 s := by
    ext z
    simp [Fin.exists_fin_succ,a,or_assoc]
  have hFull : H '' Graph.pointSet G drawing = H '' K ∪
      (centeredCarrier c ∪ segment ℝ (0:Plane) q) := by
    rw [hdecomp,hprefix,image_union,image_union,hHA,hHQ]
  have hHK : IsCompact (H '' K) := hK.image H.continuous
  have hzK : (0:Plane) ∉ H '' K := by
    rintro ⟨x,hx,hHx⟩
    have he : x=v := H.injective (hHx.trans hHv.symm)
    exact hvK (he ▸ hx)
  obtain ⟨δ,hδ,hδsub⟩ := Metric.isOpen_iff.mp hHK.isClosed.isOpen_compl 0 hzK
  have hqne : q ≠ 0 := by intro he; simpa [he] using hqy
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hqne
  let ε := min (δ/2) (min ((2-|c|)/2) (‖q‖/2))
  have hε : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hεδ : ε < δ := by
    have hh : ε ≤ δ/2 := min_le_left _ _
    linarith
  have hεq : ε < ‖q‖ := by
    have hh : ε ≤ ‖q‖/2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hεc : ε+|c| < 2 := by
    have hh : ε ≤ (2-|c|)/2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hball : ∀ z ∈ ball (0:Plane) ε, z ∉ H '' K := by
    intro z hz
    exact hδsub (ball_subset_ball hεδ.le hz)
  have hline : ∀ z ∈ ball (0:Plane) ε, z 1 = 0 → z ∈ centeredCarrier c := by
    intro z hz hzy
    have hzn : ‖z‖ < ε := by simpa only [mem_ball,dist_zero_right] using hz
    have hx : |z 0| < ε := lt_of_le_of_lt
      ((Plane.abs_zero_le_supNorm z).trans (Plane.supNorm_le_norm z)) hzn
    have hxc : |z 0+c| ≤ 2 := le_of_lt (lt_of_le_of_lt (abs_add (z 0) c) (by linarith))
    exact ⟨hzy,hxc⟩
  refine ⟨H,ε,q,hε,hεq,hqy,hHv,?_⟩
  rw [hFull]
  ext z
  constructor
  · rintro ⟨hz,hzb⟩
    rcases hz with hzK | hz
    · exact False.elim (hball z hzb hzK)
    · exact ⟨hz.imp (fun h => h.1) id,hzb⟩
  · rintro ⟨hz,hzb⟩
    exact ⟨Or.inr (hz.imp (hline z hzb) id),hzb⟩

#print axioms trivalent_local_drawing
end Nanuq.ActualStar
