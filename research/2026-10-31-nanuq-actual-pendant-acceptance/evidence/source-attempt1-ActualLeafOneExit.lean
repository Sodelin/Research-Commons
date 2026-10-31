import InteriorTerminalChart
import LeafTrace
import OneExit

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval
open scoped Graph

/-- Source-facing one-exit theorem for an ACTUAL degree-one original edge.
All compact trace, terminal shape and boundary-side data are derived here.
The parameter runs from the original leaf to its original neighbour. -/
theorem actual_leaf_one_exit {E : Type*} {G : Graph Plane E} [G.Finite]
    {drawing : E → ℝ → Plane} (hD : G.IsDrawing drawing)
    {e : E} {v w : Plane} (he : G.IsLink e v w)
    (hunique : ∀ g ∈ E(G), G.Inc g v → g = e)
    (f : ℝ → Plane) (hc : ContinuousOn f I) (hi : InjOn f I)
    (him : f '' I = Graph.edgeArc drawing e) (h0 : f 0=v) (h1 : f 1=w) :
    ∃ (H : Plane ≃ₜ Plane) (r b t : ℝ) (C : Set Plane),
      0 < r ∧ r < b ∧ t ∈ Ioo (1/2) (13/24) ∧ IsJordanCurve C ∧
      H (f (1/2))=0 ∧ H (f (13/24))=Plane.mk b 0 ∧ H (f t)=Plane.mk r 0 ∧
      H '' (f '' Icc (1/2) (13/24)) = segment ℝ (0:Plane) (Plane.mk b 0) ∧
      C ∩ (H '' Graph.pointSet G drawing) = {Plane.mk r 0} ∧
      (C ∪ inside C) ∩ (H '' Graph.pointSet G drawing) = H '' (f '' Icc 0 t) ∧
      Plane.mk r (r/2) ∈ C \ (H '' Graph.pointSet G drawing) ∧
      Plane.mk r (-r/2) ∈ C \ (H '' Graph.pointSet G drawing) ∧
      Plane.mk r (-r/2) ∈ connectedComponentIn (H '' Graph.pointSet G drawing)ᶜ
        (Plane.mk r (r/2)) := by
  obtain ⟨K,hK,hKA,hbase,htrace⟩ := leaf_trace_decomposition hD he hunique f hc hi him h0 h1
  obtain ⟨H,b,δ,hb,hδ,hmid,hend,hseg,hterm⟩ := interior_terminal_chart f hc hi
  let α : ℝ → Plane := fun u => H (f (u/2))
  let A := H '' (f '' Icc 0 (1/2))
  let L := H '' K
  have hαI : ∀ u ∈ I, u/2 ∈ I := by
    intro u hu; exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hαc : ContinuousOn α I := H.continuous.comp_continuousOn
    (hc.comp (by fun_prop) hαI)
  have hαi : InjOn α I := by
    intro u hu v hv heq
    have hh := hi (hαI u hu) (hαI v hv) (H.injective heq)
    linarith
  have hαA : α '' I = A := by
    change (fun u => H (f (u/2))) '' I = H '' (f '' Icc 0 (1/2))
    rw [← Set.image_image,half_parameter_image]
  have hαend : α 1=0 := by simpa [α] using hmid
  have hL : IsCompact L := hK.image H.continuous
  have hLA : Disjoint L (α '' I) := by
    rw [hαA,Set.disjoint_left]
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,heq⟩
    have hzy := H.injective heq
    exact Set.disjoint_left.mp hKA hy (hzy ▸ hz)
  have hbaseL : Plane.mk b 0 ∈ L := hend ▸ mem_image_of_mem H hbase
  obtain ⟨r,C,hr,hrb,hC,hAin,hLout,hleft,hright,hcap⟩ :=
    sampled_terminal_cap α hαc hαi hαend hL hLA hb hδ hbaseL (hαA.symm ▸ hterm)
  have hAin' : A ⊆ inside C := hαA ▸ hAin
  have hsplit : Icc (0:ℝ) (13/24) = Icc 0 (1/2) ∪ Icc (1/2) (13/24) := by
    ext u; simp only [mem_Icc,mem_union]; constructor
    · intro hu; by_cases h : u≤1/2
      · exact Or.inl ⟨hu.1,h⟩
      · exact Or.inr ⟨(lt_of_not_ge h).le,hu.2⟩
    · rintro (hu | hu) <;> constructor <;> linarith [hu.1,hu.2]
  have hT : H '' Graph.pointSet G drawing = A ∪ segment ℝ (0:Plane) (Plane.mk b 0) ∪ L := by
    rw [htrace,Set.image_union,hsplit,Set.image_union,Set.image_union,hseg]
    change L ∪ (A ∪ segment ℝ (0:Plane) (Plane.mk b 0)) = _
    rw [union_comm]
  obtain ⟨hinter,hclosed,hu,hd,hreturn⟩ := terminal_one_exit hr hrb hC hAin' hLout hleft hright hcap
  have hqseg : Plane.mk r 0 ∈ segment ℝ (0:Plane) (Plane.mk b 0) := by
    change Plane.mk r 0 ∈ segment ℝ (Plane.mk 0 0) (Plane.mk b 0)
    rw [mem_segment_horiz,segment_eq_Icc hb.le]
    exact ⟨rfl,hr.le,hrb.le⟩
  obtain ⟨y,⟨t,ht,rfl⟩,htq⟩ := hseg.symm ▸ hqseg
  have htm : (1/2:ℝ)<t := by
    apply lt_of_le_of_ne ht.1
    intro heq
    have hh : (0:Plane)=Plane.mk r 0 := by simpa [← heq,hmid] using htq
    have := congrArg (fun z : Plane => z 0) hh
    simp at this
    linarith
  have hte : t<(13/24:ℝ) := by
    apply lt_of_le_of_ne ht.2
    intro heq
    have hh : Plane.mk b 0=Plane.mk r 0 := by simpa [heq,hend] using htq
    have := congrArg (fun z : Plane => z 0) hh
    simp at this
    linarith
  have hsub : Icc (1/2:ℝ) t ⊆ Icc (1/2) (13/24) := Icc_subset_Icc le_rfl ht.2
  have hsubI : Icc (1/2:ℝ) (13/24) ⊆ I := Icc_subset_Icc (by norm_num) (by norm_num)
  have hline : ∀ u∈Icc (1/2:ℝ) t, H (f u) 1=0 := by
    intro u hu
    have hh : H (f u) ∈ segment ℝ (0:Plane) (Plane.mk b 0) :=
      hseg ▸ ⟨f u,⟨u,hsub hu,rfl⟩,rfl⟩
    change H (f u) ∈ segment ℝ (Plane.mk 0 0) (Plane.mk b 0) at hh
    exact (mem_segment_horiz.mp hh).1
  have hsegcut : H '' (f '' Icc (1/2) t) = segment ℝ (0:Plane) (Plane.mk r 0) := by
    rw [Set.image_image]
    have hh := horizontal_arc_image (f := fun u => H (f u)) htm.le
      (H.continuous.comp_continuousOn (hc.mono (hsub.trans hsubI)))
      (fun u hu v hv heq => hi (hsubI (hsub hu)) (hsubI (hsub hv)) (H.injective heq)) hline
    simpa only [hmid,htq] using hh
  have hprefix : H '' (f '' Icc 0 t) = A ∪ segment ℝ (0:Plane) (Plane.mk r 0) := by
    have heq : Icc (0:ℝ) t = Icc 0 (1/2) ∪ Icc (1/2) t := by
      ext u; simp only [mem_Icc,mem_union]; constructor
      · intro hu; by_cases h : u≤1/2
        · exact Or.inl ⟨hu.1,h⟩
        · exact Or.inr ⟨(lt_of_not_ge h).le,hu.2⟩
      · rintro (hu | hu) <;> constructor <;> linarith [hu.1,hu.2]
    rw [heq,Set.image_union,Set.image_union,hsegcut]
  refine ⟨H,r,b,t,C,hr,hrb,⟨htm,hte⟩,hC,hmid,hend,htq,hseg,?_,?_,?_,?_,?_⟩
  · simpa only [hT] using hinter
  · simpa only [hT,hprefix] using hclosed
  · simpa only [hT] using hu
  · simpa only [hT] using hd
  · simpa only [hT] using hreturn

#print axioms actual_leaf_one_exit
end Nanuq.Pendant
