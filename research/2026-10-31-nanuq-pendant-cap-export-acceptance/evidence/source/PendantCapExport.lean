import OriginalPendant

set_option debug.skipKernelTC false
/-! UNCOMPILED strengthened export of the accepted SAME source construction.
The only new output is the entire vertical cap already produced by
sampled_terminal_cap; all original hypotheses and all old conclusions remain.
Original accepted declarations and files are unchanged. -/
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval Nanuq.Source
open scoped Graph

/-- Source-facing one-exit theorem for an ACTUAL degree-one original edge.
All compact trace, terminal shape and boundary-side data are derived here.
The parameter runs from the original leaf to its original neighbour. -/
theorem actual_leaf_one_exit_cap {E : Type*} {G : Graph Plane E} [G.Finite]
    {drawing : E → ℝ → Plane} (hD : G.IsDrawing drawing)
    {e : E} {v w : Plane} (he : G.IsLink e v w)
    (hunique : ∀ g ∈ E(G), G.Inc g v → g = e)
    (f : ℝ → Plane) (hc : ContinuousOn f I) (hi : InjOn f I)
    (him : f '' I = Graph.edgeArc drawing e) (h0 : f 0=v) (h1 : f 1=w) :
    ∃ (H : Plane ≃ₜ Plane) (r b t : ℝ) (C : Set Plane),
      0 < r ∧ r < b ∧ t ∈ Ioo (1/2) (13/24) ∧ IsJordanCurve C ∧
      (∀ y : ℝ, |y| < r → Plane.mk r y ∈ C) ∧
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
  have hzero : (0:Plane) = Plane.mk 0 0 := by
    ext i; fin_cases i <;> simp
  have hqseg : Plane.mk r 0 ∈ segment ℝ (0:Plane) (Plane.mk b 0) := by
    rw [hzero]
    rw [mem_segment_horiz,segment_eq_Icc hb.le]
    exact ⟨rfl,hr.le,hrb.le⟩
  obtain ⟨y,⟨t,ht,rfl⟩,htq⟩ := hseg.symm ▸ hqseg
  have htm : (1/2:ℝ)<t := by
    apply lt_of_le_of_ne ht.1
    intro heq
    have hh : (0:Plane)=Plane.mk r 0 :=
      hmid.symm.trans (by simpa only [← heq] using htq)
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
    rw [hzero] at hh
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
  refine ⟨H,r,b,t,C,hr,hrb,⟨htm,hte⟩,hC,hcap,hmid,hend,htq,hseg,?_,?_,?_,?_,?_⟩
  · simpa only [hT] using hinter
  · simpa only [hT,hprefix] using hclosed
  · simpa only [hT] using hu
  · simpa only [hT] using hd
  · simpa only [hT] using hreturn


/-- Original finite rooted-binary source, SAME full faithful drawing and SAME
edge ID. The derived leaf-to-parent parameterization and unique exit are
retained. Upper/lower are geometrical sides of this particular directed
carrier, not an assumed global orientation or a face-order certificate. -/
theorem original_taxon_one_exit_cap {V E X : Type*}
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
    (N : RootedBinary V E X) (D : G1OuterLabelledMultigraphCurves.PlanarCurves N.graph)
    (x : X) :
    ∃ (e : E) (f : ℝ → Plane) (H : Plane ≃ₜ Plane) (r b t : ℝ) (C : Set Plane),
      N.graph.target e=N.leaf x ∧ ContinuousOn f I ∧ InjOn f I ∧
      f '' I=Graph.edgeArc (NanuqFaithfulSupplierDrawing.curve D) e ∧
      f 0=NanuqFaithfulSupplierDrawing.vertex D (N.leaf x) ∧
      f 1=NanuqFaithfulSupplierDrawing.vertex D (N.graph.source e) ∧
      0 < r ∧ r < b ∧ t ∈ Ioo (1/2) (13/24) ∧ IsJordanCurve C ∧
      (∀ y : ℝ, |y| < r → Plane.mk r y ∈ C) ∧
      H (f (1/2))=0 ∧ H (f (13/24))=Plane.mk b 0 ∧ H (f t)=Plane.mk r 0 ∧
      H '' (f '' Icc (1/2) (13/24))=segment ℝ (0:Plane) (Plane.mk b 0) ∧
      C ∩ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D))={Plane.mk r 0} ∧
      (C ∪ inside C) ∩ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D))=H '' (f '' Icc 0 t) ∧
      Plane.mk r (r/2) ∈ C \ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D)) ∧
      Plane.mk r (-r/2) ∈ C \ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D)) ∧
      Plane.mk r (-r/2) ∈ connectedComponentIn
        (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
          G1OuterLabelledMultigraphCurves.drawing D))ᶜ (Plane.mk r (r/2)) := by
  obtain ⟨e,het,hunique⟩ := original_leaf_unique_id N x
  let G := NanuqFaithfulSupplierDrawing.graph D
  haveI : G.Finite := by
    refine ⟨?_,?_⟩
    · change (range (NanuqFaithfulSupplierDrawing.vertex D)).Finite
      exact Set.finite_range _
    · change (univ : Set E).Finite
      exact Set.toFinite _
  have he : G.IsLink e (NanuqFaithfulSupplierDrawing.vertex D (N.leaf x))
      (NanuqFaithfulSupplierDrawing.vertex D (N.graph.source e)) :=
    Or.inr ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) het.symm,rfl⟩
  have hcover : ∀ g ∈ E(G), G.Inc g (NanuqFaithfulSupplierDrawing.vertex D (N.leaf x)) → g=e := by
    intro g _ hg
    obtain ⟨w,hw⟩ := hg
    apply hunique g
    rcases hw with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ((NanuqFaithfulSupplierDrawing.vertex_injective D) hs).symm
    · exact Or.inr ((NanuqFaithfulSupplierDrawing.vertex_injective D) hs).symm
  have hD := NanuqFaithfulSupplierDrawing.isDrawing D
  obtain ⟨f,hc,hi,him,h0,h1⟩ := hD.edge_isArcBetween he
  obtain ⟨H,r,b,t,C,hrest⟩ := actual_leaf_one_exit_cap hD he hcover f hc hi him h0 h1
  refine ⟨e,f,H,r,b,t,C,het,hc,hi,him,h0,h1,?_⟩
  simpa only [NanuqFaithfulSupplierDrawing.pointSet_eq D] using hrest


#print axioms actual_leaf_one_exit_cap
#print axioms original_taxon_one_exit_cap
end Nanuq.Pendant
