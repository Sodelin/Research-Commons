import OriginalShortArms

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval
open scoped Graph

/-- ALL other vertices/edge carriers and the FULL actual residual tail form
one compact unwanted set. No endpoint chart or source-face assertion is assumed. -/
theorem leaf_trace_decomposition {E : Type*} {G : Graph Plane E} [G.Finite]
    {drawing : E → ℝ → Plane} (hD : G.IsDrawing drawing)
    {e : E} {v w : Plane} (he : G.IsLink e v w)
    (hunique : ∀ g ∈ E(G), G.Inc g v → g = e)
    (f : ℝ → Plane) (hc : ContinuousOn f I) (hi : InjOn f I)
    (him : f '' I = Graph.edgeArc drawing e) (h0 : f 0 = v) (h1 : f 1 = w) :
    ∃ K : Set Plane, IsCompact K ∧ Disjoint K (f '' Icc 0 (1/2)) ∧
      f (13/24) ∈ K ∧ Graph.pointSet G drawing = K ∪ f '' Icc 0 (13/24) := by
  let J : Set E := {g | g ∈ E(G) ∧ g ≠ e}
  have hJfin : J.Finite := (Graph.finite_edgeSet G).subset (fun _ hg => hg.1)
  letI : Finite J := Set.finite_coe_iff.mpr hJfin
  let B := ⋃ g : J, Graph.edgeArc drawing g.val
  let W := V(G) \ {v}
  let T := f '' Icc (13/24) 1
  let K := (W ∪ B) ∪ T
  have hW : IsCompact W := ((Graph.finite_vertexSet G).subset sdiff_subset).isCompact
  have hB : IsCompact B := isCompact_iUnion (fun g : J => hD.isCompact_edgeArc g.property.1)
  have hTI : Icc (13/24:ℝ) 1 ⊆ I := Icc_subset_Icc (by norm_num) le_rfl
  have hT : IsCompact T := isCompact_Icc.image_of_continuousOn (hc.mono hTI)
  have hAI : Icc (0:ℝ) (1/2) ⊆ I := Icc_subset_Icc le_rfl (by norm_num)
  have hPI : Icc (0:ℝ) (13/24) ⊆ I := Icc_subset_Icc le_rfl (by norm_num)
  have hprefixedge : ∀ t ∈ I, f t ∈ Graph.edgeArc drawing e :=
    fun t ht => him ▸ ⟨t,ht,rfl⟩
  have hnotfar : ∀ t ∈ Icc (0:ℝ) (1/2), f t ≠ w := by
    intro t ht heq
    have ht1 := hi (hAI ht) one_mem_I (heq.trans h1.symm)
    linarith [ht.2]
  have hdisj : Disjoint K (f '' Icc 0 (1/2)) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨t,ht,rfl⟩
    rcases hz with (hzW | hzB) | hzT
    · rcases hD.vertex_mem_edgeArc he hzW.1 (hprefixedge t (hAI ht)) with hzv | hzw
      · exact hzW.2 hzv
      · exact hnotfar t ht hzw
    · obtain ⟨g,hzg⟩ := mem_iUnion.mp hzB
      have hvtx := hD.arcs_meet_at_vertex he.edge_mem g.property.1
        (Ne.symm g.property.2) (hprefixedge t (hAI ht)) hzg
      rcases hD.vertex_mem_edgeArc he hvtx (hprefixedge t (hAI ht)) with hzv | hzw
      · have hng : ¬ G.Inc g.val v := fun h => g.property.2 (hunique _ g.property.1 h)
        exact hD.notMem_edgeArc_of_not_inc g.property.1 he.left_mem hng (hzv ▸ hzg)
      · exact hnotfar t ht hzw
    · obtain ⟨u,hu,heq⟩ := hzT
      have hut := hi (hTI hu) (hAI ht) heq
      linarith [hu.1,ht.2]
  have hbase : f (13/24) ∈ K := Or.inr ⟨13/24,⟨le_rfl,by norm_num⟩,rfl⟩
  have hKsub : K ⊆ Graph.pointSet G drawing := by
    rintro z ((hzW | hzB) | hzT)
    · exact Graph.vertexSet_subset_pointSet hzW.1
    · obtain ⟨g,hzg⟩ := mem_iUnion.mp hzB
      exact Graph.edgeArc_subset_pointSet g.property.1 hzg
    · obtain ⟨t,ht,rfl⟩ := hzT
      exact Graph.edgeArc_subset_pointSet he.edge_mem (hprefixedge t (hTI ht))
  have hPsub : f '' Icc 0 (13/24) ⊆ Graph.pointSet G drawing := by
    rintro z ⟨t,ht,rfl⟩
    exact Graph.edgeArc_subset_pointSet he.edge_mem (hprefixedge t (hPI ht))
  refine ⟨K,(hW.union hB).union hT,hdisj,hbase,?_⟩
  apply Subset.antisymm
  · intro z hz
    rcases hz with hzV | hzE
    · by_cases hzv : z=v
      · subst z
        exact Or.inr ⟨0,⟨le_rfl,by norm_num⟩,h0⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hzV,hzv⟩))
    · obtain ⟨g,hg,hzg⟩ := mem_iUnion₂.mp hzE
      by_cases hge : g=e
      · rw [hge,← him] at hzg
        obtain ⟨t,ht,rfl⟩ := hzg
        by_cases hcut : t ≤ 13/24
        · exact Or.inr ⟨t,⟨ht.1,hcut⟩,rfl⟩
        · exact Or.inl (Or.inr ⟨t,⟨(lt_of_not_ge hcut).le,ht.2⟩,rfl⟩)
      · exact Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨g,hg,hge⟩,hzg⟩)))
  · exact union_subset hKsub hPsub

#print axioms leaf_trace_decomposition
end Nanuq.Pendant
