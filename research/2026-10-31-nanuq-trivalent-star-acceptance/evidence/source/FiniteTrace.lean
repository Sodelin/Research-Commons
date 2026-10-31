import OriginalThreeFrame

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualStar
open Set Schoenflies unitInterval
open scoped Graph

/-- All discarded pieces of the ACTUAL finite drawing form a compact set
away from v. Incident IDs are exhaustively enumerated, not quotiented. -/
theorem finite_discarded_trace {E : Type*} {G : Graph Plane E} [G.Finite]
    {drawing : E → ℝ → Plane} (hD : G.IsDrawing drawing)
    (es : Fin 3 → E) (ws : Fin 3 → Plane) (v : Plane)
    (hinc : ∀ i, G.IsLink (es i) v (ws i))
    (hcover : ∀ e ∈ E(G), G.Inc e v → ∃ i, es i = e)
    (f : Fin 3 → ℝ → Plane)
    (hf : ∀ i, ContinuousOn (f i) I ∧ InjOn (f i) I ∧
      f i '' I = Graph.edgeArc drawing (es i) ∧ f i 0 = v ∧ f i 1 = ws i)
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i ∧ a i ≤ 1) :
    ∃ K : Set Plane, IsCompact K ∧ v ∉ K ∧
      Graph.pointSet G drawing = K ∪ ⋃ i, f i '' Icc 0 (a i) := by
  let J : Set E := {e | e ∈ E(G) ∧ ¬ G.Inc e v}
  have hJfin : J.Finite := (Graph.finite_edgeSet G).subset (fun _ he => he.1)
  letI : Finite J := Set.finite_coe_iff.mpr hJfin
  let B := ⋃ e : J, Graph.edgeArc drawing e.val
  let T := ⋃ i : Fin 3, f i '' Icc (a i) 1
  let W := V(G) \ {v}
  let K := (W ∪ B) ∪ T
  have hW : IsCompact W := ((Graph.finite_vertexSet G).subset sdiff_subset).isCompact
  have hB : IsCompact B := isCompact_iUnion (fun e : J => hD.isCompact_edgeArc e.property.1)
  have hT : IsCompact T := isCompact_iUnion (fun i : Fin 3 =>
    isCompact_Icc.image_of_continuousOn ((hf i).1.mono (Icc_subset_Icc (ha i).1.le le_rfl)))
  have hvG : v ∈ V(G) := (hinc 0).left_mem
  have hvK : v ∉ K := by
    rintro ((hvW | hvB) | hvT)
    · exact hvW.2 rfl
    · obtain ⟨e,he⟩ := mem_iUnion.mp hvB
      exact hD.notMem_edgeArc_of_not_inc e.property.1 hvG e.property.2 he
    · obtain ⟨i,t,ht,he⟩ := mem_iUnion.mp hvT
      have htI : t ∈ I := ⟨(ha i).1.le.trans ht.1,ht.2⟩
      have ht0 : t = 0 := (hf i).2.1 htI zero_mem_I (he.trans (hf i).2.2.2.1.symm)
      linarith [(ha i).1,ht.1]
  have hprefix : (⋃ i, f i '' Icc 0 (a i)) ⊆ Graph.pointSet G drawing := by
    intro z hz
    obtain ⟨i,t,ht,rfl⟩ := mem_iUnion.mp hz
    apply Graph.edgeArc_subset_pointSet (hinc i).edge_mem
    rw [← (hf i).2.2.1]
    exact ⟨t,⟨ht.1,ht.2.trans (ha i).2⟩,rfl⟩
  have hKsub : K ⊆ Graph.pointSet G drawing := by
    rintro z ((hzW | hzB) | hzT)
    · exact Graph.vertexSet_subset_pointSet hzW.1
    · obtain ⟨e,he⟩ := mem_iUnion.mp hzB
      exact Graph.edgeArc_subset_pointSet e.property.1 he
    · obtain ⟨i,t,ht,rfl⟩ := mem_iUnion.mp hzT
      apply Graph.edgeArc_subset_pointSet (hinc i).edge_mem
      rw [← (hf i).2.2.1]
      exact ⟨t,⟨(ha i).1.le.trans ht.1,ht.2⟩,rfl⟩
  refine ⟨K,(hW.union hB).union hT,hvK,?_⟩
  apply Subset.antisymm
  · intro z hz
    rcases hz with hzV | hzE
    · by_cases hzv : z = v
      · subst z
        right
        apply mem_iUnion.mpr
        exact ⟨0,0,⟨le_rfl,(ha 0).1.le⟩,(hf 0).2.2.2.1⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hzV,hzv⟩))
    · obtain ⟨e,he,hze⟩ := mem_iUnion₂.mp hzE
      by_cases hei : G.Inc e v
      · obtain ⟨i,hei'⟩ := hcover e he hei
        rw [← hei',← (hf i).2.2.1] at hze
        obtain ⟨t,ht,rfl⟩ := hze
        by_cases hta : t ≤ a i
        · exact Or.inr (mem_iUnion.mpr ⟨i,t,⟨ht.1,hta⟩,rfl⟩)
        · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i,t,⟨(lt_of_not_ge hta).le,ht.2⟩,rfl⟩))
      · exact Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨e,he,hei⟩,hze⟩)))
  · exact union_subset hKsub hprefix

#print axioms finite_discarded_trace
end Nanuq.ActualStar
