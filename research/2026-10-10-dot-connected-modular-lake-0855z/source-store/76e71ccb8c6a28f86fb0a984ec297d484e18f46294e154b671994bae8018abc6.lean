import G1OriginalClassSameCoreAssembly
import G1AllNActualOuterSourceSharpness
import Mathlib.Analysis.Convex.PathConnected

/-! Convert the ALREADY CHECKED stronger all-n original straight-segment
certificate into faithful curved multigraph data on the SAME original graph.
This does not impose straightness/all-vertices-outer on the master class. -/
namespace G1SharpOriginalSegmentsToFaithfulCurves
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1SharpCoreCombOuterEmbedding
open G1OuterLabelledMultigraphCurves Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def originalSegmentCurves (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph) :
    PlanarCurves N.graph where
  point := D.point
  point_injective := D.injective
  arc e := Path.segment (D.point (N.graph.source e)) (D.point (N.graph.target e))
  arc_injective e := Path.segment_injective_of_ne (fun he =>
    N.graph.acyclic_no_loop N.acyclic e (D.injective he))
  vertex_incidence e v t he := by
    apply D.vertex_incidence v e
    rw [← Path.range_segment]
    exact ⟨t,he⟩
  edge_incidence e f hdiff t u he := by
    let first := Path.segment (D.point (N.graph.source e)) (D.point (N.graph.target e))
    let last := Path.segment (D.point (N.graph.source f)) (D.point (N.graph.target f))
    have hfirst : first t ∈ segment ℝ (D.point (N.graph.source e)) (D.point (N.graph.target e)) := by
      rw [← Path.range_segment]; exact mem_range_self t
    have hlast : first t ∈ segment ℝ (D.point (N.graph.source f)) (D.point (N.graph.target f)) := by
      rw [← Path.range_segment]; exact ⟨u,he.symm⟩
    obtain ⟨v,hve,hvf,hvp⟩ := D.edge_intersections e f hdiff _ hfirst hlast
    have hi := Path.segment_injective_of_ne (fun hh => N.graph.acyclic_no_loop N.acyclic e (D.injective hh))
    have hj := Path.segment_injective_of_ne (fun hh => N.graph.acyclic_no_loop N.acyclic f (D.injective hh))
    constructor
    · rcases hve with hs | ht
      · exact Or.inl (hi (hvp.symm.trans ((congrArg D.point hs).trans first.source.symm)))
      · exact Or.inr (hi (hvp.symm.trans ((congrArg D.point ht).trans first.target.symm)))
    · rcases hvf with hs | ht
      · exact Or.inl (hj (he.symm.trans (hvp.symm.trans ((congrArg D.point hs).trans last.source.symm))))
      · exact Or.inr (hj (he.symm.trans (hvp.symm.trans ((congrArg D.point ht).trans last.target.symm))))

/-- Every original vertex is actually incident; original isolated points
cannot obstruct the common outer corridor without appearing on an edge. -/
lemma actual_vertex_is_incident (N : RootedBinary V E X) (v : V) :
    ∃ e : E, N.graph.source e = v ∨ N.graph.target e = v := by
  rcases Relation.ReflTransGen.cases_tail (N.rooted v) with he | ⟨a,ha,e,hs,ht⟩
  · exact ⟨(actualRootPorts N).first,Or.inl ((actualRootPorts N).source_first.trans he.symm)⟩
  · exact ⟨e,Or.inr ht⟩

theorem actual_segment_curve_drawing (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph) :
    G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D) =
      range D.point ∪ ⋃ e : E, segment ℝ (D.point (N.graph.source e)) (D.point (N.graph.target e)) := by
  unfold G1OuterLabelledMultigraphCurves.drawing
  congr 1
  apply iUnion_congr
  intro e
  exact Path.range_segment _ _

lemma actual_corridor_misses_full_drawing (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph) (x : ℝ) :
    (x,(-1:ℝ)) ∉ G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D) := by
  rw [actual_segment_curve_drawing]
  rintro (⟨v,hv⟩ | he)
  · obtain ⟨e,hs | ht⟩ := actual_vertex_is_incident N v
    · apply D.common_outer_corridor x e
      rw [← hv,← hs]
      exact left_mem_segment ℝ _ _
    · apply D.common_outer_corridor x e
      rw [← hv,← ht]
      exact right_mem_segment ℝ _ _
  · obtain ⟨e,he⟩ := mem_iUnion.mp he
    exact D.common_outer_corridor x e he

lemma actual_downward_ray_misses_full_drawing (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph)
    (v : V) (s : ℝ) (hs : 0 < s) :
    ((D.point v).1,(D.point v).2-s) ∉ G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D) := by
  rw [actual_segment_curve_drawing]
  rintro (⟨w,hw⟩ | he)
  · obtain ⟨e,hsource | htarget⟩ := actual_vertex_is_incident N w
    · apply (D.outer_ray v).1 s hs e
      rw [← hw,← hsource]
      exact left_mem_segment ℝ _ _
    · apply (D.outer_ray v).1 s hs e
      rw [← hw,← htarget]
      exact right_mem_segment ℝ _ _
  · obtain ⟨e,he⟩ := mem_iUnion.mp he
    exact (D.outer_ray v).1 s hs e he

#print axioms originalSegmentCurves
end G1SharpOriginalSegmentsToFaithfulCurves
