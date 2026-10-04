import G1SharpCoreCombOuterOrder
import G1ConvexOriginalEdgeDrawing

/-! The constructed ALL-n family has an actual straight-line outer drawing.
Original edges are real Euclidean segments. Distinct edges meet only at a
shared original endpoint, no other vertex lies on a segment, and each
vertex has a downward ray avoiding the entire drawing and unbounded in y.
This supplies the outer-face admission rather than adding it to raw binary
graph hypotheses. Every original component port is included in the drawing. -/
namespace G1SharpCoreCombOuterEmbedding
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombOuterOrder G1ConvexOriginalEdgeDrawing
open scoped Classical

def drawing (n : Nat) (v : Vertex n) : ℝ × ℝ := parabola (outerIndex n v)

theorem actual_drawing_injective (n : Nat) (hn : 4 ≤ n) : Function.Injective (drawing n) := by
  intro v w he
  have hx := congrArg Prod.fst he
  change (outerIndex n v : ℝ) = outerIndex n w at hx
  apply outerIndex_injective n hn
  exact_mod_cast hx

lemma actual_original_segment_sorted (n : Nat) (hn : 4 ≤ n) (e : Edge n) :
    segment ℝ (drawing n ((graph n).source e)) (drawing n ((graph n).target e)) =
      segment ℝ (parabola (edgeLower n e)) (parabola (edgeUpper n e)) := by
  rcases original_endpoints_in_outer_order n hn e with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · simp only [drawing,hs,ht]
  · simp only [drawing,hs,ht]
    exact segment_symm ℝ _ _

lemma actual_endpoint_lookup (n : Nat) (hn : 4 ≤ n) (e : Edge n) (p : ℝ × ℝ)
    (hp : p = parabola (edgeLower n e) ∨ p = parabola (edgeUpper n e)) :
    ∃ v : Vertex n, (v = (graph n).source e ∨ v = (graph n).target e) ∧ drawing n v = p := by
  rcases original_endpoints_in_outer_order n hn e with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rcases hp with hp | hp
    · exact ⟨(graph n).source e,Or.inl rfl,by simpa only [drawing,hs] using hp.symm⟩
    · exact ⟨(graph n).target e,Or.inr rfl,by simpa only [drawing,ht] using hp.symm⟩
  · rcases hp with hp | hp
    · exact ⟨(graph n).target e,Or.inr rfl,by simpa only [drawing,ht] using hp.symm⟩
    · exact ⟨(graph n).source e,Or.inl rfl,by simpa only [drawing,hs] using hp.symm⟩

theorem actual_original_segments_do_not_cross (n : Nat) (hn : 4 ≤ n) (e f : Edge n)
    (hne : e ≠ f) (p : ℝ × ℝ)
    (hp : p ∈ segment ℝ (drawing n ((graph n).source e)) (drawing n ((graph n).target e)))
    (hq : p ∈ segment ℝ (drawing n ((graph n).source f)) (drawing n ((graph n).target f))) :
    ∃ v : Vertex n, (v = (graph n).source e ∨ v = (graph n).target e) ∧
      (v = (graph n).source f ∨ v = (graph n).target f) ∧ drawing n v = p := by
  rw [actual_original_segment_sorted n hn e] at hp
  rw [actual_original_segment_sorted n hn f] at hq
  have hel : (edgeLower n e : ℝ) < edgeUpper n e := by exact_mod_cast original_interval_strict n hn e
  have hfl : (edgeLower n f : ℝ) < edgeUpper n f := by exact_mod_cast original_interval_strict n hn f
  have hd : (edgeLower n e : ℝ) ≠ edgeLower n f ∨ (edgeUpper n e : ℝ) ≠ edgeUpper n f := by
    by_contra h
    push_neg at h
    apply hne
    apply original_interval_identity n hn e f
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hlam : (edgeUpper n e : ℝ) ≤ edgeLower n f ∨ (edgeUpper n f : ℝ) ≤ edgeLower n e ∨
      ((edgeLower n e : ℝ) ≤ edgeLower n f ∧ (edgeUpper n f : ℝ) ≤ edgeUpper n e) ∨
      ((edgeLower n f : ℝ) ≤ edgeLower n e ∧ (edgeUpper n e : ℝ) ≤ edgeUpper n f) := by
    exact_mod_cast original_intervals_laminar n hn e f
  have hends := laminar_actual_segments_intersect_only_at_endpoints
    (edgeLower n e) (edgeUpper n e) (edgeLower n f) (edgeUpper n f) hel hfl hd hlam p hp hq
  obtain ⟨v,hve,hvp⟩ := actual_endpoint_lookup n hn e p hends.1
  obtain ⟨w,hwf,hwp⟩ := actual_endpoint_lookup n hn f p hends.2
  have hvw := actual_drawing_injective n hn (hvp.trans hwp.symm)
  subst w
  exact ⟨v,hve,hwf,hvp⟩

theorem original_vertices_only_meet_incident_segments (n : Nat) (hn : 4 ≤ n)
    (v : Vertex n) (e : Edge n)
    (hp : drawing n v ∈ segment ℝ (drawing n ((graph n).source e)) (drawing n ((graph n).target e))) :
    v = (graph n).source e ∨ v = (graph n).target e := by
  have h := parabola_point_on_actual_segment_is_endpoint
    (outerIndex n v) (outerIndex n ((graph n).source e)) (outerIndex n ((graph n).target e)) hp
  rcases h with h | h
  · exact Or.inl (outerIndex_injective n hn (by exact_mod_cast h))
  · exact Or.inr (outerIndex_injective n hn (by exact_mod_cast h))

theorem every_original_vertex_has_unbounded_outer_ray (n : Nat) (hn : 4 ≤ n) (v : Vertex n) :
    (∀ s : ℝ, 0 < s → ∀ e : Edge n,
      outerRay (outerIndex n v) s ∉
        segment ℝ (drawing n ((graph n).source e)) (drawing n ((graph n).target e))) ∧
    (∀ height : ℝ, ∃ s : ℝ, 0 < s ∧ (outerRay (outerIndex n v) s).2 < height) := by
  constructor
  · intro s hs e
    exact unbounded_outer_ray_avoids_every_actual_segment
      (outerIndex n v) (outerIndex n ((graph n).source e)) (outerIndex n ((graph n).target e)) s hs
  · intro height
    let y : ℝ := (outerIndex n v : ℝ)^2
    refine ⟨max 0 (y-height)+1,?_,?_⟩
    · have h := le_max_left (0:ℝ) (y-height)
      linarith
    · have h := le_max_right (0:ℝ) (y-height)
      change y-(max 0 (y-height)+1) < height
      linarith

theorem actual_common_unbounded_outer_corridor (n : Nat) (x : ℝ) (e : Edge n) :
    (x,(-1:ℝ)) ∉ segment ℝ (drawing n ((graph n).source e)) (drawing n ((graph n).target e)) := by
  intro hp
  have hh := entire_actual_segment_above_tangent 0
    (outerIndex n ((graph n).source e)) (outerIndex n ((graph n).target e)) (x,-1) hp
  norm_num [tangentHeight] at hh

theorem actual_outer_ray_reaches_common_corridor (n : Nat) (v : Vertex n) :
    ∃ s : ℝ, 0 < s ∧ outerRay (outerIndex n v) s = ((drawing n v).1,-1) := by
  refine ⟨(outerIndex n v : ℝ)^2+1,?_,?_⟩
  · nlinarith [sq_nonneg (outerIndex n v : ℝ)]
  · apply Prod.ext
    · rfl
    · change (outerIndex n v : ℝ)^2-((outerIndex n v : ℝ)^2+1) = -1
      ring

/-- An explicit geometric certificate for original edges and vertex access
to the unbounded face. The concrete theorem below CONSTRUCTS every field. -/
structure OriginalOuterEmbedding {V E : Type*} (G : EdgeGraph V E) where
  point : V → ℝ × ℝ
  injective : Function.Injective point
  edge_intersections : ∀ e f, e ≠ f → ∀ p,
    p ∈ segment ℝ (point (G.source e)) (point (G.target e)) →
    p ∈ segment ℝ (point (G.source f)) (point (G.target f)) →
    ∃ v, (v = G.source e ∨ v = G.target e) ∧ (v = G.source f ∨ v = G.target f) ∧ point v = p
  vertex_incidence : ∀ v e,
    point v ∈ segment ℝ (point (G.source e)) (point (G.target e)) → v = G.source e ∨ v = G.target e
  outer_ray : ∀ v, (∀ s : ℝ, 0 < s → ∀ e,
    ((point v).1,(point v).2-s) ∉ segment ℝ (point (G.source e)) (point (G.target e))) ∧
    (∀ height : ℝ, ∃ s : ℝ, 0 < s ∧ (point v).2-s < height)
  common_outer_corridor : ∀ x : ℝ, ∀ e,
    (x,(-1:ℝ)) ∉ segment ℝ (point (G.source e)) (point (G.target e))
  ray_reaches_corridor : ∀ v, ∃ s : ℝ, 0 < s ∧ ((point v).1,(point v).2-s) = ((point v).1,-1)

def actual_outer_embedding (n : Nat) (hn : 4 ≤ n) : OriginalOuterEmbedding (graph n) where
  point := drawing n
  injective := actual_drawing_injective n hn
  edge_intersections := actual_original_segments_do_not_cross n hn
  vertex_incidence := original_vertices_only_meet_incident_segments n hn
  outer_ray := every_original_vertex_has_unbounded_outer_ray n hn
  common_outer_corridor := actual_common_unbounded_outer_corridor n
  ray_reaches_corridor := actual_outer_ray_reaches_common_corridor n

#print axioms actual_outer_embedding
end G1SharpCoreCombOuterEmbedding
