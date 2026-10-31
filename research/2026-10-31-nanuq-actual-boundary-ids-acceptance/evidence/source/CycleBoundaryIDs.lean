import Schoenflies.CrosscutExists
import Schoenflies.Graph.CycleJordan

/-! SOURCE-ONLY DRAFT, UNCOMPILED. Keep original multigraph edge IDs.
The two-edge bigon is admitted; a loop is excluded by the actual drawing. -/
namespace Nanuq.OpenedCore
open Set Schoenflies
open scoped Graph
variable {E : Type*} {G : Graph Plane E} {drawing : E → ℝ → Plane}

private theorem cycle_start_two {e : E} {u v : Plane} {D : List E}
    (hc : G.IsCycleThrough e u v D) (hne : u≠v) :
    ∃ f g : E, f≠g ∧ f∈e::D ∧ g∈e::D ∧ G.Inc f u ∧ G.Inc g u := by
  cases D with
  | nil =>
    cases hc.isPath
    exact False.elim (hne rfl)
  | cons g R =>
    cases hp : hc.isPath with
    | cons hl ht hfresh =>
      refine ⟨e,g,?_,List.mem_cons_self,List.mem_cons_of_mem _ List.mem_cons_self,
        hc.isLink.inc_left,hl.inc_left⟩
      intro heq
      subst g
      exact hc.notMem List.mem_cons_self

/-- A vertex on this particular drawn cycle has TWO distinct incident IDs
on this same cycle, not merely in the surrounding graph. -/
theorem cycle_two_incident_ids
    (hd : Graph.IsDrawing G drawing) {e : E} {u v z : Plane} {D : List E}
    (hc : G.IsCycleThrough e u v D) (hz : z∈V(G))
    (hcover : z∈Graph.edgesCover drawing (e::D)) :
    ∃ f g : E, f≠g ∧ f∈e::D ∧ g∈e::D ∧ G.Inc f z ∧ G.Inc g z := by
  obtain ⟨k,hk,hzk⟩ := Graph.mem_edgesCover_iff.mp hcover
  obtain ⟨a,b,W,hrot,hperm⟩ := hc.rotate hk
  have hab : a≠b := hd.ne_of_isLink hrot.isLink
  have hzab : z=a ∨ z=b := hd.vertex_mem_edgeArc hrot.isLink hz hzk
  rcases hzab with hza | hzb
  · subst z
    obtain ⟨f,g,hfg,hf,hg,hfi,hgi⟩ := cycle_start_two hrot hab
    exact ⟨f,g,hfg,hperm.mem_iff.mp hf,hperm.mem_iff.mp hg,hfi,hgi⟩
  · subst z
    have hreverse : G.IsCycleThrough k b a W.reverse :=
      ⟨hrot.isLink.symm,hrot.isPath.reverse,by simpa using hrot.notMem⟩
    obtain ⟨f,g,hfg,hf,hg,hfi,hgi⟩ := cycle_start_two hreverse hab.symm
    have hf' : f∈k::W := by simpa using hf
    have hg' : g∈k::W := by simpa using hg
    exact ⟨f,g,hfg,hperm.mem_iff.mp hf',hperm.mem_iff.mp hg',hfi,hgi⟩

/-- If the source proves that EXACTLY two possible IDs are incident at a
vertex, the particular boundary cycle must use both of them. The actual raw
hybrid specialization must derive this exhaustion, never assume it as an
extra original-network condition. -/
theorem cycle_contains_both_incident_ids
    (hd : Graph.IsDrawing G drawing) {e e₁ e₂ : E} {u v z : Plane} {D : List E}
    (hc : G.IsCycleThrough e u v D) (hz : z∈V(G))
    (hcover : z∈Graph.edgesCover drawing (e::D))
    (hexhaust : ∀ f, G.Inc f z → f=e₁ ∨ f=e₂) :
    e₁∈e::D ∧ e₂∈e::D := by
  obtain ⟨f,g,hfg,hf,hg,hfi,hgi⟩ := cycle_two_incident_ids hd hc hz hcover
  rcases hexhaust f hfi with hf1 | hf2 <;>
    rcases hexhaust g hgi with hg1 | hg2
  · exact False.elim (hfg (hf1.trans hg1.symm))
  · exact ⟨hf1 ▸ hf,hg2 ▸ hg⟩
  · exact ⟨hg1 ▸ hg,hf2 ▸ hf⟩
  · exact False.elim (hfg (hf2.trans hg2.symm))
end Nanuq.OpenedCore
