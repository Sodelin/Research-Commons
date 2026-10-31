import OriginalBlobSupplier
import Schoenflies.SourceOverlay

/-! LOCAL UNCOMPILED DRAFT for the actual core use. A side is the ORIGINAL
edge-ID deletion reachability class, never an arbitrary geometric partition. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.CutSideCarrier
open Nanuq.Source G1OuterLabelledMultigraphCurves Set
open NanuqFaithfulSupplierDrawing Nanuq.RawBlockSupplier
open scoped Graph Classical
variable {V E : Type*} (G : EdgeGraph V E)

abbrev SideVertex (k : E) (a : V) := {v : V // G.ReachWithout k a v}
abbrev SideEdge (k : E) (a : V) := {e : E // e ≠ k ∧ G.ReachWithout k a (G.source e)}

def sideGraph (k : E) (a : V) : EdgeGraph (SideVertex G k a) (SideEdge G k a) where
  source e := ⟨G.source e.val,e.property.2⟩
  target e := ⟨G.target e.val,e.property.2.tail ⟨e.val,e.property.1,Or.inl ⟨rfl,rfl⟩⟩⟩

/-- Every intermediate original vertex stays in its actual deletion class. -/
theorem side_walk_lift (k : E) (a : V) {u v : V}
    (h : G.ReachWithout k u v) : ∀ hu : G.ReachWithout k a u,
    ∀ hv : G.ReachWithout k a v,
    (sideGraph G k a).UReach (fun _ => True) ⟨u,hu⟩ ⟨v,hv⟩ := by
  induction h with
  | refl => intro hu hv; exact .refl
  | @tail v w hp hs ih =>
    intro hu hw
    have hv : G.ReachWithout k a v := hu.trans hp
    have hi := ih hu hv
    obtain ⟨e,he,hinc⟩ := hs
    have hsrc : G.ReachWithout k a (G.source e) := by
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · rw [hs]; exact hv
      · rw [hs]; exact hw
    apply hi.tail
    refine ⟨⟨e,he,hsrc⟩,True.intro,?_⟩
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨Subtype.ext hs,Subtype.ext ht⟩
    · exact Or.inr ⟨Subtype.ext hs,Subtype.ext ht⟩

theorem side_connected (k : E) (a : V) (u v : SideVertex G k a) :
    (sideGraph G k a).UReach (fun _ => True) u v :=
  side_walk_lift G k a ((G.ureach_symm u.property).trans v.property) u.property v.property

/-- Restriction of the SAME original curves with original retained IDs. -/
def sideCurves (D : PlanarCurves G) (k : E) (a : V) : PlanarCurves (sideGraph G k a) where
  point v := D.point v.val
  point_injective := fun _ _ h => Subtype.ext (D.point_injective h)
  arc e := D.arc e.val
  arc_injective e := D.arc_injective e.val
  vertex_incidence e v t h := by
    rcases D.vertex_incidence e.val v.val t h with hs | ht
    · exact Or.inl (Subtype.ext hs)
    · exact Or.inr (Subtype.ext ht)
  edge_incidence e f hef t u h :=
    D.edge_incidence e.val f.val (fun hh => hef (Subtype.ext hh)) t u h

lemma sideCurves_subset (D : PlanarCurves G) (k : E) (a : V) :
    drawing (sideCurves G D k a) ⊆ drawing D := by
  rintro z (⟨v,rfl⟩ | hz)
  · exact Or.inl ⟨v.val,rfl⟩
  · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨e.val,t,rfl⟩)

/-- A source vertex belongs to the side drawing iff it belongs to the actual
cut class. No geometric connected-component assumption is used. -/
theorem point_mem_side_iff (D : PlanarCurves G) (k : E) (a v : V) :
    D.point v ∈ drawing (sideCurves G D k a) ↔ G.ReachWithout k a v := by
  constructor
  · rintro (⟨w,hw⟩ | hz)
    · have hv := D.point_injective hw
      exact hv ▸ w.property
    · obtain ⟨e,t,ht⟩ := Set.mem_iUnion.mp hz
      rcases D.vertex_incidence e.val v t ht with hs | ht
      · rw [hs]
        exact e.property.2
      · rw [ht]
        exact ((sideGraph G k a).target e).property
  · intro hv
    exact Or.inl ⟨⟨v,hv⟩,rfl⟩

/-- Any point of a retained edge found in a side forces that edge's source
into the side. Endpoint intersections are explicitly included. -/
theorem side_of_edge_point (D : PlanarCurves G) (k : E) (a : V)
    (e : E) (he : e ≠ k) (t : unitInterval)
    (hz : D.arc e t ∈ drawing (sideCurves G D k a)) :
    G.ReachWithout k a (G.source e) := by
  have at_endpoint : t = 0 ∨ t = 1 → G.ReachWithout k a (G.source e) := by
    rintro (rfl | rfl)
    · exact (point_mem_side_iff G D k a (G.source e)).mp (by simpa using hz)
    · have ht := (point_mem_side_iff G D k a (G.target e)).mp (by simpa using hz)
      exact ht.tail ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  rcases hz with ⟨v,hv⟩ | hz
  · rcases D.vertex_incidence e v.val t hv.symm with hs | ht
    · exact hs ▸ v.property
    · have hw : G.ReachWithout k a (G.target e) := ht ▸ v.property
      exact hw.tail ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  · obtain ⟨f,u,hf⟩ := Set.mem_iUnion.mp hz
    by_cases hef : e = f.val
    · simpa only [hef] using f.property.2
    · exact at_endpoint (D.edge_incidence e f.val hef t u hf.symm).1

/-- Distinct original deletion classes have genuinely disjoint geometric
carriers, including all vertex and endpoint cases. -/
theorem side_drawings_disjoint (D : PlanarCurves G) (k : E) (a c : V)
    (hac : ¬ G.ReachWithout k a c) :
    Disjoint (drawing (sideCurves G D k a)) (drawing (sideCurves G D k c)) := by
  apply Set.disjoint_left.mpr
  intro z ha hc
  rcases ha with ⟨v,rfl⟩ | ha
  · have hcv := (point_mem_side_iff G D k c v.val).mp hc
    exact hac (v.property.trans (G.ureach_symm hcv))
  · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp ha
    have hce := side_of_edge_point G D k c e.val e.property.1 t hc
    exact hac (e.property.2.trans (G.ureach_symm hce))

/-- Plane-coordinate carrier for direct use with the supplier's Jordan disk. -/
def carrier (D : PlanarCurves G) (k : E) (a : V) : Set Schoenflies.Plane :=
  Graph.pointSet (graph (sideCurves G D k a)) (curve (sideCurves G D k a))

/-- Exact membership for queried original vertex occurrences. -/
theorem point_mem_carrier_iff (D : PlanarCurves G) (k : E) (a v : V) :
    coordinates (D.point v) ∈ carrier G D k a ↔ G.ReachWithout k a v := by
  rw [carrier,pointSet_eq]
  constructor
  · rintro ⟨z,hz,he⟩
    have he' : z = D.point v := coordinates.injective he
    exact (point_mem_side_iff G D k a v).mp (he' ▸ hz)
  · intro h
    exact ⟨D.point v,(point_mem_side_iff G D k a v).mpr h,rfl⟩

theorem carrier_subset (D : PlanarCurves G) (k : E) (a : V) :
    carrier G D k a ⊆ coordinates '' drawing D := by
  rw [carrier,pointSet_eq]
  exact Set.image_mono (sideCurves_subset G D k a)

theorem carrier_connected (D : PlanarCurves G) (k : E) (a : V) :
    IsConnected (carrier G D k a) := by
  have hc : (graph (sideCurves G D k a)).Connected := by
    refine ⟨⟨vertex (sideCurves G D k a) ⟨a,.refl⟩,Set.mem_range_self _⟩,?_⟩
    rintro x ⟨u,rfl⟩ y ⟨v,rfl⟩
    exact faithful_reaches (sideCurves G D k a) (side_connected G k a u v)
  exact Schoenflies.Graph.IsDrawing.isConnected_pointSet
    (isDrawing (sideCurves G D k a)) hc

theorem carrier_compact [Finite V] [Finite E] (D : PlanarCurves G) (k : E) (a : V) :
    IsCompact (carrier G D k a) := by
  haveI : Finite (SideVertex G k a) := by unfold SideVertex; infer_instance
  haveI : Finite (SideEdge G k a) := by unfold SideEdge; infer_instance
  exact (isDrawing (sideCurves G D k a)).isCompact_pointSet

theorem carriers_disjoint (D : PlanarCurves G) (k : E) (a c : V)
    (hac : ¬ G.ReachWithout k a c) :
    Disjoint (carrier G D k a) (carrier G D k c) := by
  apply Set.disjoint_left.mpr
  intro z ha hc
  rw [carrier,pointSet_eq] at ha hc
  obtain ⟨u,hu,huz⟩ := ha
  obtain ⟨v,hv,hvz⟩ := hc
  have huv := coordinates.injective (huz.trans hvz.symm)
  subst v
  exact Set.disjoint_left.mp (side_drawings_disjoint G D k a c hac) hu hv

#print axioms carrier_connected
#print axioms carrier_compact
#print axioms carriers_disjoint
end Nanuq.CutSideCarrier
