import OriginalBlob
import NanuqFaithfulSupplierDrawing
import Schoenflies.Graph.TwoConnected

/-! UNCOMPILED own-source adapter. Original edge IDs and original curve traces are
retained. No fixed taxon order, contour, adjacent copies or global NANUQ claim. -/
noncomputable section
namespace Nanuq.RawBlockSupplier
open Nanuq.Source Nanuq.RawBlock G1OuterLabelledMultigraphCurves
open NanuqFaithfulSupplierDrawing
open scoped Graph
variable {V E : Type*} {G : EdgeGraph V E}

/-- Restrict the given continuous drawing, not a redrawing. -/
def blobCurves (D : PlanarCurves G) (b : G.Blob) : PlanarCurves (originalBlob G b) where
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

lemma faithful_link (D : PlanarCurves G) {e : E} {a b : V} (hi : G.Inc e a b) :
    (graph D).IsLink e (vertex D a) (vertex D b) := by
  rcases hi with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact Or.inl ⟨congrArg (vertex D) hs.symm,congrArg (vertex D) ht.symm⟩
  · exact Or.inr ⟨congrArg (vertex D) ht.symm,congrArg (vertex D) hs.symm⟩

lemma faithful_reaches (D : PlanarCurves G) {a b : V}
    (h : G.UReach (fun _ => True) a b) : (graph D).Reaches (vertex D a) (vertex D b) := by
  induction h with
  | refl => exact Graph.Reaches.refl (Set.mem_range_self _)
  | tail _ hs ih =>
    obtain ⟨e,_,hi⟩ := hs
    exact ih.trans (Graph.Reaches.of_isLink (faithful_link D hi))

lemma faithful_delete_reaches (D : PlanarCurves G) {v a b : V}
    (ha : a ≠ v) (h : G.UReach (Avoid G v) a b) :
    ((graph D).deleteVerts {vertex D v}).Reaches (vertex D a) (vertex D b) := by
  induction h with
  | refl =>
    exact Graph.Reaches.refl (Graph.mem_deleteVerts_singleton.mpr
      ⟨Set.mem_range_self _,fun hh => ha (vertex_injective D hh)⟩)
  | tail _ hs ih =>
    obtain ⟨e,he,hi⟩ := hs
    apply ih.trans
    apply Graph.Reaches.of_isLink
    rw [Graph.deleteVerts_isLink]
    refine ⟨faithful_link D hi,?_,?_⟩
    · simp only [Set.mem_singleton_iff]
      intro hh
      have hh' := vertex_injective D hh
      rcases hi with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact he.1 (hs.trans hh')
      · exact he.2 (ht.trans hh')
    · simp only [Set.mem_singleton_iff]
      intro hh
      have hh' := vertex_injective D hh
      rcases hi with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact he.2 (ht.trans hh')
      · exact he.1 (hs.trans hh')

/-- The ≥3 guard is explicit: a bigon is not supplier-two-connected. -/
theorem faithful_two_connected (D : PlanarCurves G)
    (hthree : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hc : ∀ a b, G.UReach (fun _ => True) a b)
    (hdel : ∀ v a b, a ≠ v → b ≠ v → G.UReach (Avoid G v) a b) :
    (graph D).IsTwoConnected := by
  obtain ⟨a,b,c,hab,hac,hbc⟩ := hthree
  have hthree' : (graph D).HasThreeVertices :=
    ⟨vertex D a,Set.mem_range_self _,vertex D b,Set.mem_range_self _,
      vertex D c,Set.mem_range_self _,
      fun h => hab (vertex_injective D h),fun h => hac (vertex_injective D h),
      fun h => hbc (vertex_injective D h)⟩
  refine ⟨hthree',⟨⟨vertex D a,Set.mem_range_self _⟩,?_⟩,?_⟩
  · rintro x ⟨u,rfl⟩ y ⟨w,rfl⟩
    exact faithful_reaches D (hc u w)
  · intro x hx
    obtain ⟨v,rfl⟩ := hx
    obtain ⟨z,hz,hzv,_⟩ := hthree'.exists_ne_ne (vertex D v) (vertex D v)
    refine ⟨⟨z,Graph.mem_deleteVerts_singleton.mpr ⟨hz,hzv⟩⟩,?_⟩
    intro y hy z hz
    obtain ⟨hy,hyv⟩ := Graph.mem_deleteVerts_singleton.mp hy
    obtain ⟨hz,hzv⟩ := Graph.mem_deleteVerts_singleton.mp hz
    obtain ⟨u,rfl⟩ := hy
    obtain ⟨w,rfl⟩ := hz
    have huv : u ≠ v := fun h => hyv (congrArg (vertex D) h)
    have hwv : w ≠ v := fun h => hzv (congrArg (vertex D) h)
    exact faithful_delete_reaches D huv (hdel v u w huv hwv)

/-- Actual raw UNSWITCHED original blob, in the SAME continuous drawing. -/
theorem actual_blob_two_connected [Fintype E] (D : PlanarCurves G)
    (hd : ∀ v, Set.ncard {e | G.source e = v ∨ G.target e = v} ≤ 3)
    (b : G.Blob)
    (hthree : ∃ a c d : BlobVertex G b, a ≠ c ∧ a ≠ d ∧ c ≠ d) :
    (graph (blobCurves D b)).IsTwoConnected := by
  exact faithful_two_connected (blobCurves D b) hthree
    (original_blob_connected G b)
    (fun v a c ha hc => original_blob_delete_vertex_connected G hd b ha hc)

theorem actual_binary_blob_two_connected {X : Type*}
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
    (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
    (hthree : ∃ a c d : BlobVertex N.graph b, a ≠ c ∧ a ≠ d ∧ c ≠ d) :
    (graph (blobCurves D b)).IsTwoConnected :=
  actual_blob_two_connected D (binary_incidence_bound N) b hthree

#print axioms actual_blob_two_connected
#print axioms actual_binary_blob_two_connected
end Nanuq.RawBlockSupplier
