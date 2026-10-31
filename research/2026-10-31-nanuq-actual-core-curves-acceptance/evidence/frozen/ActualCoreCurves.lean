import ActualOpenedCore
import RootedCapMap
import OriginalBlobSupplier
import Schoenflies.CrosscutCells

/-! SOURCE DRAFT, UNCOMPILED. Literal prefix realization of the already
qualified original-ID opened core. No redraw or boundary-order certificate. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves Nanuq.CapCurves Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

def corePoint : CoreVertex N b → Plane
  | .inl v => D.point v.val.val
  | .inr e => D.arc e.val.val oneHalf

lemma half_ne_zero : oneHalf ≠ (0 : unitInterval) := by
  intro h; have := congrArg Subtype.val h; norm_num [oneHalf] at this
lemma half_ne_one : oneHalf ≠ (1 : unitInterval) := by
  intro h; have := congrArg Subtype.val h; norm_num [oneHalf] at this

lemma corePoint_injective : Function.Injective (corePoint N D b) := by
  intro v w h
  rcases v with v | e <;> rcases w with w | f
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (D.point_injective h)))
  · exact False.elim (original_interior_not_vertex N D f.val.val oneHalf
      half_ne_zero half_ne_one v.val.val h.symm)
  · exact False.elim (original_interior_not_vertex N D e.val.val oneHalf
      half_ne_zero half_ne_one w.val.val h)
  · have he := (original_interior_eq N D half_ne_zero half_ne_one h).1
    exact congrArg Sum.inr (Subtype.ext (Subtype.ext he))

def coreEnd (e : N.OriginalBlobArc b) : unitInterval :=
  if N.graph.IsHybrid (N.graph.target e.val) then oneHalf else 1

def coreParameter (e : N.OriginalBlobArc b) (t : unitInterval) : unitInterval :=
  affineParameter 0 (coreEnd N b e) t

lemma coreEnd_ne_zero (e : N.OriginalBlobArc b) : coreEnd N b e ≠ 0 := by
  unfold coreEnd
  split
  · exact half_ne_zero
  · norm_num

lemma coreParameter_endpoint (e : N.OriginalBlobArc b) (t : unitInterval)
    (h : coreParameter N b e t = 0 ∨ coreParameter N b e t = 1) :
    t = 0 ∨ t = 1 := by
  by_cases hh : N.graph.IsHybrid (N.graph.target e.val)
  · rcases h with h | h
    · left; apply Subtype.ext
      have he := congrArg Subtype.val h
      norm_num [coreParameter,affineParameter,coreEnd,hh,oneHalf] at he ⊢
      linarith
    · have he := congrArg Subtype.val h
      norm_num [coreParameter,affineParameter,coreEnd,hh,oneHalf] at he
      linarith [t.property.2]
  · have ht : coreParameter N b e t = t := by
      apply Subtype.ext; simp [coreParameter,affineParameter,coreEnd,hh]
    simpa only [ht] using h

def coreRawArc (e : N.OriginalBlobArc b) (t : unitInterval) : Plane :=
  D.arc e.val (coreParameter N b e t)

lemma coreRawArc_source (hg : N.graph.GalledDetour) (e : N.OriginalBlobArc b) :
    coreRawArc N D b e 0 = corePoint N D b ((coreGraph N b hg).source e) := by
  simp [coreRawArc,coreParameter,corePoint,coreGraph]

lemma coreRawArc_target (hg : N.graph.GalledDetour) (e : N.OriginalBlobArc b) :
    coreRawArc N D b e 1 = corePoint N D b ((coreGraph N b hg).target e) := by
  by_cases hh : N.graph.IsHybrid (N.graph.target e.val) <;>
    simp [coreRawArc,coreParameter,coreEnd,corePoint,coreGraph,hh]

def coreArc (hg : N.graph.GalledDetour) (e : N.OriginalBlobArc b) :
    Path (corePoint N D b ((coreGraph N b hg).source e))
      (corePoint N D b ((coreGraph N b hg).target e)) where
  toFun := coreRawArc N D b e
  continuous_toFun := (D.arc e.val).continuous.comp
    (show Continuous (coreParameter N b e) from by fun_prop [coreParameter,affineParameter])
  source' := coreRawArc_source N D b hg e
  target' := coreRawArc_target N D b hg e

lemma coreArc_injective (hg : N.graph.GalledDetour) (e : N.OriginalBlobArc b) :
    Function.Injective (coreArc N D b hg e) :=
  (D.arc_injective e.val).comp (affineParameter_injective 0 (coreEnd N b e)
    (Ne.symm (coreEnd_ne_zero N b e)))

lemma coreArc_edge_incidence (hg : N.graph.GalledDetour)
    (e f : N.OriginalBlobArc b) (hef : e ≠ f) (t u : unitInterval)
    (h : coreArc N D b hg e t = coreArc N D b hg f u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  have hids : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  have hi := D.edge_incidence e.val f.val hids
    (coreParameter N b e t) (coreParameter N b f u) h
  exact ⟨coreParameter_endpoint N b e t hi.1,coreParameter_endpoint N b f u hi.2⟩

lemma coreArc_vertex_incidence (hg : N.graph.GalledDetour)
    (e : N.OriginalBlobArc b) (v : CoreVertex N b) (t : unitInterval)
    (h : coreArc N D b hg e t = corePoint N D b v) :
    v = (coreGraph N b hg).source e ∨ v = (coreGraph N b hg).target e := by
  rcases v with v | f
  · have hi := D.vertex_incidence e.val v.val.val (coreParameter N b e t) h
    rcases hi with hs | ht
    · left
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext hs))
    · right
      have hh : ¬ N.graph.IsHybrid (N.graph.target e.val) := by
        simpa only [← ht] using v.property
      simp only [coreGraph,dif_neg hh]
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext ht))
  · have he : f.val.val = e.val :=
      (original_interior_eq N D half_ne_zero half_ne_one h.symm).1
    have hfe : f.val = e := Subtype.ext he
    have hh : N.graph.IsHybrid (N.graph.target e.val) := hfe ▸ f.property
    right
    simp only [coreGraph,dif_pos hh]
    exact congrArg Sum.inr (Subtype.ext hfe)

/-- Same original vertices, midpoint incoming-occurrence tips, and literal
whole/prefix original arcs. Original parallel IDs are retained. -/
def actualCoreCurves (hg : N.graph.GalledDetour) : PlanarCurves (coreGraph N b hg) where
  point := corePoint N D b
  point_injective := corePoint_injective N D b
  arc := coreArc N D b hg
  arc_injective := coreArc_injective N D b hg
  vertex_incidence := coreArc_vertex_incidence N D b hg
  edge_incidence := coreArc_edge_incidence N D b hg

/-- Every core point and retained arc belongs to the actual RAW blob drawing,
not merely to the full network or to the capped drawing with outside stubs. -/
theorem actualCoreCurves_subset_raw (hg : N.graph.GalledDetour) :
    drawing (actualCoreCurves N D b hg) ⊆ drawing (blobCurves D b) := by
  intro z hz
  rcases hz with ⟨v,rfl⟩ | hz
  · rcases v with v | f
    · exact Or.inl ⟨⟨v.val.val,v.val.property⟩,rfl⟩
    · right
      let g : BlobEdge N.graph b := ⟨f.val.val,internal_not_bridge N b f.val,f.val.property.1⟩
      exact Set.mem_iUnion.mpr ⟨g,oneHalf,rfl⟩
  · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp hz
    right
    let g : BlobEdge N.graph b := ⟨e.val,internal_not_bridge N b e,e.property.1⟩
    exact Set.mem_iUnion.mpr ⟨g,coreParameter N b e t,rfl⟩

/-- Explicit original carrier formula; truncation is by target hybrid status,
not by an unrelated switching choice. -/
theorem actualCoreCurves_arc_formula (hg : N.graph.GalledDetour)
    (e : N.OriginalBlobArc b) (t : unitInterval) :
    (actualCoreCurves N D b hg).arc e t =
      D.arc e.val (affineParameter 0
        (if N.graph.IsHybrid (N.graph.target e.val) then oneHalf else 1) t) := rfl

/-- This equality is the OUTPUT of the accepted raw outer-cycle provider
(and the separately qualifying bigon candidate), not a supplied geometric-order certificate.
It implies closed-disk containment, with no false strict-interior claim. -/
theorem actualCoreCurves_closed_disk (hg : N.graph.GalledDetour)
    (o : Schoenflies.Plane) (C : Set Schoenflies.Plane)
    (hface : Graph.face
      (NanuqFaithfulSupplierDrawing.graph (blobCurves D b))
      (NanuqFaithfulSupplierDrawing.curve (blobCurves D b)) o = Schoenflies.outside C) :
    NanuqFaithfulSupplierDrawing.coordinates '' drawing (actualCoreCurves N D b hg) ⊆
      C ∪ Schoenflies.inside C := by
  rintro z ⟨w,hw,rfl⟩
  have hr := actualCoreCurves_subset_raw N D b hg hw
  have hp : NanuqFaithfulSupplierDrawing.coordinates w ∈ Graph.pointSet
      (NanuqFaithfulSupplierDrawing.graph (blobCurves D b))
      (NanuqFaithfulSupplierDrawing.curve (blobCurves D b)) := by
    rw [NanuqFaithfulSupplierDrawing.pointSet_eq (blobCurves D b)]
    exact ⟨w,hr,rfl⟩
  by_cases hc : NanuqFaithfulSupplierDrawing.coordinates w ∈ C
  · exact Or.inl hc
  · right
    have hi : NanuqFaithfulSupplierDrawing.coordinates w ∈
        Schoenflies.inside C ∪ Schoenflies.outside C := by
      rw [Schoenflies.inside_union_outside]
      exact hc
    rcases hi with hi | ho
    · exact hi
    · rw [← hface] at ho
      exact False.elim ((Graph.face_subset_exterior _ _ _ ho) hp)

#print axioms actualCoreCurves
#print axioms actualCoreCurves_subset_raw
#print axioms actualCoreCurves_closed_disk
#print axioms actualCoreCurves_arc_formula
end Nanuq.OpenedCore
