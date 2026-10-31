import RootedCapMap
import DrawingSides

/-! Working source-bound bridge-side facts. UNCOMPILED. -/
noncomputable section
namespace Nanuq.CapExterior
open Nanuq.Source G1OuterLabelledMultigraphCurves Nanuq.CapCurves Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (b : N.graph.Blob)

def nearSide (p : N.BlobPort b) : Set V :=
  {v | N.graph.ReachWithout p.val.val (N.originalPortInner b p).val v}

def farVertex (p : N.BlobPort b) : V :=
  if N.graph.bridgeQuotient.source p.val = b then N.graph.target p.val.val
  else N.graph.source p.val.val

lemma blob_vertex_near (p : N.BlobPort b) (v : N.OriginalBlobVertex b) :
    v.val ∈ nearSide N b p :=
  N.graph.sameBlob_avoids_bridge p.val.property
    (Quotient.exact ((N.originalPortInner b p).property.trans v.property.symm))

lemma near_closed_other_edge (p : N.BlobPort b) {f : E} (hf : f ≠ p.val.val) :
    N.graph.source f ∈ nearSide N b p ↔ N.graph.target f ∈ nearSide N b p := by
  constructor
  · intro h
    exact h.tail ⟨f,hf,N.graph.inc_source_target f⟩
  · intro h
    exact h.tail ⟨f,hf,N.graph.inc_symm (N.graph.inc_source_target f)⟩

lemma other_port_near (p q : N.BlobPort b) (hpq : q ≠ p) :
    N.graph.source q.val.val ∈ nearSide N b p ∧
    N.graph.target q.val.val ∈ nearSide N b p := by
  have hqp : q.val.val ≠ p.val.val := fun h => hpq (Subtype.ext (Subtype.ext h))
  have hi := blob_vertex_near N b p (N.originalPortInner b q)
  by_cases hq : N.graph.bridgeQuotient.source q.val = b
  · rw [N.originalPortInner_value_outgoing b q hq] at hi
    exact ⟨hi,(near_closed_other_edge N b p hqp).mp hi⟩
  · rw [N.originalPortInner_value_incoming b q (q.property.resolve_left hq)] at hi
    exact ⟨(near_closed_other_edge N b p hqp).mpr hi,hi⟩

lemma far_not_near (p : N.BlobPort b) : farVertex N b p ∉ nearSide N b p := by
  by_cases hp : N.graph.bridgeQuotient.source p.val = b
  · simpa only [farVertex,if_pos hp,nearSide,mem_setOf_eq,
      N.originalPortInner_value_outgoing b p hp,EdgeGraph.IsBridge] using p.val.property
  · intro h
    have h' : N.graph.ReachWithout p.val.val (N.graph.target p.val.val)
        (N.graph.source p.val.val) := by
      simpa only [farVertex,if_neg hp,nearSide,mem_setOf_eq,
        N.originalPortInner_value_incoming b p (p.property.resolve_left hp)] using h
    exact p.val.property (N.graph.ureach_symm h')

lemma far_walk_not_near (p : N.BlobPort b) {v : V}
    (hv : N.graph.ReachWithout p.val.val (farVertex N b p) v) :
    v ∉ nearSide N b p := by
  intro hn
  exact far_not_near N b p (hn.trans (N.graph.ureach_symm hv))

/-- Replace the path keep predicate by its actual far-side endpoint condition.
This is not a switching or a geometric-order certificate. -/
lemma far_walk_internal (p : N.BlobPort b) {v : V}
    (hv : N.graph.ReachWithout p.val.val (farVertex N b p) v) :
    N.graph.UReach (fun f => N.graph.source f ∉ nearSide N b p ∧
      N.graph.target f ∉ nearSide N b p) (farVertex N b p) v := by
  induction hv with
  | refl => exact .refl
  | @tail a c hprev hstep ih =>
    obtain ⟨f,hf,hinc⟩ := hstep
    have ha := far_walk_not_near N b p hprev
    have hc := far_walk_not_near N b p (hprev.tail ⟨f,hf,hinc⟩)
    apply ih.tail
    refine ⟨f,?_,hinc⟩
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact ⟨hs.symm ▸ ha,ht.symm ▸ hc⟩
    · exact ⟨hs.symm ▸ hc,ht.symm ▸ ha⟩

lemma port_fibre_far (hb : N.NonleafBlob b) (p : N.BlobPort b) (x : X)
    (hx : N.blobProjection b hb x = p) :
    N.graph.ReachWithout p.val.val (farVertex N b p) (N.leaf x) := by
  by_cases hp : N.graph.bridgeQuotient.source p.val = b
  · simpa only [farVertex,if_pos hp] using
      (N.blobProjection_eq_iff_target_side b hb x p hp).mp hx
  · simpa only [farVertex,if_neg hp] using
      (N.blobProjection_eq_iff_source_side b hb x p (p.property.resolve_left hp)).mp hx

end Nanuq.CapExterior
