import NanuqActualPortCardinality
import G1OuterLabelledMultigraphCurves
import AffineSubpath

/-! WORKING source-bound cap map, UNCOMPILED.
These are literal formulas, not yet a PlanarCurves provider or an order theorem.
Every added tag lies on its original bridge; internal arcs are unchanged. -/
noncomputable section
namespace Nanuq.CapCurves
open Nanuq.Source G1OuterLabelledMultigraphCurves
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

def oneThird : unitInterval := ⟨1/3, by norm_num⟩
def oneHalf : unitInterval := ⟨1/2, by norm_num⟩
def twoThirds : unitInterval := ⟨2/3, by norm_num⟩

variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

def portParameter (p : N.BlobPort b) : unitInterval :=
  if N.graph.bridgeQuotient.source p.val = b then oneHalf else oneThird

lemma portParameter_interior (p : N.BlobPort b) :
    portParameter N b p ≠ 0 ∧ portParameter N b p ≠ 1 ∧
      portParameter N b p ≠ twoThirds := by
  unfold portParameter
  split <;> constructor
  all_goals try { intro h; have := congrArg Subtype.val h; norm_num [oneHalf,oneThird,twoThirds] at this }
  all_goals constructor <;> intro h <;>
    have := congrArg Subtype.val h <;> norm_num [oneHalf,oneThird,twoThirds] at this

lemma original_interior_not_vertex (e : E) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (v : V) : D.arc e t ≠ D.point v := by
  intro h
  rcases D.vertex_incidence e v t h with hv | hv
  · apply ht0
    apply D.arc_injective e
    exact h.trans ((congrArg D.point hv).trans (D.arc e).source.symm)
  · apply ht1
    apply D.arc_injective e
    exact h.trans ((congrArg D.point hv).trans (D.arc e).target.symm)

lemma original_interior_eq {e f : E} {t u : unitInterval}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (h : D.arc e t = D.arc f u) :
    e = f ∧ t = u := by
  have hef : e = f := by
    by_contra hn
    rcases (D.edge_incidence e f hn t u h).1 with h0 | h1
    · exact ht0 h0
    · exact ht1 h1
  subst f
  exact ⟨rfl,D.arc_injective e h⟩

def capPoint : N.RootedCapVertex b → Plane
  | .inl v => D.point v.val
  | .inr (.inl p) => D.arc p.val.val
      (portParameter N b p)
  | .inr (.inr r) => D.arc (N.originalIncomingBlobPort b r.property).val.val twoThirds

lemma capPoint_injective : Function.Injective (capPoint N D b) := by
  have h20 : twoThirds ≠ (0 : unitInterval) := by
    intro h; have := congrArg Subtype.val h; norm_num [twoThirds] at this
  have h21 : twoThirds ≠ (1 : unitInterval) := by
    intro h; have := congrArg Subtype.val h; norm_num [twoThirds] at this
  intro v w h
  rcases v with v | (p | r) <;> rcases w with w | (q | s)
  · exact congrArg Sum.inl (Subtype.ext (D.point_injective h))
  · exact False.elim (original_interior_not_vertex N D _ _
      (portParameter_interior N b q).1 (portParameter_interior N b q).2.1 v.val h.symm)
  · exact False.elim (original_interior_not_vertex N D _ _ h20 h21 v.val h.symm)
  · exact False.elim (original_interior_not_vertex N D _ _
      (portParameter_interior N b p).1 (portParameter_interior N b p).2.1 w.val h)
  · have he := original_interior_eq N D
      (portParameter_interior N b p).1 (portParameter_interior N b p).2.1 h
    have hpq : p = q := Subtype.ext (Subtype.ext he.1)
    subst q
    rfl
  · have he := original_interior_eq N D
      (portParameter_interior N b p).1 (portParameter_interior N b p).2.1 h
    exact False.elim ((portParameter_interior N b p).2.2 he.2)
  · exact False.elim (original_interior_not_vertex N D _ _ h20 h21 w.val h)
  · have he := original_interior_eq N D h20 h21 h
    exact False.elim ((portParameter_interior N b q).2.2 he.2.symm)
  · have hrs : r = s := Subtype.ext (Subsingleton.elim _ _)
    subst s
    rfl

def capRawArc (e : N.RootedCapArc b) (t : unitInterval) : Plane :=
  match e with
  | .inl e => D.arc e.val t
  | .inr (.inl p) =>
      if N.graph.bridgeQuotient.source p.val = b then
        D.arc p.val.val (affineParameter 0 oneHalf t)
      else D.arc p.val.val (affineParameter twoThirds oneThird t)
  | .inr (.inr r) => D.arc (N.originalIncomingBlobPort b r.property).val.val
      (affineParameter twoThirds 1 t)

lemma incoming_port_nonroot (p : N.BlobPort b)
    (hp : ¬ N.graph.bridgeQuotient.source p.val = b) : b ≠ N.graph.blobOf N.root := by
  intro h
  exact N.original_root_blob_has_no_incoming_port p.val ((p.property.resolve_left hp).trans h)

lemma incoming_port_eq (p : N.BlobPort b)
    (hp : ¬ N.graph.bridgeQuotient.source p.val = b) :
    p = N.originalIncomingBlobPort b (incoming_port_nonroot N b p hp) :=
  N.original_incoming_port_unique b p _ (p.property.resolve_left hp)
    (N.originalIncomingBlobPort_target b _)

lemma capRawArc_source (e : N.RootedCapArc b) :
    capRawArc N D b e 0 = capPoint N D b ((N.actualRootedCapGraph b).source e) := by
  rcases e with e | (p | r)
  · simp [capRawArc,capPoint,RootedBinary.actualRootedCapGraph]
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · simp [capRawArc,capPoint,RootedBinary.actualRootedCapGraph,hp,
        N.originalPortInner_value_outgoing b p hp]
    · have hn := incoming_port_nonroot N b p hp
      have he := incoming_port_eq N b p hp
      have hp' := N.originalRootedCapIncoming_outside_source b hn
      simp [capRawArc,capPoint,RootedBinary.actualRootedCapGraph,hp,hp',
        RootedBinary.actualRootedCapRoot,hn,he]
      exact congrArg (fun q : N.BlobPort b => D.arc q.val.val twoThirds) he
  · simp [capRawArc,capPoint,RootedBinary.actualRootedCapGraph,
      RootedBinary.actualRootedCapRoot,r.property]

lemma capRawArc_target (e : N.RootedCapArc b) :
    capRawArc N D b e 1 = capPoint N D b ((N.actualRootedCapGraph b).target e) := by
  rcases e with e | (p | r)
  · simp [capRawArc,capPoint,RootedBinary.actualRootedCapGraph]
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b <;>
      simp [capRawArc,capPoint,RootedBinary.actualRootedCapGraph,portParameter,hp]
  · simp [capRawArc,capPoint,RootedBinary.actualRootedCapGraph,
      N.originalRootedCapEntry_nonroot_value b r.property]

lemma capRawArc_continuous (e : N.RootedCapArc b) : Continuous (capRawArc N D b e) := by
  rcases e with e | (p | r)
  · exact (D.arc e.val).continuous
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · change Continuous (capRawArc N D b (.inr (.inl p)))
      have hf : capRawArc N D b (.inr (.inl p)) =
          (fun t => (D.arc p.val.val) (affineParameter 0 oneHalf t)) := by
        funext t
        change (if N.graph.bridgeQuotient.source p.val = b then
          D.arc p.val.val (affineParameter 0 oneHalf t)
          else D.arc p.val.val (affineParameter twoThirds oneThird t)) = _
        exact if_pos hp
      rw [hf]
      exact (D.arc p.val.val).continuous.comp
        (show Continuous (affineParameter 0 oneHalf) from by fun_prop [affineParameter])
    · change Continuous (capRawArc N D b (.inr (.inl p)))
      have hf : capRawArc N D b (.inr (.inl p)) =
          (fun t => (D.arc p.val.val) (affineParameter twoThirds oneThird t)) := by
        funext t
        change (if N.graph.bridgeQuotient.source p.val = b then
          D.arc p.val.val (affineParameter 0 oneHalf t)
          else D.arc p.val.val (affineParameter twoThirds oneThird t)) = _
        exact if_neg hp
      rw [hf]
      exact (D.arc p.val.val).continuous.comp
        (show Continuous (affineParameter twoThirds oneThird) from by fun_prop [affineParameter])
  · exact (D.arc _).continuous.comp (by fun_prop [capRawArc,affineParameter])

def capArc (e : N.RootedCapArc b) :
    Path (capPoint N D b ((N.actualRootedCapGraph b).source e))
      (capPoint N D b ((N.actualRootedCapGraph b).target e)) where
  toFun := capRawArc N D b e
  continuous_toFun := capRawArc_continuous N D b e
  source' := capRawArc_source N D b e
  target' := capRawArc_target N D b e

lemma capArc_injective (e : N.RootedCapArc b) : Function.Injective (capArc N D b e) := by
  rcases e with e | (p | r)
  · exact D.arc_injective e.val
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · change Function.Injective (capRawArc N D b (.inr (.inl p)))
      have hf : capRawArc N D b (.inr (.inl p)) =
          (fun t => (D.arc p.val.val) (affineParameter 0 oneHalf t)) := by
        funext t
        change (if N.graph.bridgeQuotient.source p.val = b then
          D.arc p.val.val (affineParameter 0 oneHalf t)
          else D.arc p.val.val (affineParameter twoThirds oneThird t)) = _
        exact if_pos hp
      rw [hf]
      exact (D.arc_injective p.val.val).comp (affineParameter_injective 0 oneHalf (by
          intro h; have := congrArg Subtype.val h; norm_num [oneHalf] at this))
    · change Function.Injective (capRawArc N D b (.inr (.inl p)))
      have hf : capRawArc N D b (.inr (.inl p)) =
          (fun t => (D.arc p.val.val) (affineParameter twoThirds oneThird t)) := by
        funext t
        change (if N.graph.bridgeQuotient.source p.val = b then
          D.arc p.val.val (affineParameter 0 oneHalf t)
          else D.arc p.val.val (affineParameter twoThirds oneThird t)) = _
        exact if_neg hp
      rw [hf]
      exact (D.arc_injective p.val.val).comp (affineParameter_injective twoThirds oneThird (by
          intro h; have := congrArg Subtype.val h; norm_num [twoThirds,oneThird] at this))
  · exact (D.arc_injective _).comp (affineParameter_injective _ _ (by
      intro h; have := congrArg Subtype.val h; norm_num [twoThirds] at this))

def capCarrier (e : N.RootedCapArc b) : E :=
  match e with
  | .inl e => e.val
  | .inr (.inl p) => p.val.val
  | .inr (.inr r) => (N.originalIncomingBlobPort b r.property).val.val

def capParameter (e : N.RootedCapArc b) (t : unitInterval) : unitInterval :=
  match e with
  | .inl _ => t
  | .inr (.inl p) => if N.graph.bridgeQuotient.source p.val = b then
      affineParameter 0 oneHalf t else affineParameter twoThirds oneThird t
  | .inr (.inr _) => affineParameter twoThirds 1 t

lemma capRawArc_eq (e : N.RootedCapArc b) (t : unitInterval) :
    capRawArc N D b e t = D.arc (capCarrier N b e) (capParameter N b e t) := by
  rcases e with e | (p | r)
  · rfl
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b <;>
      simp [capRawArc,capCarrier,capParameter,hp] <;> rfl
  · rfl

lemma capParameter_interior (e : N.RootedCapArc b) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    capParameter N b e t ≠ 0 ∧ capParameter N b e t ≠ 1 := by
  have ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1 := by
    have h0 : (t:ℝ) ≠ 0 := fun h => ht0 (Subtype.ext h)
    have h1 : (t:ℝ) ≠ 1 := fun h => ht1 (Subtype.ext h)
    exact ⟨lt_of_le_of_ne t.property.1 (Ne.symm h0), lt_of_le_of_ne t.property.2 h1⟩
  rcases e with e | (p | r)
  · exact ⟨ht0,ht1⟩
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b
    all_goals constructor <;> intro h <;> have he := congrArg Subtype.val h
    all_goals simp [capParameter,hp,affineParameter,oneHalf,oneThird,twoThirds] at he
    all_goals first | exact ht0 he | exact ht1 he | linarith [ht.1,ht.2]
  · constructor <;> intro h <;> have he := congrArg Subtype.val h
    all_goals simp [capParameter,affineParameter,twoThirds] at he
    all_goals linarith [ht.1,ht.2]

lemma internal_not_bridge (e : N.OriginalBlobArc b) : ¬ N.graph.IsBridge e.val := by
  intro he
  exact N.graph.bridge_blob_ne he (e.property.1.trans e.property.2.symm)

/-- Two cap segments of the same incoming bridge meet only at the fresh root;
all different original carrier IDs are separated by the original drawing. -/
lemma capArc_interior_disjoint (e f : N.RootedCapArc b) (hef : e ≠ f)
    (t u : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    capRawArc N D b e t ≠ capRawArc N D b f u := by
  intro h
  rw [capRawArc_eq,capRawArc_eq] at h
  have hi := capParameter_interior N b e t ht0 ht1
  obtain ⟨hc,hp⟩ := original_interior_eq N D hi.1 hi.2 h
  have ht : 0 < (t:ℝ) := by
    have hn : (t:ℝ) ≠ 0 := fun h => ht0 (Subtype.ext h)
    exact lt_of_le_of_ne t.property.1 (Ne.symm hn)
  rcases e with e | (p | r) <;> rcases f with f | (q | s)
  · exact hef (congrArg Sum.inl (Subtype.ext hc))
  · apply internal_not_bridge N b e
    have hc' : e.val = q.val.val := hc
    rw [hc']
    exact q.val.property
  · apply internal_not_bridge N b e
    have hc' : e.val = (N.originalIncomingBlobPort b s.property).val.val := hc
    rw [hc']
    exact (N.originalIncomingBlobPort b s.property).val.property
  · apply internal_not_bridge N b f
    have hc' : p.val.val = f.val := hc
    rw [← hc']
    exact p.val.property
  · exact hef (congrArg (fun z => Sum.inr (Sum.inl z)) (Subtype.ext (Subtype.ext hc)))
  · have he : p = N.originalIncomingBlobPort b s.property := Subtype.ext (Subtype.ext hc)
    have hn : ¬ N.graph.bridgeQuotient.source p.val = b := by
      rw [he]
      exact N.originalRootedCapIncoming_outside_source b s.property
    have heq := congrArg Subtype.val hp
    simp [capParameter,hn,affineParameter,oneThird,twoThirds] at heq
    nlinarith [u.property.1]
  · apply internal_not_bridge N b f
    have hc' : (N.originalIncomingBlobPort b r.property).val.val = f.val := hc
    rw [← hc']
    exact (N.originalIncomingBlobPort b r.property).val.property
  · have he : q = N.originalIncomingBlobPort b r.property := Subtype.ext (Subtype.ext hc.symm)
    have hn : ¬ N.graph.bridgeQuotient.source q.val = b := by
      rw [he]
      exact N.originalRootedCapIncoming_outside_source b r.property
    have heq := congrArg Subtype.val hp
    simp [capParameter,hn,affineParameter,oneThird,twoThirds] at heq
    nlinarith [u.property.1]
  · exact hef (congrArg (fun z => Sum.inr (Sum.inr z))
      (Subtype.ext (Subsingleton.elim _ _)))

lemma capArc_edge_incidence (e f : N.RootedCapArc b) (hef : e ≠ f)
    (t u : unitInterval) (h : capArc N D b e t = capArc N D b f u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  constructor
  · by_contra hn
    push_neg at hn
    exact capArc_interior_disjoint N D b e f hef t u hn.1 hn.2 h
  · by_contra hn
    push_neg at hn
    exact capArc_interior_disjoint N D b f e (Ne.symm hef) u t hn.1 hn.2 h.symm

lemma binary_incident_edge {W F Y : Type*} [Fintype W] [Fintype F]
    [Fintype Y] [DecidableEq W] (M : RootedBinary W F Y) (v : W) :
    ∃ e, M.graph.source e = v ∨ M.graph.target e = v := by
  classical
  have hd : 0 < M.graph.inDegree v ∨ 0 < M.graph.outDegree v := by
    by_cases hr : v = M.root
    · subst v
      exact Or.inr (by rw [M.root_degrees.2]; decide)
    by_cases hl : ∃ x, M.leaf x = v
    · obtain ⟨x,rfl⟩ := hl
      exact Or.inl (by rw [(M.leaf_degrees x).1]; decide)
    rcases M.internal_degrees v hr (fun x hx => hl ⟨x,hx⟩) with hi | hi
    · exact Or.inl (by rw [hi.1]; decide)
    · exact Or.inl (by rw [hi.1]; decide)
  rcases hd with hi | ho
  · obtain ⟨e,he⟩ := Finset.card_pos.mp hi
    exact ⟨e,Or.inr (Finset.mem_filter.mp he).2⟩
  · obtain ⟨e,he⟩ := Finset.card_pos.mp ho
    exact ⟨e,Or.inl (Finset.mem_filter.mp he).2⟩

lemma capArc_vertex_incidence (hb : N.NonleafBlob b) (e : N.RootedCapArc b)
    (v : N.RootedCapVertex b) (t : unitInterval)
    (h : capArc N D b e t = capPoint N D b v) :
    v = (N.actualRootedCapGraph b).source e ∨ v = (N.actualRootedCapGraph b).target e := by
  obtain ⟨f,hf⟩ := binary_incident_edge (N.actualEveryNonleafRootedCapSource b hb) v
  have hv : capPoint N D b v = capArc N D b f 0 ∨
      capPoint N D b v = capArc N D b f 1 := by
    rcases hf with hs | ht
    · left
      have hs' : (N.actualRootedCapGraph b).source f = v := hs
      rw [← hs']
      exact (capArc N D b f).source.symm
    · right
      have ht' : (N.actualRootedCapGraph b).target f = v := ht
      rw [← ht']
      exact (capArc N D b f).target.symm
  have ht : t = 0 ∨ t = 1 := by
    rcases hv with hv | hv
    · by_cases he : e = f
      · subst f
        exact Or.inl (capArc_injective N D b e (h.trans hv))
      · exact (capArc_edge_incidence N D b e f he t 0 (h.trans hv)).1
    · by_cases he : e = f
      · subst f
        exact Or.inr (capArc_injective N D b e (h.trans hv))
      · exact (capArc_edge_incidence N D b e f he t 1 (h.trans hv)).1
  rcases ht with rfl | rfl
  · exact Or.inl (capPoint_injective N D b (h.symm.trans (capArc N D b e).source))
  · exact Or.inr (capPoint_injective N D b (h.symm.trans (capArc N D b e).target))

/-- Literal cap of the SAME original drawing; no outer-order or face premise. -/
def actualRootedCapCurves (hb : N.NonleafBlob b) : PlanarCurves (N.actualRootedCapGraph b) where
  point := capPoint N D b
  point_injective := capPoint_injective N D b
  arc := capArc N D b
  arc_injective := capArc_injective N D b
  vertex_incidence := capArc_vertex_incidence N D b hb
  edge_incidence := capArc_edge_incidence N D b

lemma actualRootedCapCurves_drawing_subset (hb : N.NonleafBlob b) :
    drawing (actualRootedCapCurves N D b hb) ⊆ drawing D := by
  intro z hz
  rcases hz with ⟨v,rfl⟩ | hz
  · rcases v with v | (p | r)
    · exact Or.inl ⟨v.val,rfl⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨p.val.val,⟨portParameter N b p,rfl⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr
        ⟨(N.originalIncomingBlobPort b r.property).val.val,⟨twoThirds,rfl⟩⟩)
  · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp hz
    exact Or.inr (Set.mem_iUnion.mpr
      ⟨capCarrier N b e,⟨capParameter N b e t,(capRawArc_eq N D b e t).symm⟩⟩)

#print axioms actualRootedCapCurves
#print axioms actualRootedCapCurves_drawing_subset
-- UNCOMPILED: source candidate only. Does not yet prove cap TaxonOuterFace,
-- original port-order/C compatibility, or any opened-tree contour theorem.
end Nanuq.CapCurves
