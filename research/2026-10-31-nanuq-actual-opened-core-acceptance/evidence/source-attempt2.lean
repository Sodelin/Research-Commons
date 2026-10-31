import NanuqActualOpenedRootedAdmission

/-! WORKING SOURCE-ONLY DRAFT. Literal raw opened core of the ACTUAL rooted
blob cap. Existing rooted GalledDetour is explicit; canonical arbitrary
semidirected input identification remains a separate admission obligation.
No switching cap, drawing/order certificate or endpoint-pair edge quotient. -/
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (b : N.graph.Blob)

abbrev CoreInner := {v : N.OriginalBlobVertex b // ¬N.graph.IsHybrid v.val}
abbrev CoreTip := {e : N.OriginalBlobArc b // N.graph.IsHybrid (N.graph.target e.val)}
abbrev CoreVertex := Sum (CoreInner N b) (CoreTip N b)

/-- Internal original IDs cannot leave a hybrid, since its child is a bridge. -/
theorem internal_source_nonhybrid (hg : N.graph.GalledDetour) (e : N.OriginalBlobArc b) :
    ¬N.graph.IsHybrid (N.graph.source e.val) := by
  intro hh
  exact N.graph.bridge_blob_ne (N.actual_galled_hybrid_child_is_bridge hg e.val hh)
    (e.property.1.trans e.property.2.symm)

def coreGraph (hg : N.graph.GalledDetour) : EdgeGraph (CoreVertex N b) (N.OriginalBlobArc b) where
  source e := Sum.inl ⟨⟨N.graph.source e.val,e.property.1⟩,internal_source_nonhybrid N b hg e⟩
  target e := if ht : N.graph.IsHybrid (N.graph.target e.val)
    then Sum.inr ⟨e,ht⟩ else Sum.inl ⟨⟨N.graph.target e.val,e.property.2⟩,ht⟩

variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "hl" => N.actual_admitted_cap_hybrid_child_is_taxon hg b hb
local notation "OG" => (M).openedHybridGraph hl

include hg in
/-- In the actual cap, inner skeleton vertices are exactly nonhybrid raw
vertices. Hybrid child taxa are port tips, never inner raw vertices. -/
theorem inner_skeleton_iff (v : N.OriginalBlobVertex b) :
    (M).SkeletonVertexPredicate (Sum.inl v) ↔ ¬N.graph.IsHybrid v.val := by
  constructor
  · intro hv hh
    exact hv.1 ((N.actual_rooted_cap_inner_hybrid_iff b v).mpr hh)
  · intro hv
    refine ⟨fun hh => hv ((N.actual_rooted_cap_inner_hybrid_iff b v).mp hh),?_⟩
    intro e he hh
    obtain ⟨p,hp⟩ := hl e hh
    have hbad : (Sum.inl v : N.RootedCapVertex b)=Sum.inr (Sum.inl p) := he.symm.trans hp
    cases hbad

/-- Literal lift of a retained inner vertex or incoming EDGE occurrence. -/
def coreLift : CoreVertex N b → (M).OpenedHybridVertex
  | Sum.inl v => Sum.inl ⟨Sum.inl v.val,(inner_skeleton_iff N b hg hb v.val).mpr v.property⟩
  | Sum.inr e => Sum.inr ⟨Sum.inl e.val,
      (N.actual_rooted_cap_inner_hybrid_iff b ⟨N.graph.target e.val.val,e.val.property.2⟩).mpr e.property⟩

/-- Every raw original edge is retained ONCE in the actual opened cap,
with only a hybrid endpoint replaced by its exact edge-occurrence tip. -/
def coreEdgeLift (e : N.OriginalBlobArc b) : (M).OpenedHybridEdge :=
  if ht : N.graph.IsHybrid (N.graph.target e.val) then
    Sum.inr ⟨Sum.inl e,(N.actual_rooted_cap_inner_hybrid_iff b
      ⟨N.graph.target e.val,e.property.2⟩).mpr ht⟩
  else Sum.inl ⟨Sum.inl e,
    (inner_skeleton_iff N b hg hb ⟨N.graph.source e.val,e.property.1⟩).mpr
      (internal_source_nonhybrid N b hg e),
    (inner_skeleton_iff N b hg hb ⟨N.graph.target e.val,e.property.2⟩).mpr ht⟩

theorem coreEdgeLift_source (e : N.OriginalBlobArc b) :
    (OG).source (coreEdgeLift N b hg hb e)=coreLift N b hg hb ((coreGraph N b hg).source e) := by
  unfold coreEdgeLift
  split <;> rfl

theorem coreEdgeLift_target (e : N.OriginalBlobArc b) :
    (OG).target (coreEdgeLift N b hg hb e)=coreLift N b hg hb ((coreGraph N b hg).target e) := by
  by_cases ht : N.graph.IsHybrid (N.graph.target e.val) <;>
    simp [coreEdgeLift,coreGraph,coreLift,ht]

theorem coreEdgeLift_original (e : N.OriginalBlobArc b) :
    (M).openedOriginalEdge (coreEdgeLift N b hg hb e)=Sum.inl e := by
  unfold coreEdgeLift
  split <;> rfl

theorem coreEdgeLift_injective : Function.Injective (coreEdgeLift N b hg hb) := by
  intro e f he
  have h := congrArg (M).openedOriginalEdge he
  rw [coreEdgeLift_original,coreEdgeLift_original] at h
  exact Sum.inl.inj h

/-- Core walks lift through the SAME IDs. This direction uses no arbitrary
choice of switching, child order or drawing. -/
theorem core_cut_walk_lifts (k : N.OriginalBlobArc b) {a c : CoreVertex N b}
    (h : (coreGraph N b hg).ReachWithout k a c) :
    (OG).ReachWithout (coreEdgeLift N b hg hb k) (coreLift N b hg hb a) (coreLift N b hg hb c) := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨e,hek,hi⟩ := hs
    apply ih.tail
    refine ⟨coreEdgeLift N b hg hb e,fun he => hek (coreEdgeLift_injective N b hg hb he),?_⟩
    rcases hi with ⟨hes,het⟩ | ⟨hes,het⟩
    · exact Or.inl ⟨(coreEdgeLift_source N b hg hb e).trans (congrArg (coreLift N b hg hb) hes),
        (coreEdgeLift_target N b hg hb e).trans (congrArg (coreLift N b hg hb) het)⟩
    · exact Or.inr ⟨(coreEdgeLift_source N b hg hb e).trans (congrArg (coreLift N b hg hb) hes),
        (coreEdgeLift_target N b hg hb e).trans (congrArg (coreLift N b hg hb) het)⟩

/-- A retained ordinary port is attached at a nonhybrid. Incoming ports
use the actual bridge-entry theorem, not a chosen geometric convention. -/
theorem retained_port_inner_nonhybrid (p : N.BlobPort b)
    (hv : (M).SkeletonVertexPredicate (Sum.inr (Sum.inl p))) :
    ¬N.graph.IsHybrid (N.originalPortInner b p).val := by
  by_cases hp : N.graph.bridgeQuotient.source p.val=b
  · intro hh
    apply hv.2 (Sum.inr (Sum.inl p)) rfl
    change (N.actualRootedCapGraph b).IsHybrid
      ((N.actualRootedCapGraph b).source (Sum.inr (Sum.inl p)))
    simp only [RootedBinary.actualRootedCapGraph,hp,if_pos]
    exact (N.actual_rooted_cap_inner_hybrid_iff b (N.originalPortInner b p)).mpr hh
  · rw [N.originalPortInner_value_incoming b p (p.property.resolve_left hp)]
    exact GProgram.G6.BridgeEntry.original_bridge_target_not_hybrid N p.val.property

def collapseSkeleton (v : (M).SkeletonVertex) : CoreInner N b := by
  rcases v with ⟨v | (p | r),hv⟩
  · exact ⟨v,(inner_skeleton_iff N b hg hb v).mp hv⟩
  · exact ⟨N.originalPortInner b p,retained_port_inner_nonhybrid N b hb p hv⟩
  · exact ⟨N.originalRootedCapEntry b,N.originalRootedCapEntry_nonroot_not_hybrid b r.property⟩

/-- A hybrid incoming cap occurrence is necessarily an ORIGINAL INTERNAL
edge. Neither port-leaf edges nor the incoming fresh-root stem can qualify. -/
def occurrenceRaw (e : (M).HybridParentOccurrence) : CoreTip N b := by
  rcases e with ⟨e | (p | r),hh⟩
  · exact ⟨e,(N.actual_rooted_cap_inner_hybrid_iff b
      ⟨N.graph.target e.val,e.property.2⟩).mp hh⟩
  · have h2 := hh.1
    have h1 := (N.actual_rooted_cap_port_degrees b p).1
    change (N.actualRootedCapGraph b).inDegree (Sum.inr (Sum.inl p))=2 at h2
    omega
  · exact False.elim (N.originalRootedCapEntry_nonroot_not_hybrid b r.property
      ((N.actual_rooted_cap_inner_hybrid_iff b (N.originalRootedCapEntry b)).mp hh))

def collapse : (M).OpenedHybridVertex → CoreVertex N b :=
  Sum.elim (fun v => Sum.inl (collapseSkeleton N b hg hb v))
    (fun e => Sum.inr (occurrenceRaw N b hb e))

theorem collapse_coreLift (v : CoreVertex N b) :
    collapse N b hg hb (coreLift N b hg hb v)=v := by
  rcases v with v | e <;> rfl

theorem core_edge_collapsed_source (e : N.OriginalBlobArc b) :
    collapse N b hg hb ((OG).source (coreEdgeLift N b hg hb e))=(coreGraph N b hg).source e := by
  rw [coreEdgeLift_source,collapse_coreLift]

theorem core_edge_collapsed_target (e : N.OriginalBlobArc b) :
    collapse N b hg hb ((OG).target (coreEdgeLift N b hg hb e))=(coreGraph N b hg).target e := by
  rw [coreEdgeLift_target,collapse_coreLift]

theorem opened_original_injective : Function.Injective (M).openedOriginalEdge := by
  intro f g he
  rcases f with f | f <;> rcases g with g | g
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact False.elim (f.property.2.1 (he.symm ▸ g.property))
  · exact False.elim (g.property.2.1 (he ▸ f.property))
  · exact congrArg Sum.inr (Subtype.ext he)

theorem occurrenceRaw_original (e : (M).HybridParentOccurrence) :
    Sum.inl (occurrenceRaw N b hb e).val=e.val := by
  rcases e with ⟨e | (p | r),hh⟩
  · rfl
  · have h2 := hh.1
    have h1 := (N.actual_rooted_cap_port_degrees b p).1
    change (N.actualRootedCapGraph b).inDegree (Sum.inr (Sum.inl p))=2 at h2
    omega
  · exact False.elim (N.originalRootedCapEntry_nonroot_not_hybrid b r.property
      ((N.actual_rooted_cap_inner_hybrid_iff b (N.originalRootedCapEntry b)).mp hh))

/-- Every ACTUAL opened edge is either the lift of the same raw internal
ID or is contracted to one attachment. Both root-chain pieces are included. -/
theorem opened_edge_core_or_constant (f : (M).OpenedHybridEdge) :
    (∃ e : N.OriginalBlobArc b, f=coreEdgeLift N b hg hb e) ∨
      collapse N b hg hb ((OG).source f)=collapse N b hg hb ((OG).target f) := by
  rcases f with ⟨e | (p | r),hs,ht⟩ | e
  · left
    refine ⟨e,opened_original_injective N b hb ?_⟩
    exact (coreEdgeLift_original N b hg hb e).symm
  · right
    by_cases hp : N.graph.bridgeQuotient.source p.val=b
    · simp [collapse,collapseSkeleton,RootedBinary.openedHybridGraph,
        RootedBinary.rootSkeletonGraph,RootedBinary.actualRootedCapGraph,hp]
    · have hpt := p.property.resolve_left hp
      have hr : b≠N.graph.blobOf N.root := by
        intro heq
        exact N.original_root_blob_has_no_incoming_port p.val (hpt.trans heq)
      have hi : N.originalIncomingBlobPort b hr=p :=
        N.original_incoming_port_unique b _ p (N.originalIncomingBlobPort_target b hr) hpt
      simp [collapse,collapseSkeleton,RootedBinary.openedHybridGraph,
        RootedBinary.rootSkeletonGraph,RootedBinary.actualRootedCapGraph,hp,
        RootedBinary.actualRootedCapRoot,hr,RootedBinary.originalRootedCapEntry,hi]
  · right
    simp [collapse,collapseSkeleton,RootedBinary.openedHybridGraph,
      RootedBinary.rootSkeletonGraph,RootedBinary.actualRootedCapGraph,
      RootedBinary.actualRootedCapRoot,r.property]
  · left
    refine ⟨(occurrenceRaw N b hb e).val,opened_original_injective N b hb ?_⟩
    change e.val=(M).openedOriginalEdge (coreEdgeLift N b hg hb (occurrenceRaw N b hb e).val)
    rw [coreEdgeLift_original]
    exact (occurrenceRaw_original N b hb e).symm

/-- Forward contraction preserves every original internal forbidden ID. -/
theorem opened_cut_walk_collapses (k : N.OriginalBlobArc b) {a c : (M).OpenedHybridVertex}
    (h : (OG).ReachWithout (coreEdgeLift N b hg hb k) a c) :
    (coreGraph N b hg).ReachWithout k (collapse N b hg hb a) (collapse N b hg hb c) := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨f,hfk,hi⟩ := hs
    rcases opened_edge_core_or_constant N b hg hb f with ⟨e,rfl⟩ | heq
    · apply ih.tail
      refine ⟨e,fun hek => hfk (congrArg (coreEdgeLift N b hg hb) hek),?_⟩
      rcases hi with ⟨hsrc,htgt⟩ | ⟨hsrc,htgt⟩
      · exact Or.inl ⟨(core_edge_collapsed_source N b hg hb e).symm.trans
          (congrArg (collapse N b hg hb) hsrc),
          (core_edge_collapsed_target N b hg hb e).symm.trans
          (congrArg (collapse N b hg hb) htgt)⟩
      · exact Or.inr ⟨(core_edge_collapsed_source N b hg hb e).symm.trans
          (congrArg (collapse N b hg hb) hsrc),
          (core_edge_collapsed_target N b hg hb e).symm.trans
          (congrArg (collapse N b hg hb) htgt)⟩
    · have hvw : collapse N b hg hb v=collapse N b hg hb w := by
        rcases hi with ⟨hsrc,htgt⟩ | ⟨hsrc,htgt⟩
        · exact (congrArg (collapse N b hg hb) hsrc).symm.trans
            (heq.trans (congrArg (collapse N b hg hb) htgt))
        · exact (congrArg (collapse N b hg hb) htgt).symm.trans
            (heq.symm.trans (congrArg (collapse N b hg hb) hsrc))
      simpa only [hvw] using ih

theorem openedOutEdge_target_skeleton (e : N.RootedCapArc b)
    (hs : (M).SkeletonVertexPredicate ((M).graph.source e))
    (ht : (M).SkeletonVertexPredicate ((M).graph.target e)) :
    (OG).target ((M).openedOutEdge e hs)=Sum.inl ⟨(M).graph.target e,ht⟩ := by
  simp only [RootedBinary.openedOutEdge,dif_neg ht.1]
  rfl

/-- A discarded cap edge is traversable without ANY retained raw ID.
The source and target skeleton facts are proved at its actual use sites. -/
theorem discarded_edge_step (k : N.OriginalBlobArc b) (e : N.RootedCapArc b)
    (hne : ∀ a : N.OriginalBlobArc b, e≠Sum.inl a)
    (hs : (M).SkeletonVertexPredicate ((M).graph.source e))
    (ht : (M).SkeletonVertexPredicate ((M).graph.target e)) :
    (OG).ReachWithout (coreEdgeLift N b hg hb k)
      (Sum.inl ⟨(M).graph.source e,hs⟩) (Sum.inl ⟨(M).graph.target e,ht⟩) := by
  apply Relation.ReflTransGen.single
  refine ⟨(M).openedOutEdge e hs,?_,Or.inl
    ⟨(M).openedOutEdge_source hl e hs,openedOutEdge_target_skeleton N b hg hb e hs ht⟩⟩
  intro he
  have he' := congrArg (M).openedOriginalEdge he
  rw [(M).openedOutEdge_original,coreEdgeLift_original] at he'
  exact hne k he'

/-- Fresh root to the SAME original entry is the second incoming chain
piece. It is not silently omitted in the cap-to-core contraction. -/
theorem fresh_root_fibre_walk (k : N.OriginalBlobArc b) (r : N.RootedCapRootTag b)
    (hv : (M).SkeletonVertexPredicate (Sum.inr (Sum.inr r))) :
    (OG).ReachWithout (coreEdgeLift N b hg hb k)
      (Sum.inl ⟨Sum.inr (Sum.inr r),hv⟩)
      (coreLift N b hg hb (Sum.inl ⟨N.originalRootedCapEntry b,
        N.originalRootedCapEntry_nonroot_not_hybrid b r.property⟩)) := by
  let e : N.RootedCapArc b := Sum.inr (Sum.inr r)
  have hs : (M).SkeletonVertexPredicate ((M).graph.source e) := by
    simpa [e,RootedBinary.actualRootedCapGraph,RootedBinary.actualRootedCapRoot,r.property] using hv
  have ht : (M).SkeletonVertexPredicate ((M).graph.target e) :=
    (inner_skeleton_iff N b hg hb (N.originalRootedCapEntry b)).mpr
      (N.originalRootedCapEntry_nonroot_not_hybrid b r.property)
  have hw := discarded_edge_step N b hg hb k e (fun a he => by cases he) hs ht
  simpa [e,coreLift,RootedBinary.actualRootedCapGraph,
    RootedBinary.actualRootedCapRoot,r.property] using hw

/-- Ordinary port to its raw attachment. Incoming ports use BOTH actual
edges tip -> fresh root -> entry, not a one-edge surrogate. -/
theorem port_fibre_walk (k : N.OriginalBlobArc b) (p : N.BlobPort b)
    (hv : (M).SkeletonVertexPredicate (Sum.inr (Sum.inl p))) :
    (OG).ReachWithout (coreEdgeLift N b hg hb k)
      (Sum.inl ⟨Sum.inr (Sum.inl p),hv⟩)
      (coreLift N b hg hb (Sum.inl ⟨N.originalPortInner b p,
        retained_port_inner_nonhybrid N b hb p hv⟩)) := by
  let e : N.RootedCapArc b := Sum.inr (Sum.inl p)
  have ht : (M).SkeletonVertexPredicate ((M).graph.target e) := hv
  have hs := (M).skeleton_predicate_parent hl e ht
  have hw := (OG).ureach_symm (discarded_edge_step N b hg hb k e (fun a he => by cases he) hs ht)
  by_cases hp : N.graph.bridgeQuotient.source p.val=b
  · simpa [e,coreLift,RootedBinary.actualRootedCapGraph,hp] using hw
  · have hpt := p.property.resolve_left hp
    have hr : b≠N.graph.blobOf N.root := by
      intro heq
      exact N.original_root_blob_has_no_incoming_port p.val (hpt.trans heq)
    let r : N.RootedCapRootTag b := ⟨(),hr⟩
    have hroot : (M).SkeletonVertexPredicate (Sum.inr (Sum.inr r)) := by
      simpa [e,r,RootedBinary.actualRootedCapGraph,hp,RootedBinary.actualRootedCapRoot,hr] using hs
    have hw1 : (OG).ReachWithout (coreEdgeLift N b hg hb k)
        (Sum.inl ⟨Sum.inr (Sum.inl p),hv⟩) (Sum.inl ⟨Sum.inr (Sum.inr r),hroot⟩) := by
      simpa [e,r,RootedBinary.actualRootedCapGraph,hp,RootedBinary.actualRootedCapRoot,hr] using hw
    have hw2 := fresh_root_fibre_walk N b hg hb k r hroot
    have hi : N.originalIncomingBlobPort b hr=p :=
      N.original_incoming_port_unique b _ p (N.originalIncomingBlobPort_target b hr) hpt
    have hentry : N.originalRootedCapEntry b=N.originalPortInner b p := by
      simp [RootedBinary.originalRootedCapEntry,hr,hi]
    simpa [hentry] using hw1.trans hw2

/-- Every actual opened vertex joins its canonical core lift through only
its literal contracted fibre, avoiding every original retained core edge. -/
theorem collapse_fibre_walk (k : N.OriginalBlobArc b) (v : (M).OpenedHybridVertex) :
    (OG).ReachWithout (coreEdgeLift N b hg hb k) v
      (coreLift N b hg hb (collapse N b hg hb v)) := by
  rcases v with ⟨v | (p | r),hv⟩ | e
  · exact .refl
  · exact port_fibre_walk N b hg hb k p hv
  · exact fresh_root_fibre_walk N b hg hb k r hv
  · rcases e with ⟨e | (p | r),hh⟩
    · exact .refl
    · have h2 := hh.1
      have h1 := (N.actual_rooted_cap_port_degrees b p).1
      change (N.actualRootedCapGraph b).inDegree (Sum.inr (Sum.inl p))=2 at h2
      omega
    · exact False.elim (N.originalRootedCapEntry_nonroot_not_hybrid b r.property
        ((N.actual_rooted_cap_inner_hybrid_iff b (N.originalRootedCapEntry b)).mp hh))

/-- EXACT original-ID cut-side correspondence for the actual opened cap.
Not a switching-cap analogue and not an averaged quartet identity. -/
theorem actual_opened_core_cut_iff (k : N.OriginalBlobArc b) (a c : (M).OpenedHybridVertex) :
    (OG).ReachWithout (coreEdgeLift N b hg hb k) a c ↔
      (coreGraph N b hg).ReachWithout k (collapse N b hg hb a) (collapse N b hg hb c) := by
  constructor
  · exact opened_cut_walk_collapses N b hg hb k
  · intro h
    exact (collapse_fibre_walk N b hg hb k a).trans
      ((core_cut_walk_lifts N b hg hb k h).trans
        ((OG).ureach_symm (collapse_fibre_walk N b hg hb k c)))
end Nanuq.OpenedCore
