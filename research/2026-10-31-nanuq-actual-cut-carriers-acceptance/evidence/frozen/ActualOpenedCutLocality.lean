import ActualOpenedCore
import OpenedCutLeaf

/-! UNCOMPILED LOCAL DRAFT. Actual nontrivial quartet cut IDs are retained
core IDs; BOTH discarded incoming root-chain pieces are handled explicitly. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

private theorem two_outgoing_exhaust {W F : Type*} [Fintype F]
    (G : EdgeGraph W F) (r : W) (hd : G.outDegree r = 2)
    (f k : F) (hfk : f≠k) (hf : G.source f=r) (hk : G.source k=r) :
    ∀ e, G.source e=r → e=f ∨ e=k := by
  classical
  obtain ⟨x,y,hxy,hset⟩ := Finset.card_eq_two.mp hd
  have hm : ∀ e, G.source e=r → e=x ∨ e=y := by
    intro e he
    have he' : e ∈ Finset.univ.filter (fun e => G.source e=r) := by simp [he]
    rw [hset] at he'
    simpa using he'
  intro e he
  rcases hm f hf with hfx | hfy <;>
    rcases hm k hk with hkx | hky <;>
    rcases hm e he with hex | hey <;> aesop

variable (N : RootedBinary V E X) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "hl" => N.actual_admitted_cap_hybrid_child_is_taxon hg b hb
local notation "OG" => RootedBinary.openedHybridGraph (N.actualEveryNonleafRootedCapSource b hb) (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)

/-- The actual fresh-root stem cannot support two distinct queried tips on
its root side: the only other root branch is the actual incoming-port leaf. -/
theorem actual_stem_quartet_false (r : N.RootedCapRootTag b)
    (s : (M).SkeletonEdge) (hs : s.val = Sum.inr (Sum.inr r))
    (a c d e : (M).OpenedTip) (hac : a ≠ c)
    (hq : (OG).OrientedQuartet (Sum.inl s)
      ((M).openedTipVertex a) ((M).openedTipVertex c)
      ((M).openedTipVertex d) ((M).openedTipVertex e)) : False := by
  let p := N.originalIncomingBlobPort b r.property
  let pc : N.RootedCapArc b := Sum.inr (Sum.inl p)
  let root := Sum.inl (M).rootSkeletonRoot
  have hps : (M).graph.source pc = (M).root := by
    change (N.actualRootedCapGraph b).source pc = N.actualRootedCapRoot b
    simp [pc,p,RootedBinary.actualRootedCapGraph,
      N.originalRootedCapIncoming_outside_source b r.property]
  have hsp : (M).SkeletonVertexPredicate ((M).graph.source pc) := by
    rw [hps]
    exact (M).root_skeleton_root_predicate
  have htp : (M).SkeletonVertexPredicate ((M).graph.target pc) := by
    apply (M).skeleton_edge_nonhybrid_target pc hsp
    intro hh
    have hd := ((M).leaf_degrees p).1
    have heq : (M).graph.target pc = (M).leaf p := rfl
    rw [← heq] at hd
    have hh2 := hh.1
    omega
  let pt : (M).OrdinaryTaxon := ⟨p,htp⟩
  let k := (M).openedOutEdge pc hsp
  have hfr : (OG).source (Sum.inl s) = root := by
    apply congrArg Sum.inl
    apply Subtype.ext
    change (N.actualRootedCapGraph b).source s.val = N.actualRootedCapRoot b
    rw [hs]
    rfl
  have hkr : (OG).source k = root := by
    rw [(M).openedOutEdge_source hl]
    exact congrArg Sum.inl (Subtype.ext hps)
  have hkl : (OG).target k = (M).openedTipVertex (Sum.inl pt) := by
    exact openedOutEdge_target_skeleton N b hg hb pc hsp htp
  have hfk : (Sum.inl s : (M).OpenedHybridEdge) ≠ k := by
    intro he
    have hid := congrArg (M).openedOriginalEdge he
    change s.val = (M).openedOriginalEdge k at hid
    rw [(M).openedOutEdge_original] at hid
    rw [hs] at hid
    cases hid
  have hroot : ∀ f, (OG).target f ≠ root :=
    ((M).actualOpenedRootedSource hl).edge_target_ne_root
  have hex := two_outgoing_exhaust (OG) root ((M).opened_root_degrees hl).2
    (Sum.inl s) k hfk hfr hkr
  exact (OG).root_leaf_branch_oriented_quartet_false
    ((M).opened_hybrid_uniqueIncoming hl) (Sum.inl s) k root
    ((M).openedTipVertex (Sum.inl pt)) hfr hkr hkl hroot hex
    ((M).opened_tip_degrees hl (Sum.inl pt)).2
    (fun h => hac ((M).openedTipVertex.injective h))
    ((M).opened_tip_ne_root a) ((M).opened_tip_ne_root c) hq

/-- Exact retained-ID locality for actual opened occurrence-tip quartets.
No switching source, assumed core witness, or collapse-only inference. -/
theorem actual_opened_quartet_core_id (f : (M).OpenedHybridEdge)
    (a c d e : (M).OpenedTip) (hac : a ≠ c) (hde : d ≠ e)
    (hq : (OG).OrientedQuartet f
      ((M).openedTipVertex a) ((M).openedTipVertex c)
      ((M).openedTipVertex d) ((M).openedTipVertex e)) :
    ∃ k : N.OriginalBlobArc b, f = coreEdgeLift N b hg hb k := by
  have hde' : (M).openedTipVertex d ≠ (M).openedTipVertex e :=
    fun h => hde ((M).openedTipVertex.injective h)
  obtain ⟨s,rfl⟩ := (M).opened_nontrivial_cut_skeleton hl f hde' hq
  rcases hs : s.val with k | (p | r)
  · refine ⟨k,opened_original_injective N b hb ?_⟩
    change s.val = (M).openedOriginalEdge (coreEdgeLift N b hg hb k)
    rw [coreEdgeLift_original]
    exact hs
  · let pt : (M).OrdinaryTaxon := ⟨p,by
      have ht := s.property.2
      simpa only [hs] using ht⟩
    apply False.elim
    apply (M).opened_nontrivial_cut_target_not_tip hl (Sum.inl s) hde' hq (Sum.inl pt)
    apply congrArg Sum.inl
    apply Subtype.ext
    change (N.actualRootedCapGraph b).target s.val = _
    rw [hs]
    rfl
  · exact False.elim (actual_stem_quartet_false N b hg hb r s hs a c d e hac hq)

#print axioms actual_stem_quartet_false
#print axioms actual_opened_quartet_core_id
end Nanuq.OpenedCore
