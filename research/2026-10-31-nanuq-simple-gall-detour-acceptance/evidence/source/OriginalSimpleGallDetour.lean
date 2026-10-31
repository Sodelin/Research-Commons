import GraphGalls
import Schoenflies.Graph.Tree

/-!
Source-only candidate: the one needed rooted original-ID simple-cycle direction.
This is NOT the separate lifting of an admitted marked semi-directed cycle through
root suppression. Parallel edge IDs are retained, and a bigon has an empty detour.
Supplier Graph.IsPath/IsCycleThrough semantics are those of Álvaro Begué's
Schoenflies graph library (Apache-2.0), pinned in the dependency manifest.
-/
noncomputable section
namespace Nanuq.SimpleGallAdmission
open Nanuq.Source Set
open scoped Graph
variable {V E : Type*} (G : EdgeGraph V E)

/-- The literal undirected multigraph on the SAME original vertices and edge IDs. -/
def originalGraph : Graph V E where
  vertexSet := univ
  edgeSet := univ
  IsLink := G.Inc
  isLink_symm := by
    intro e _
    constructor
    intro a b h
    exact G.inc_symm h
  eq_or_eq_of_isLink_of_isLink := by
    intro e a b c d h k
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
      rcases k with ⟨hc,hd⟩ | ⟨hc,hd⟩ <;> simp_all
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨_,_,G.inc_source_target e⟩,fun _ => mem_univ _⟩
  left_mem_of_isLink := by
    intro e a b h
    exact mem_univ a

/-- A list walk with an edgewise guard realizes the exact source UReach. -/
theorem original_walk_ureach {a b : V} {W : List E} {keep : E → Prop}
    (hw : (originalGraph G).IsWalk a W b) (hk : ∀ d ∈ W, keep d) :
    G.UReach keep a b := by
  revert hk
  induction hw with
  | nil => intro _; exact .refl
  | @cons a w b e W hl hw ih =>
    intro hk
    exact (G.ureach_single ⟨e,hk e (List.mem_cons_self),hl⟩).trans
      (ih (fun d hd => hk d (List.mem_cons_of_mem _ hd)))

/-- Remove the two specified incoming edges from a literal simple gall.
No distinct-parent assumption: the two-edge bigon leaves the empty tail. -/
theorem incoming_cycle_detour [Fintype E] [DecidableEq V]
    {h : V} {e f : E} {W : List E}
    (he : G.target e=h) (hf : G.target f=h) (hef : e≠f)
    (hc : (originalGraph G).IsCycleThrough e h (G.source e) W)
    (hfm : f ∈ W)
    (hord : ∀ d ∈ e::W, d≠e → d≠f → ¬G.IsHybrid (G.target d)) :
    G.UReach (fun d => ¬G.IsHybrid (G.target d) ∧ G.source d≠h ∧ G.target d≠h)
      (G.source e) (G.source f) := by
  cases W with
  | nil => simp at hfm
  | cons g R =>
    have hfi : (originalGraph G).Inc f h := by
      exact (show (originalGraph G).IsLink f (G.source f) h from
        Or.inl ⟨rfl,hf⟩).inc_right
    have hfg : f=g := hc.isPath.eq_head_of_inc_source hfm hfi
    subst g
    have hfn : f ∉ R := (List.nodup_cons.mp hc.isPath.nodup).1
    cases hp : hc.isPath with
    | @cons h w v f R hl ht hnot =>
      have hw : w=G.source f := by
        change G.Inc f h w at hl
        rcases hl with ⟨hs,htarget⟩ | ⟨hs,htarget⟩
        · exact htarget.symm.trans (hf.trans hs.symm)
        · exact hs.symm
      subst w
      apply G.ureach_symm
      apply original_walk_ureach G ht.isWalk
      intro d hd
      have hde : d≠e := by
        intro hde
        subst d
        exact hc.notMem (List.mem_cons_of_mem _ hd)
      have hdf : d≠f := by
        intro hdf
        subst d
        exact hfn hd
      refine ⟨hord d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)) hde hdf,?_,?_⟩
      · intro hds
        apply hnot
        apply Graph.mem_walkVertices_of_mem_covered
        refine ⟨d,hd,?_⟩
        exact (show (originalGraph G).IsLink d h (G.target d) from
          Or.inl ⟨hds,rfl⟩).inc_left
      · intro hdt
        apply hnot
        apply Graph.mem_walkVertices_of_mem_covered
        refine ⟨d,hd,?_⟩
        exact (show (originalGraph G).IsLink d (G.source d) h from
          Or.inl ⟨rfl,hdt⟩).inc_right

/-- Explicit rooted cycle syntax, NOT a claim that root suppression has been lifted. -/
def RootedSimpleGalls [Fintype E] [DecidableEq V] : Prop :=
  ∀ h, G.IsHybrid h → ∀ e f, e≠f → G.target e=h → G.target f=h →
    ∃ W, (originalGraph G).IsCycleThrough e h (G.source e) W ∧ f∈W ∧
      ∀ d ∈ e::W, d≠e → d≠f → ¬G.IsHybrid (G.target d)

theorem rooted_simple_galls_to_detour [Fintype E] [DecidableEq V]
    (hg : RootedSimpleGalls G) : G.GalledDetour := by
  intro h hh e f hef he hf
  obtain ⟨W,hc,hfm,hord⟩ := hg h hh e f hef he hf
  exact incoming_cycle_detour G he hf hef hc hfm hord

#print axioms incoming_cycle_detour
#print axioms rooted_simple_galls_to_detour
end Nanuq.SimpleGallAdmission
