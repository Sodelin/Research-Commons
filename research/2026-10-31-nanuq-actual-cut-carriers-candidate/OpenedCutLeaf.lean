import NanuqActualOpenedBinaryDegrees
import SourceQuartetRelation

/-! SOURCE-ONLY DRAFT, UNCOMPILED. A prerequisite in the actual opened-cap
cut-side contraction, not the contraction or geometric order theorem. -/
namespace Nanuq.Source.EdgeGraph
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Deleting the unique edge into a terminal vertex isolates that vertex. -/
theorem terminal_cut_walk_constant (G : EdgeGraph V E)
    (hin : G.UniqueIncoming) (e : E) (hout : G.outDegree (G.target e)=0)
    {v : V} (h : G.ReachWithout e (G.target e) v) : v=G.target e := by
  induction h with
  | refl => rfl
  | @tail v w hp hs ih =>
    obtain ⟨f,hfe,hinc⟩ := hs
    rcases hinc with ⟨hsource,htarget⟩ | ⟨hsource,htarget⟩
    · exact False.elim (G.no_edge_source_of_outdegree_zero hout f (hsource.trans ih))
    · exact False.elim (hfe (hin f e (htarget.trans ih)))

/-- A genuine two-tip target side cannot be separated by a terminal edge. -/
theorem terminal_oriented_quartet_false (G : EdgeGraph V E)
    (hin : G.UniqueIncoming) (e : E) (hout : G.outDegree (G.target e)=0)
    {a b c d : V} (hcd : c≠d) (h : G.OrientedQuartet e a b c d) : False := by
  exact hcd ((G.terminal_cut_walk_constant hin e hout h.2.2.1).trans
    (G.terminal_cut_walk_constant hin e hout h.2.2.2).symm)

/-- Removing one root branch when the other is a single leaf leaves only
the root and that leaf. This tracks the incoming cap's TWO-edge chain. -/
theorem root_leaf_branch_cut_walk (G : EdgeGraph V E)
    (hin : G.UniqueIncoming) (f k : E) (r l : V)
    (hkr : G.source k=r) (hkl : G.target k=l)
    (hroot : ∀ e, G.target e≠r)
    (hexhaust : ∀ e, G.source e=r → e=f ∨ e=k)
    (hleaf : G.outDegree l=0)
    {v : V} (h : G.ReachWithout f r v) : v=r ∨ v=l := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail v w hp hs ih =>
    obtain ⟨e,hef,hi⟩ := hs
    rcases ih with hvr | hvl
    · rcases hi with ⟨hes,het⟩ | ⟨hes,het⟩
      · rcases hexhaust e (hes.trans hvr) with he | he
        · exact False.elim (hef he)
        · subst e
          exact Or.inr (het.symm.trans hkl)
      · exact False.elim (hroot e (het.trans hvr))
    · rcases hi with ⟨hes,het⟩ | ⟨hes,het⟩
      · exact False.elim (G.no_edge_source_of_outdegree_zero hleaf e (hes.trans hvl))
      · have hek : e=k := hin e k ((het.trans hvl).trans hkl.symm)
        subst e
        exact Or.inl (hes.symm.trans hkr)

/-- The fresh root plus its one ordinary port tip cannot contain two
DISTINCT nonroot queried tips after the stem is cut. -/
theorem root_leaf_branch_oriented_quartet_false (G : EdgeGraph V E)
    (hin : G.UniqueIncoming) (f k : E) (r l : V)
    (hfr : G.source f=r) (hkr : G.source k=r) (hkl : G.target k=l)
    (hroot : ∀ e, G.target e≠r)
    (hexhaust : ∀ e, G.source e=r → e=f ∨ e=k)
    (hleaf : G.outDegree l=0)
    {a b c d : V} (hab : a≠b) (har : a≠r) (hbr : b≠r)
    (h : G.OrientedQuartet f a b c d) : False := by
  have ha := G.root_leaf_branch_cut_walk hin f k r l hkr hkl hroot hexhaust hleaf
    (hfr ▸ h.1)
  have hb := G.root_leaf_branch_cut_walk hin f k r l hkr hkl hroot hexhaust hleaf
    (hfr ▸ h.2.1)
  exact hab ((ha.resolve_left har).trans (hb.resolve_left hbr).symm)
end Nanuq.Source.EdgeGraph

namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e=N.leaf x)

/-- Every nontrivial oriented opened-tree cut retains a skeleton original ID;
none is one of the distinct hybrid-parent occurrence pendant edges. -/
theorem opened_nontrivial_cut_skeleton
    (f : N.OpenedHybridEdge) {a b c d : N.OpenedHybridVertex}
    (hcd : c≠d) (h : (N.openedHybridGraph hleaf).OrientedQuartet f a b c d) :
    ∃ e : N.SkeletonEdge, f=Sum.inl e := by
  rcases f with e | e
  · exact ⟨e,rfl⟩
  · exact False.elim ((N.openedHybridGraph hleaf).terminal_oriented_quartet_false
      (N.opened_hybrid_uniqueIncoming hleaf) (Sum.inr e)
      (N.opened_new_tip_degrees hleaf e).2 hcd h)

/-- Neither an ordinary port leaf nor a duplicated hybrid tip can be the
terminal target of a nontrivial queried cut. The exact tip occurrence is kept. -/
theorem opened_nontrivial_cut_target_not_tip
    (f : N.OpenedHybridEdge) {a b c d : N.OpenedHybridVertex}
    (hcd : c≠d) (h : (N.openedHybridGraph hleaf).OrientedQuartet f a b c d)
    (t : N.OpenedTip) :
    (N.openedHybridGraph hleaf).target f ≠ N.openedTipVertex t := by
  intro ht
  have hout : (N.openedHybridGraph hleaf).outDegree
      ((N.openedHybridGraph hleaf).target f)=0 := by
    rw [ht]
    exact (N.opened_tip_degrees hleaf t).2
  exact (N.openedHybridGraph hleaf).terminal_oriented_quartet_false
    (N.opened_hybrid_uniqueIncoming hleaf) f hout hcd h
end Nanuq.Source.RootedBinary
