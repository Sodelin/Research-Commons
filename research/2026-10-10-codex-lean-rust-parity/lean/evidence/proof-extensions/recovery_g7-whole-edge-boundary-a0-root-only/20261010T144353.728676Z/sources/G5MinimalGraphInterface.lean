import GraphCuts

/-!
# Weaker graph interface isolated by the G5 hypothesis audit

New formal generalization: dot's dedicated Lean lane, 2026-10-01.
Original edge-ID graph API and foundational lemmas retain Samuel attribution.

The bridge/descendant theorem needs only directed rootedness and acyclicity.
No LSA, binary degrees, finite vertex bound, galledness or planar embedding is
assumed. This is a genuine stronger graph statement, not a full biological Q
or split-identification theorem. Finite stochastic route-support, calendar and
chronological lifting obligations remain separate.
-/

namespace GProgram.G5.Minimal

open Nanuq.Source

variable {V E : Type*}

theorem root_source_side_of_rooted_acyclic (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) (e : E) :
    G.ReachWithout e (G.source e) root := by
  apply G.ureach_symm
  apply G.dreach_without_of_no_return e (hr (G.source e))
  intro hreturn
  exact ha (G.source e) (Relation.TransGen.head' ⟨e, rfl, rfl⟩ hreturn)

/-- Actual directed bridge components equal actual directed descendants on
every rooted acyclic edge-indexed graph, without the stronger source package. -/
theorem bridge_component_iff_descendant (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e : E}
    (he : G.IsBridge e) (v : V) :
    G.ReachWithout e (G.target e) v ↔ G.DReach (G.target e) v := by
  constructor
  · intro hv
    by_contra hn
    have hroot := G.dreach_without_of_no_return e (hr v) hn
    have hs := (root_source_side_of_rooted_acyclic G root ha hr e).trans hroot
    exact G.bridge_sides_disjoint he hs hv
  · intro hv
    exact G.dreach_preserves
      (fun _ _ hstep hmem => G.bridge_target_forward_closed he hstep hmem)
      hv (.refl)

#print axioms root_source_side_of_rooted_acyclic
#print axioms bridge_component_iff_descendant

end GProgram.G5.Minimal
