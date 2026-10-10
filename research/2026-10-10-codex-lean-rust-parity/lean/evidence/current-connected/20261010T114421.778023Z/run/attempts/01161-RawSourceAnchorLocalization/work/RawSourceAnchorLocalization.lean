import GraphSwitching
import G6BridgeCannotEnterHybrid

/-!
# Original bridge-component ports are switching-invariant

New original-source localization proof: dot, 2026-10-02.
The edge-indexed source graph and actual Switching API retain their original
NANUQ packet attribution. The generic rooted-acyclic bridge-entry proof comes
from GProgram.G6.BridgeEntry.

Every original bridge is retained by every actual raw switching, WITHOUT a
GalledDetour assumption. Both deletion components, hence every original taxon
fiber at every incident original component port, are unchanged. Parallel edge
occurrences and original vertices/taxon labels are retained exactly.

This is a bounded source-graph strengthening. It does not prove the anchor sum
identity, capped-blob quartet restriction/extension, semidirected convention
bridge, CircularPortMap, local planar representation, or raw all-level closure.
No source probability or desired conclusion is assumed as a field.
-/

namespace Nanuq.Source.RootedBinary.Switching

open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

/-- The source axioms alone retain every original bridge edge occurrence. -/
theorem original_bridge_retained {e : E} (he : N.graph.IsBridge e) : S.keep e :=
  S.ordinary e (GProgram.G6.BridgeEntry.original_bridge_target_not_hybrid N he)

/-- The selected occurrence has exactly the original edge identity. -/
def retainedBridge (e : E) (he : N.graph.IsBridge e) : S.Edge :=
  ⟨e, S.original_bridge_retained he⟩

@[simp] theorem retainedBridge_val (e : E) (he : N.graph.IsBridge e) :
    (S.retainedBridge e he).val = e := rfl

/-- Selected edge deletion never creates an original edge-deletion route. -/
theorem selected_reach_without_original (f : S.Edge) {a b : V}
    (h : S.graph.ReachWithout f a b) : N.graph.ReachWithout f.val a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨g, hgf, hinc⟩ := hstep
      have hv : g.val ≠ f.val := fun heq => hgf (Subtype.ext heq)
      exact ih.tail ⟨g.val, hv, hinc⟩

/-- Exact source-side equality, with no galled/planar/level hypothesis. -/
theorem original_bridge_source_side_iff (e : E) (he : N.graph.IsBridge e) (a : V) :
    S.graph.ReachWithout (S.retainedBridge e he) (N.graph.source e) a ↔
      N.graph.ReachWithout e (N.graph.source e) a := by
  constructor
  · exact S.selected_reach_without_original (S.retainedBridge e he)
  · intro ha
    rcases S.graph.edge_side_cover (S.retainedBridge e he)
        (S.selected_connected (N.graph.source e) a) with hs | ht
    · exact hs
    · exact False.elim (N.graph.bridge_sides_disjoint he ha
        (S.selected_reach_without_original (S.retainedBridge e he) ht))

/-- Exact target-side equality, with no galled/planar/level hypothesis. -/
theorem original_bridge_target_side_iff (e : E) (he : N.graph.IsBridge e) (a : V) :
    S.graph.ReachWithout (S.retainedBridge e he) (N.graph.target e) a ↔
      N.graph.ReachWithout e (N.graph.target e) a := by
  constructor
  · exact S.selected_reach_without_original (S.retainedBridge e he)
  · intro ha
    rcases S.graph.edge_side_cover (S.retainedBridge e he)
        (S.selected_connected (N.graph.source e) a) with hs | ht
    · exact False.elim (N.graph.bridge_sides_disjoint he
        (S.selected_reach_without_original (S.retainedBridge e he) hs) ha)
    · exact ht

/-- An original port is an original bridge with an endpoint in the selected
actual bridge-deleted component. Its external taxon-side meaning is exactly
preserved in the actual switching. Both port orientations are covered. -/
theorem raw_component_port_taxon_localization (a : V) (e : E)
    (he : N.graph.IsBridge e) (x : X) :
    ((N.graph.SameBlob a (N.graph.source e) ∧
        S.graph.ReachWithout (S.retainedBridge e he) (N.graph.target e) (N.leaf x)) ∨
      (N.graph.SameBlob a (N.graph.target e) ∧
        S.graph.ReachWithout (S.retainedBridge e he) (N.graph.source e) (N.leaf x))) ↔
    ((N.graph.SameBlob a (N.graph.source e) ∧
        N.graph.ReachWithout e (N.graph.target e) (N.leaf x)) ∨
      (N.graph.SameBlob a (N.graph.target e) ∧
        N.graph.ReachWithout e (N.graph.source e) (N.leaf x))) := by
  rw [S.original_bridge_source_side_iff e he, S.original_bridge_target_side_iff e he]

/-- The downstream component at an original port is also precisely the raw
directed descendant set; the switching has the same original taxon fiber. -/
theorem original_bridge_taxon_descendant_iff (e : E) (he : N.graph.IsBridge e) (x : X) :
    S.graph.ReachWithout (S.retainedBridge e he) (N.graph.target e) (N.leaf x) ↔
      N.graph.DReach (N.graph.target e) (N.leaf x) := by
  rw [S.original_bridge_target_side_iff e he]
  exact GProgram.G5.Minimal.bridge_component_iff_descendant
    N.graph N.root N.acyclic N.rooted he (N.leaf x)

/-- Exact equality of finite original-label fibers, not just a mass bound. -/
theorem original_bridge_taxon_fibers (e : E) (he : N.graph.IsBridge e) :
    (Finset.univ.filter (fun x : X =>
      S.graph.ReachWithout (S.retainedBridge e he) (N.graph.source e) (N.leaf x))) =
      (Finset.univ.filter (fun x : X =>
        N.graph.ReachWithout e (N.graph.source e) (N.leaf x))) ∧
    (Finset.univ.filter (fun x : X =>
      S.graph.ReachWithout (S.retainedBridge e he) (N.graph.target e) (N.leaf x))) =
      (Finset.univ.filter (fun x : X =>
        N.graph.ReachWithout e (N.graph.target e) (N.leaf x))) := by
  classical
  constructor
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.original_bridge_source_side_iff e he (N.leaf x)
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.original_bridge_target_side_iff e he (N.leaf x)

#print axioms original_bridge_retained
#print axioms original_bridge_source_side_iff
#print axioms original_bridge_target_side_iff
#print axioms raw_component_port_taxon_localization
#print axioms original_bridge_taxon_descendant_iff
#print axioms original_bridge_taxon_fibers

end Nanuq.Source.RootedBinary.Switching
