import GraphSwitchingCuts
import GraphQuartetExistence
import G1CutChildPorts
import G4WeightedOrdinaryTreeLaw

/-!
Actual original bridge cuts and COMMON route fibres.

Source-only composition of selected providers. No graph geometry, cut equality,
bank law, or cardinality bound is supplied as a premise. The calendar below is
the existing commonRoutes interface; no timed observation theorem is asserted.
-/
namespace Astra.BridgeTaxonCuts

open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeCommonPairGerm
open GProgram.G5 GProgram.G5.AttainedChronology
open DotG4.WeightedOrdinaryTreeLaw
open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

/-- Original taxa on the child side after deleting the actual original bridge. -/
noncomputable def bridgeTaxa (N : RootedBinary V E X)
    (e : N.graph.BridgeEdge) : Finset X :=
  Finset.univ.filter (fun x =>
    N.graph.ReachWithout e.val (N.graph.target e.val) (N.leaf x))

theorem mem_bridgeTaxa (N : RootedBinary V E X)
    (e : N.graph.BridgeEdge) (x : X) :
    x ∈ bridgeTaxa N e ↔
      N.graph.ReachWithout e.val (N.graph.target e.val) (N.leaf x) := by
  simp only [bridgeTaxa, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bridgeTaxa_nonempty (N : RootedBinary V E X)
    (e : N.graph.BridgeEdge) : (bridgeTaxa N e).Nonempty := by
  obtain ⟨x, hx⟩ := N.bridge_target_side_contains_taxon e.property
  exact ⟨x, (mem_bridgeTaxa N e x).mpr hx⟩

theorem bridgeTaxa_has_outside (N : RootedBinary V E X)
    (e : N.graph.BridgeEdge) : ∃ x : X, x ∉ bridgeTaxa N e := by
  obtain ⟨x, hx⟩ := N.bridge_source_side_contains_taxon e.val
  refine ⟨x, ?_⟩
  intro hmem
  exact N.graph.bridge_sides_disjoint e.property hx
    ((mem_bridgeTaxa N e x).mp hmem)

theorem bridgeTaxa_proper (N : RootedBinary V E X)
    (e : N.graph.BridgeEdge) : bridgeTaxa N e ≠ Finset.univ := by
  obtain ⟨x, hx⟩ := bridgeTaxa_has_outside N e
  intro heq
  apply hx
  rw [heq]
  exact Finset.mem_univ x

/-- Both witnesses are original taxa, and necessarily distinct. -/
theorem bridgeTaxa_separating_pair (N : RootedBinary V E X)
    (e : N.graph.BridgeEdge) :
    ∃ i j : X, i ∈ bridgeTaxa N e ∧ j ∉ bridgeTaxa N e ∧ i ≠ j := by
  obtain ⟨i, hi⟩ := bridgeTaxa_nonempty N e
  obtain ⟨j, hj⟩ := bridgeTaxa_has_outside N e
  refine ⟨i, j, hi, hj, ?_⟩
  intro hij
  exact hj (hij ▸ hi)

/-- Every original bridge is ordinary at its target, hence is retained by
every actual switching. No galled or cut-child premise is needed. -/
theorem bridge_retained (N : RootedBinary V E X) (S : N.Switching)
    (e : N.graph.BridgeEdge) : S.keep e.val := by
  apply S.ordinary e.val
  intro hhybrid
  exact G1CutChildPorts.actual_hybrid_parent_nonbridge N e.val hhybrid e.property

/-- The same original edge occurrence, equipped only with its derived keep proof. -/
noncomputable def selectedBridge (N : RootedBinary V E X) (S : N.Switching)
    (e : N.graph.BridgeEdge) : S.Edge :=
  ⟨e.val, bridge_retained N S e⟩

@[simp] theorem selectedBridge_val (N : RootedBinary V E X) (S : N.Switching)
    (e : N.graph.BridgeEdge) : (selectedBridge N S e).val = e.val := rfl

/-- The original edge-deletion cut is the descendant fibre in every selected
tree; selected rootedness and unique incoming edges are derived providers. -/
theorem mem_bridgeTaxa_iff_selected_descendant (N : RootedBinary V E X)
    (S : N.Switching) (e : N.graph.BridgeEdge) (x : X) :
    x ∈ bridgeTaxa N e ↔ S.graph.DReach (N.graph.target e.val) (N.leaf x) := by
  exact (mem_bridgeTaxa N e x).trans
    ((S.selected_target_side_iff (selectedBridge N S e) e.property (N.leaf x)).symm.trans
      (S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic
        (selectedBridge N S e) (N.leaf x)))

/-- Literal equality with the existing actual COMMON route fibre. -/
theorem common_edgeTaxa_eq_bridgeTaxa (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (coin : CommonSeed N)
    (e : N.graph.BridgeEdge) :
    edgeTaxa N C H coin e.val = bridgeTaxa N e := by
  ext x
  exact (edgeTaxa_selected_descendants N C H coin
    (selectedBridge N (commonSwitching N H coin) e) x).trans
      (mem_bridgeTaxa_iff_selected_descendant N (commonSwitching N H coin) e x).symm

/-- The existing compiler routes cross the bridge for precisely its child taxa. -/
theorem common_route_bridge_iff (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (coin : CommonSeed N)
    (e : N.graph.BridgeEdge) (x : X) :
    e.val ∈ (commonRoutes N C H coin).edges x ↔ x ∈ bridgeTaxa N e := by
  rw [← mem_edgeTaxa N C H coin e.val x, common_edgeTaxa_eq_bridgeTaxa]

/-- One original bridge cut is unchanged across all original COMMON banks. -/
theorem common_bridge_fibre_bank_independent (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (coin coin' : CommonSeed N) (e : N.graph.BridgeEdge) :
    edgeTaxa N C H coin e.val = edgeTaxa N C H coin' e.val := by
  rw [common_edgeTaxa_eq_bridgeTaxa, common_edgeTaxa_eq_bridgeTaxa]

/-- A single pair of original taxa witnesses this bridge in every COMMON bank. -/
theorem common_bridge_uniform_pair (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (e : N.graph.BridgeEdge) :
    ∃ i j : X, i ≠ j ∧ ∀ coin : CommonSeed N,
      e.val ∈ (commonRoutes N C H coin).edges i ∧
      e.val ∉ (commonRoutes N C H coin).edges j := by
  obtain ⟨i, j, hi, hj, hij⟩ := bridgeTaxa_separating_pair N e
  refine ⟨i, j, hij, ?_⟩
  intro coin
  exact ⟨(common_route_bridge_iff N C H coin e i).mpr hi,
    fun h => hj ((common_route_bridge_iff N C H coin e j).mp h)⟩

end Astra.BridgeTaxonCuts
