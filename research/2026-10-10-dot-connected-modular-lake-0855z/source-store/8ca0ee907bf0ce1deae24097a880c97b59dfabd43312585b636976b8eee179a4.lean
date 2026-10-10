import SourceNetwork
import Mathlib.Data.Finset.Card

/-!
UNCHECKED actual graph-count adapter. No compiler has run for these bytes.
The sets use the inherited edge-indexed RootedBinary graph and its original
directed reachability, not a supplied source word or assumed law equality.
These cardinality facts alone do not serialize the graph or identify its law.
The original cut-child/passive quartet source-to-word bridge remains a separate
hand theorem in SOURCE-WORD-CONTRACT.md and a named formal consumer gate.
-/

namespace CloudG3.ActualFocalHybridCount

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

noncomputable def totalHybrids (N : RootedBinary V E X) : Finset V := by
  classical
  exact Finset.univ.filter N.graph.IsHybrid

noncomputable def focalHybrids (N : RootedBinary V E X) (A : X) : Finset V := by
  classical
  exact (totalHybrids N).filter (fun h => N.graph.DReach h (N.leaf A))

noncomputable def totalHybridCount (N : RootedBinary V E X) : ℕ :=
  (totalHybrids N).card

noncomputable def focalHybridCount (N : RootedBinary V E X) (A : X) : ℕ :=
  (focalHybrids N A).card

theorem mem_totalHybrids (N : RootedBinary V E X) (h : V) :
    h ∈ totalHybrids N ↔ N.graph.IsHybrid h := by
  classical
  simp [totalHybrids]

theorem mem_focalHybrids (N : RootedBinary V E X) (A : X) (h : V) :
    h ∈ focalHybrids N A ↔
      N.graph.IsHybrid h ∧ N.graph.DReach h (N.leaf A) := by
  classical
  simp [focalHybrids, totalHybrids]

theorem focalHybrids_subset (N : RootedBinary V E X) (A : X) :
    focalHybrids N A ⊆ totalHybrids N := by
  classical
  unfold focalHybrids
  exact Finset.filter_subset _ _

theorem focalHybridCount_le_total (N : RootedBinary V E X) (A : X) :
    focalHybridCount N A ≤ totalHybridCount N := by
  unfold focalHybridCount totalHybridCount
  exact Finset.card_le_card (focalHybrids_subset N A)

end CloudG3.ActualFocalHybridCount
