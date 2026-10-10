import GraphBlobs
import SourceNetwork
import Mathlib.SetTheory.Cardinal.Finite

/-!
Root additive source draft, 8 October 2026.
Compiler UNCHECKED; outside the accepted 165 and proposed 166 selections.
The original cut-child hypothesis is explicit. Original physical edge IDs
are retained; a child port is never an arbitrary replacement kernel.
This is only the first port-count bridge, not bigon classification,
switching/target preservation or the complete nonplanar G6 theorem.
-/

namespace UnifiedLean.G6.HybridChildPorts

open Nanuq.Source

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Actual hybrid outdegree one supplies an original outgoing occurrence. -/
theorem hybrid_child_exists (N : RootedBinary V E X) (h : V)
    (hh : N.graph.IsHybrid h) :
    ∃ e : E, N.graph.source e = h := by
  classical
  have hc : (Finset.univ.filter (fun e : E => N.graph.source e = h)).card = 1 :=
    hh.2
  have he : ∃! e : E, e ∈ Finset.univ.filter (fun e => N.graph.source e = h) :=
    Finset.card_eq_one_iff_existsUnique.mp hc
  obtain ⟨e, he⟩ := he.exists
  exact ⟨e, (Finset.mem_filter.mp he).2⟩

/-- Choose the original occurrence whose existence follows from outdegree. -/
noncomputable def hybridChild (N : RootedBinary V E X)
    (h : {v : V // N.graph.IsHybrid v}) : E :=
  Classical.choose (hybrid_child_exists N h.val h.property)

theorem hybridChild_source (N : RootedBinary V E X)
    (h : {v : V // N.graph.IsHybrid v}) :
    N.graph.source (hybridChild N h) = h.val :=
  Classical.choose_spec (hybrid_child_exists N h.val h.property)

/-- Two hybrids cannot own the same outgoing original edge occurrence. -/
theorem hybridChild_injective (N : RootedBinary V E X) :
    Function.Injective (hybridChild N) := by
  intro a b hab
  apply Subtype.ext
  calc
    a.val = N.graph.source (hybridChild N a) := (hybridChild_source N a).symm
    _ = N.graph.source (hybridChild N b) := congrArg N.graph.source hab
    _ = b.val := hybridChild_source N b

/-- Every hybrid in an actual bridge-deleted component injects into that
component's outgoing bridge occurrences. No embedding or supplied
decomposition is assumed. This counts outgoing ports, not all incident
ports; the unique nonroot entry must be handled in the next consumer. -/
theorem hybrids_in_blob_card_le_outgoing_bridges (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) :
    Nat.card {h : V // N.graph.IsHybrid h ∧ N.graph.blobOf h = b} ≤
      Nat.card {e : E // N.graph.IsBridge e ∧
        N.graph.blobOf (N.graph.source e) = b} := by
  classical
  let f : {h : V // N.graph.IsHybrid h ∧ N.graph.blobOf h = b} →
      {e : E // N.graph.IsBridge e ∧
        N.graph.blobOf (N.graph.source e) = b} := fun h =>
    ⟨hybridChild N ⟨h.val, h.property.1⟩,
      hcut _ (by rw [hybridChild_source]; exact h.property.1),
      by rw [hybridChild_source]; exact h.property.2⟩
  apply Nat.card_le_card_of_injective f
  intro a d had
  apply Subtype.ext
  have he : hybridChild N ⟨a.val, a.property.1⟩ =
      hybridChild N ⟨d.val, d.property.1⟩ := congrArg Subtype.val had
  exact congrArg Subtype.val (hybridChild_injective N he)

#print axioms hybrid_child_exists
#print axioms hybridChild_source
#print axioms hybridChild_injective
#print axioms hybrids_in_blob_card_le_outgoing_bridges

end UnifiedLean.G6.HybridChildPorts
