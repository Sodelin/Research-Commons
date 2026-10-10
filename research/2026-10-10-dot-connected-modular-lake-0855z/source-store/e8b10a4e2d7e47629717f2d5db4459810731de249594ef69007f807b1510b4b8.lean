import HybridChildPorts
import G5BridgeComponentEntries
import Mathlib.SetTheory.Cardinal.Finite

/-!
Original bridge-occurrence incident-port counts for nonplanar G6.
Contributor: Cloud Codex literature/organization structural source lane.
8 October 2026, 02:06 UTC. Compiler UNCHECKED; outside sole166.

The graph, original edge IDs and actual bridge-deleted components are the
inherited source. Unique rootward entries and original hybrid child bridges
derive the count bounds; no decomposition, count or target equality is an
input. Bigon classification, target preservation and full G6 remain separate.
-/

namespace UnifiedLean.G6.BlobIncidentPorts

open Nanuq.Source

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Original bridge occurrences whose target lies in the actual component. -/
abbrev IncomingPorts (N : RootedBinary V E X) (b : N.graph.Blob) :=
  {e : E // N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.target e) = b}

/-- Original bridge occurrences whose source lies in the actual component. -/
abbrev OutgoingPorts (N : RootedBinary V E X) (b : N.graph.Blob) :=
  {e : E // N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.source e) = b}

/-- Count an incident original edge occurrence once, with either orientation. -/
abbrev IncidentPorts (N : RootedBinary V E X) (b : N.graph.Blob) :=
  {e : E // N.graph.IsBridge e ∧
    (N.graph.blobOf (N.graph.target e) = b ∨
      N.graph.blobOf (N.graph.source e) = b)}

abbrev HybridsInBlob (N : RootedBinary V E X) (b : N.graph.Blob) :=
  {h : V // N.graph.IsHybrid h ∧ N.graph.blobOf h = b}

/-- An actual bridge cannot be both incoming and outgoing for one blob. -/
theorem bridge_incidence_disjoint (N : RootedBinary V E X) (b : N.graph.Blob)
    (e : E) (he : N.graph.IsBridge e)
    (hin : N.graph.blobOf (N.graph.target e) = b)
    (hout : N.graph.blobOf (N.graph.source e) = b) : False :=
  N.graph.bridge_blob_ne he (hout.trans hin.symm)

noncomputable def incidentToSum (N : RootedBinary V E X) (b : N.graph.Blob) :
    IncidentPorts N b → IncomingPorts N b ⊕ OutgoingPorts N b := by
  classical
  exact fun p => if hin : N.graph.blobOf (N.graph.target p.val) = b then
    Sum.inl ⟨p.val, p.property.1, hin⟩
  else
    Sum.inr ⟨p.val, p.property.1, p.property.2.resolve_left hin⟩

def sumToIncident (N : RootedBinary V E X) (b : N.graph.Blob) :
    IncomingPorts N b ⊕ OutgoingPorts N b → IncidentPorts N b
  | .inl p => ⟨p.val, p.property.1, Or.inl p.property.2⟩
  | .inr p => ⟨p.val, p.property.1, Or.inr p.property.2⟩

theorem sumToIncident_incidentToSum (N : RootedBinary V E X) (b : N.graph.Blob)
    (p : IncidentPorts N b) : sumToIncident N b (incidentToSum N b p) = p := by
  classical
  apply Subtype.ext
  by_cases hin : N.graph.blobOf (N.graph.target p.val) = b
  · simp [incidentToSum, sumToIncident, hin]
  · simp [incidentToSum, sumToIncident, hin]

theorem incidentToSum_sumToIncident (N : RootedBinary V E X) (b : N.graph.Blob)
    (p : IncomingPorts N b ⊕ OutgoingPorts N b) :
    incidentToSum N b (sumToIncident N b p) = p := by
  classical
  cases p with
  | inl p => simp [incidentToSum, sumToIncident, p.property.2]
  | inr p =>
      have hin : ¬ N.graph.blobOf (N.graph.target p.val) = b := by
        intro h
        exact bridge_incidence_disjoint N b p.val p.property.1 h p.property.2
      simp [incidentToSum, sumToIncident, hin]

/-- The sum representation is DERIVED from actual bridge disjointness. -/
noncomputable def incidentEquivSum (N : RootedBinary V E X) (b : N.graph.Blob) :
    IncidentPorts N b ≃ IncomingPorts N b ⊕ OutgoingPorts N b where
  toFun := incidentToSum N b
  invFun := sumToIncident N b
  left_inv := sumToIncident_incidentToSum N b
  right_inv := incidentToSum_sumToIncident N b

/-- The root component has no incoming original bridge occurrence. -/
theorem incoming_card_root_zero (N : RootedBinary V E X) :
    Nat.card (IncomingPorts N (N.graph.blobOf N.root)) = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  refine ⟨fun e => ?_⟩
  exact GProgram.G5.ComponentEntries.bridge_target_not_root_component
    N.graph N.root N.acyclic N.rooted e.property.1 (Quotient.exact e.property.2)

/-- Every actual nonroot component has precisely one incoming occurrence. -/
theorem incoming_card_nonroot_one (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) : Nat.card (IncomingPorts N b) = 1 := by
  classical
  revert hb
  refine Quotient.inductionOn b ?_
  intro v hv
  have hnonroot : ¬ N.graph.SameBlob N.root v := by
    intro h
    exact hv (Quotient.sound h).symm
  obtain ⟨e, he, huniq⟩ := GProgram.G5.ComponentEntries.nonroot_component_unique_entry
    N.graph N.root N.acyclic N.rooted v hnonroot
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨e, he.1, Quotient.sound he.2⟩, ?_⟩
  intro f
  apply Subtype.ext
  exact huniq f.val ⟨f.property.1, Quotient.exact f.property.2⟩

/-- Finite original incidence is the disjoint incoming/outgoing sum. -/
theorem incident_card_eq_sum (N : RootedBinary V E X) (b : N.graph.Blob) :
    Nat.card (IncidentPorts N b) =
      Nat.card (IncomingPorts N b) + Nat.card (OutgoingPorts N b) := by
  calc
    Nat.card (IncidentPorts N b) =
        Nat.card (IncomingPorts N b ⊕ OutgoingPorts N b) :=
      Nat.card_congr (incidentEquivSum N b)
    _ = Nat.card (IncomingPorts N b) + Nat.card (OutgoingPorts N b) := Nat.card_sum

theorem incident_card_nonroot (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) :
    Nat.card (IncidentPorts N b) = Nat.card (OutgoingPorts N b) + 1 := by
  rw [incident_card_eq_sum, incoming_card_nonroot_one N b hb]
  exact Nat.add_comm 1 _

theorem incident_card_root (N : RootedBinary V E X) :
    Nat.card (IncidentPorts N (N.graph.blobOf N.root)) =
      Nat.card (OutgoingPorts N (N.graph.blobOf N.root)) := by
  rw [incident_card_eq_sum, incoming_card_root_zero]
  simp

/-- The one derived rootward entry is excluded from the hybrid child count. -/
theorem nonroot_hybrid_card_le_incident_sub_one (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) :
    Nat.card (HybridsInBlob N b) ≤ Nat.card (IncidentPorts N b) - 1 := by
  calc
    Nat.card (HybridsInBlob N b) ≤ Nat.card (OutgoingPorts N b) :=
      UnifiedLean.G6.HybridChildPorts.hybrids_in_blob_card_le_outgoing_bridges N hcut b
    _ = Nat.card (IncidentPorts N b) - 1 := by
      rw [incident_card_nonroot N b hb]
      simp

theorem root_hybrid_card_le_incident (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e) :
    Nat.card (HybridsInBlob N (N.graph.blobOf N.root)) ≤
      Nat.card (IncidentPorts N (N.graph.blobOf N.root)) := by
  rw [incident_card_root]
  exact UnifiedLean.G6.HybridChildPorts.hybrids_in_blob_card_le_outgoing_bridges
    N hcut (N.graph.blobOf N.root)

#print axioms bridge_incidence_disjoint
#print axioms sumToIncident_incidentToSum
#print axioms incidentToSum_sumToIncident
#print axioms incoming_card_root_zero
#print axioms incoming_card_nonroot_one
#print axioms incident_card_eq_sum
#print axioms incident_card_nonroot
#print axioms incident_card_root
#print axioms nonroot_hybrid_card_le_incident_sub_one
#print axioms root_hybrid_card_le_incident

end UnifiedLean.G6.BlobIncidentPorts
