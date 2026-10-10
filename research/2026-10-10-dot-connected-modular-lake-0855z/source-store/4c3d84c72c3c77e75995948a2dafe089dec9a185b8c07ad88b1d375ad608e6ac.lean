import ParallelArmSwitching
import EdgeOccurrenceQuartetTransport
import SourceResolve

/-!
Actual original bigon arm-choice neutrality for the existing raw quartet
resolution. Cloud G6 source prototype, 8 October 2026. COMPILER UNCHECKED.
The actual two-port theorem supplies the arm witness; the selected edge
bijection supplies primitive graph data; actual edge-deletion predicates
supply the quartet conclusion. Suppression and full Q/S union are separate.
-/
namespace UnifiedLean.G6.BigonQuartetChoice

open Nanuq.Source
open UnifiedLean.G6.ParallelArmSwitching UnifiedLean.G6.EdgeOccurrenceTransport

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X}

/-- Endpoint-preserving occurrence data come from the actual switching flip. -/
noncomputable def selectedOccurrenceEquiv (P : OriginalParallelArms N) (S : N.Switching) :
    OccurrenceEquiv S.graph (flippedSwitching P S).graph where
  edge := selectedEdgeEquiv P S
  source := selectedEdgeEquiv_source P S
  target := selectedEdgeEquiv_target P S

theorem flipped_hasQuartet_iff (P : OriginalParallelArms N) (S : N.Switching)
    (a b c d : V) :
    S.graph.HasQuartet a b c d ↔ (flippedSwitching P S).graph.HasQuartet a b c d :=
  (selectedOccurrenceEquiv P S).hasQuartet_iff a b c d

/-- Transport the proved existing raw resolution, using its original edge-cut semantics. -/
theorem flipped_resolution_eq (P : OriginalParallelArms N) (S : N.Switching)
    (q : Fin 4 ↪ X) : S.resolve q = (flippedSwitching P S).resolve q := by
  exact (flippedSwitching P S).graph.resolution_unique
    (((selectedOccurrenceEquiv P S).resolves_iff
      (fun i => N.leaf (q i)) (S.resolve q)).mp (S.resolve_spec q))
    ((flippedSwitching P S).resolve_spec q)

/-- The narrow witness is derived from the original actual two-port blob. -/
theorem actual_twoport_quartet_choice_neutral (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (UnifiedLean.G6.BlobIncidentPorts.IncidentPorts N b) = 2)
    (S : N.Switching) :
    ∃ P : OriginalParallelArms N,
      ∀ q : Fin 4 ↪ X, S.resolve q = (flippedSwitching P S).resolve q := by
  obtain ⟨P⟩ := actual_parallel_arms_nonempty N hcut b hb hp
  exact ⟨P, fun q => flipped_resolution_eq P S q⟩

#print axioms flipped_hasQuartet_iff
#print axioms flipped_resolution_eq
#print axioms actual_twoport_quartet_choice_neutral

end UnifiedLean.G6.BigonQuartetChoice
