import RawSourceAnchorLocalization
import GraphQuartetBridge

set_option debug.skipKernelTC false

/-!
Actual original-source bridge quartet localization, 4 October 2026.
The historical quartet API requested a GalledDetour field.  The accepted
original bridge-side theorem proves the required switching transport directly.
No planar, level, or desired-quartet premise is added.
-/
namespace Nanuq.Source.RootedBinary

open Nanuq.Quartet Nanuq.PortPatterns
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X}

namespace Switching

theorem hasQuartet_of_actual_original_bridge (S : N.Switching) {a b c d : V}
    (h : N.graph.HasQuartet a b c d) : S.graph.HasQuartet a b c d := by
  obtain ⟨e, he, hside⟩ := h
  let f : S.Edge := S.retainedBridge e he
  have hf := S.graph.uniqueIncoming_all_bridges
    S.selected_uniqueIncoming S.selected_acyclic f
  refine ⟨f, hf, ?_⟩
  rcases hside with hside | hside
  · exact Or.inl ⟨(S.original_bridge_source_side_iff e he _).mpr hside.1,
      (S.original_bridge_source_side_iff e he _).mpr hside.2.1,
      (S.original_bridge_target_side_iff e he _).mpr hside.2.2.1,
      (S.original_bridge_target_side_iff e he _).mpr hside.2.2.2⟩
  · exact Or.inr ⟨(S.original_bridge_source_side_iff e he _).mpr hside.1,
      (S.original_bridge_source_side_iff e he _).mpr hside.2.1,
      (S.original_bridge_target_side_iff e he _).mpr hside.2.2.1,
      (S.original_bridge_target_side_iff e he _).mpr hside.2.2.2⟩

theorem resolve_of_actual_original_bridge (S : N.Switching) (q : Fin 4 ↪ X)
    (r : Resolution) (h : N.graph.Resolves (fun i => N.leaf (q i)) r) :
    S.resolve q = r := by
  apply S.graph.resolution_unique (S.resolve_spec q)
  cases r <;> exact S.hasQuartet_of_actual_original_bridge h

end Switching

theorem actual_rawQuartetMean_of_original_bridge (N : RootedBinary V E X)
    (q : Fin 4 ↪ X) (r : Resolution)
    (h : N.graph.Resolves (fun i => N.leaf (q i)) r) :
    N.rawQuartetMean q = separatesFirstPair r := by
  have hc : (fun S : N.Switching => S.resolve q) = fun _ : N.Switching => r := by
    funext S
    exact S.resolve_of_actual_original_bridge q r h
  unfold rawQuartetMean
  rw [hc, sourceMean_const]

theorem actual_two_branching_blobs_force_resolution (N : RootedBinary V E X)
    (q : Fin 4 ↪ X) (b c : N.graph.Blob)
    (hb : N.NonleafBlob b) (hc : N.NonleafBlob c) (hbc : b ≠ c)
    (hf : 3 ≤ portCount (fun i => N.blobProjection b hb (q i)))
    (hg : 3 ≤ portCount (fun i => N.blobProjection c hc (q i))) :
    ∃ r, N.graph.Resolves (fun i => N.leaf (q i)) r ∧
      (∀ S : N.Switching, S.resolve q = r) ∧
      N.rawQuartetMean q = separatesFirstPair r := by
  obtain ⟨e, he, _, ht⟩ := N.two_branching_blobs_bridge q b c hb hc hbc hf hg
  obtain ⟨r, hr⟩ := N.original_bridge_resolution q he ht
  exact ⟨r, hr, fun S => S.resolve_of_actual_original_bridge q r hr,
    N.actual_rawQuartetMean_of_original_bridge q r hr⟩

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_rawQuartetMean_of_original_bridge
#print axioms Nanuq.Source.RootedBinary.actual_two_branching_blobs_force_resolution
