import G6NontrivialSplitFilter
import G1ActualDisplayedQuartetTransport
import G1FiniteNormalizationDisplayedTargets

/-!
Thin original G6 (Q,S) consumer of the existing actual G1 splice.
CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026.
Compiler UNCHECKED; outside current176 and proposed179.

The SAME derived original bigon supplies one constructed suppressed network.
Q uses actual raw displayed resolutions on every original-label quartet panel;
S uses the actual displayed nontrivial split union on all original X.
No desired target field, observation, likelihood or stochastic-law equality
is a premise. Generic original G1 restriction/lifting proofs are reused.
-/

namespace UnifiedLean.G6.PairedTargetReuse

open GProgram.G5
open Nanuq.Source GProgram.G5.Normalization
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore
open G1FiniteNormalizationDisplayedTargets G1ReducedCoreCounts
open G1ActualDisplayedQuartetTransport
open UnifiedLean.G6.OriginalSpliceAdapter
open UnifiedLean.G6.NontrivialSplitFilter
open scoped Classical

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Fixed original-label representation of distinct displayed Q and
nontrivial displayed S. Ordered quartet embeddings are redundant coordinates,
not switching multiplicities or gene-tree support. -/
noncomputable def originalG6TargetPair (N : RootedBinary V E X) :
    ((Fin 4 ↪ X) → Finset Nanuq.Quartet.Resolution) ×
      Finset (Finset (Finset X)) :=
  (fun q => N.rawDisplayedQuartets q, originalG6S N)

theorem suppressed_raw_displayed_quartets (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (q : Fin 4 ↪ X) :
    (suppressedNetwork N hcut b hb hp).rawDisplayedQuartets q =
      N.rawDisplayedQuartets q :=
  actual_raw_displayed_quartets_splice N C hcut b hb
    (derivedBigon N hcut b hb hp) q

/-- The inherited normalized-tree interpretation uses the original calendar,
and the constructed splice retains its calendar through the existing provider. -/
theorem suppressed_normalized_displayed_quartets (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (q : Fin 4 ↪ X) :
    GProgram.G5.Normalization.normalizedDisplayedCutQuartets
        (suppressedNetwork N hcut b hb hp) q =
      GProgram.G5.Normalization.normalizedDisplayedCutQuartets N q :=
  actual_normalized_displayed_quartets_splice N C hcut b hb
    (derivedBigon N hcut b hb hp) q

/-- Both target components belong to ONE constructed source reduction,
with the SAME original label universe and the SAME original bigon witness. -/
theorem suppressed_originalG6TargetPair (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    originalG6TargetPair (suppressedNetwork N hcut b hb hp) =
      originalG6TargetPair N := by
  unfold originalG6TargetPair
  apply Prod.ext
  · funext q
    exact suppressed_raw_displayed_quartets N C hcut b hb hp q
  · exact suppressed_originalG6S N hcut b hb hp

/-- The existing generic constructed normalization and original-span decoration
supply a bounded raw core with the same original G6 target pair.
This is a topological/original-provenance witness, not a numerical or
stochastic-law replacement theorem. No planar embedding is a premise. -/
theorem actual_bounded_original_core_preserves_G6_pair
    (O : G1ActualGraphNormalization.Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) :
    ∃ (T : G1ActualGraphNormalization.Source X) (D : Decoration O T),
      Steps O T ∧ Originated O H D ∧ Reduced T ∧
      (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧
      Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 ∧
      originalG6TargetPair T.network = originalG6TargetPair O.network := by
  obtain ⟨T, D, steps, origin, reduced, hh, hv, he, hCS, hQ⟩ :=
    actual_bounded_originated_core_preserves_displayed_targets O H
  refine ⟨T, D, steps, origin, reduced, hh, hv, he, ?_⟩
  unfold originalG6TargetPair
  apply Prod.ext
  · funext q
    rw [raw_displayed_equals_normalized_cut_quartets T.network T.calendar q,
      raw_displayed_equals_normalized_cut_quartets O.network O.calendar q]
    exact hQ q
  · unfold originalG6S nontrivialDisplayedSplits
    rw [(hCS Finset.univ).2]

#print axioms originalG6TargetPair
#print axioms suppressed_raw_displayed_quartets
#print axioms suppressed_normalized_displayed_quartets
#print axioms suppressed_originalG6TargetPair
#print axioms actual_bounded_original_core_preserves_G6_pair

end UnifiedLean.G6.PairedTargetReuse
