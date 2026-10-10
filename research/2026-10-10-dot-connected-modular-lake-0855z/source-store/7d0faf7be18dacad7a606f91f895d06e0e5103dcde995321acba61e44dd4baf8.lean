import G6OriginalSpliceAdapter
import G1ActualDisplayedClusterSplitTransport

/-!
Original G6 nontrivial split target, using Dot's actual G1 pruning and splice
transport unchanged. Cloud literature/organization lane, 8 October 2026.
Compiler UNCHECKED; outside current176. No suppression code is copied.

The original G1 cut union includes pendant splits. The G6 target keeps precisely
the unordered cuts with BOTH original-label sides of cardinality at least two.
The full target uses the SAME original X, not the retained vertex subtype.
Actual normalized evaluator membership is derived from the original provider;
no observed S, desired target equality or stochastic/source-law field is supplied.
-/

namespace UnifiedLean.G6.NontrivialSplitFilter

open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.Normalization
open G1CutChildPorts G1ActualTwoPortBlob G1SplicedSourceAdmission
open G1ActualDisplayedClusterSplitTransport
open UnifiedLean.G6.OriginalSpliceAdapter
open scoped Classical

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- This predicate is used ONLY with an actually generated unordered split.
The split membership theorem below supplies its two complementary sides. -/
def BothSidesNontrivial (cut : Finset (Finset X)) : Prop :=
  ∀ D ∈ cut, 2 ≤ D.card

/-- A symmetric filter, independent of which side names the unordered cut. -/
theorem bothSidesNontrivial_pair (panel D : Finset X) :
    BothSidesNontrivial {D, panel \ D} ↔
      2 ≤ D.card ∧ 2 ≤ (panel \ D).card := by
  constructor
  · intro h
    exact ⟨h D (Finset.mem_insert_self _ _),
      h (panel \ D) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  · rintro ⟨hD, hComp⟩ A hA
    have hA' : A = D ∨ A = panel \ D := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hA
    rcases hA' with rfl | rfl
    · exact hD
    · exact hComp

/-- General panel helper. The original G6 S below specializes to ALL X. -/
noncomputable def nontrivialDisplayedSplits (N : RootedBinary V E X)
    (panel : Finset X) : Finset (Finset (Finset X)) :=
  (actualDisplayedSplits N panel).filter BothSidesNontrivial

/-- The original G6 displayed split union: fixed original-label universe X,
both sides >= 2, with duplicates removed by the inherited unordered encoding. -/
noncomputable def originalG6S (N : RootedBinary V E X) :
    Finset (Finset (Finset X)) :=
  nontrivialDisplayedSplits N Finset.univ

theorem mem_nontrivialDisplayedSplits (N : RootedBinary V E X)
    (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ nontrivialDisplayedSplits N panel ↔
      cut ∈ actualDisplayedSplits N panel ∧ BothSidesNontrivial cut := by
  simp only [nontrivialDisplayedSplits, Finset.mem_filter]

/-- Both directions use actual displayed original clusters, not an arbitrary
cut family or a supplied equality of target fields. Cardinality >= 2 supplies
the original provider's proper/nonempty-side conditions. -/
theorem mem_nontrivialDisplayedSplits_iff_cluster (N : RootedBinary V E X)
    (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ nontrivialDisplayedSplits N panel ↔
      ∃ D, D ∈ actualDisplayedClusters N panel ∧ D ⊆ panel ∧
        2 ≤ D.card ∧ 2 ≤ (panel \ D).card ∧ cut = {D, panel \ D} := by
  rw [mem_nontrivialDisplayedSplits]
  constructor
  · rintro ⟨hcut, hBoth⟩
    obtain ⟨D, hD, he⟩ := Finset.mem_image.mp hcut
    obtain ⟨hC, hsub, _, _⟩ := Finset.mem_filter.mp hD
    have hCard := (bothSidesNontrivial_pair panel D).mp (he.symm ▸ hBoth)
    exact ⟨D, hC, hsub, hCard.1, hCard.2, he.symm⟩
  · rintro ⟨D, hC, hsub, hDcard, hCompcard, rfl⟩
    refine ⟨?_, (bothSidesNontrivial_pair panel D).mpr ⟨hDcard, hCompcard⟩⟩
    refine Finset.mem_image.mpr ⟨D, Finset.mem_filter.mpr ⟨hC, hsub, ?_, ?_⟩, rfl⟩
    · exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hDcard)
    · exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hCompcard)

/-- Source/target interface: exactly the nontrivial cuts of actual original
root-pruned switching trees. Calendar is the original provider's existence
premise; no probability, inferred support or observed S enters the statement. -/
theorem mem_nontrivialDisplayedSplits_iff_normalized_evaluator
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ nontrivialDisplayedSplits N panel ↔
      ∃ S : N.Switching, ∃ T : Genealogy X,
        PrunedAt N S panel N.root (some T) ∧
          cut ∈ rootSuppressedCuts T ∧ BothSidesNontrivial cut := by
  rw [mem_nontrivialDisplayedSplits,
    actual_displayed_splits_iff_normalized_evaluator N C panel cut]
  constructor
  · rintro ⟨⟨S, T, hT, hcut⟩, hBoth⟩
    exact ⟨S, T, hT, hcut, hBoth⟩
  · rintro ⟨S, T, hT, hcut, hBoth⟩
    exact ⟨⟨S, T, hT, hcut⟩, hBoth⟩

theorem mem_originalG6S_iff_normalized_evaluator
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (cut : Finset (Finset X)) :
    cut ∈ originalG6S N ↔
      ∃ S : N.Switching, ∃ T : Genealogy X,
        PrunedAt N S Finset.univ N.root (some T) ∧
          cut ∈ rootSuppressedCuts T ∧ BothSidesNontrivial cut :=
  mem_nontrivialDisplayedSplits_iff_normalized_evaluator N C Finset.univ cut

/-- Reuse the original source-proved restriction/lifting of actual switchings.
The same filter is applied to the already proved equal unfiltered cut unions. -/
theorem nontrivialDisplayedSplits_splice (N : RootedBinary V E X)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (panel : Finset X) :
    nontrivialDisplayedSplits (splicedNetwork N hc b hb A) panel =
      nontrivialDisplayedSplits N panel := by
  unfold nontrivialDisplayedSplits
  rw [actual_displayed_splits_splice N hc b hb A panel]

/-- The actual G6 incident-two-port premise derives the genuine original
bigon first. No desired target preservation is an input. -/
theorem suppressed_nontrivialDisplayedSplits (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) (panel : Finset X) :
    nontrivialDisplayedSplits (suppressedNetwork N hcut b hb hp) panel =
      nontrivialDisplayedSplits N panel :=
  nontrivialDisplayedSplits_splice N hcut b hb (derivedBigon N hcut b hb hp) panel

theorem suppressed_originalG6S (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    originalG6S (suppressedNetwork N hcut b hb hp) = originalG6S N :=
  suppressed_nontrivialDisplayedSplits N hcut b hb hp Finset.univ

/-- Vertex suppression retains the very same label x at its original vertex.
There is no quotient/relabeling of X and no deletion of taxa. -/
theorem suppressed_leaf_identity (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) (x : X) :
    ((suppressedNetwork N hcut b hb hp).leaf x).val = N.leaf x := rfl

theorem suppressed_root_identity (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    (suppressedNetwork N hcut b hb hp).root.val = N.root := rfl

#print axioms bothSidesNontrivial_pair
#print axioms mem_nontrivialDisplayedSplits
#print axioms mem_nontrivialDisplayedSplits_iff_cluster
#print axioms mem_nontrivialDisplayedSplits_iff_normalized_evaluator
#print axioms mem_originalG6S_iff_normalized_evaluator
#print axioms nontrivialDisplayedSplits_splice
#print axioms suppressed_nontrivialDisplayedSplits
#print axioms suppressed_originalG6S
#print axioms suppressed_leaf_identity
#print axioms suppressed_root_identity

end UnifiedLean.G6.NontrivialSplitFilter
