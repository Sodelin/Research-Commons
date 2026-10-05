import G1SharpCoreCombOuterEmbedding
import UnifiedLean.Source.NativeIndependentPairMixture

/-! Formal port of the ACCEPTED all-n sharpness family, fresh source review
§3 (2026-10-01), preserving n≥4. All original admission properties and outer
geometry are constructed. This concerns reduced physical core size; it is
not an ordinary-profile witness bound or exact source-image recognition. -/
namespace G1AllNActualOuterSourceSharpness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombAdmission G1SharpCoreCombCutChild G1SharpCoreCombReduced
open G1SharpCoreCombOuterEmbedding G1ActualGraphNormalization G1ReducedCoreCounts
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open scoped Classical

noncomputable def admittedSource (n : Nat) (hn : 4 ≤ n) : Source.{0,0,0} (Fin n) :=
  admit (network n hn) (actual_cut_child n hn) (calendar n)

def originalRates (n : Nat) : PositivePairRates (Edge n) where
  edge := fun _ => 1
  edge_pos := fun _ => by norm_num
  ancestral := 1
  ancestral_pos := by norm_num

noncomputable def originalInheritance (n : Nat) (hn : 4 ≤ n) : HybridProbabilities (network n hn) where
  gamma := fun _ => 1/2
  positive := fun _ => by norm_num
  below_one := fun _ => by norm_num

theorem admitted_source_already_reduced (n : Nat) (hn : 4 ≤ n) : Reduced (admittedSource n hn) :=
  actual_reduced n hn

/-- EVERY n≥4 has an actual positive dated, outer-labelled, binary LSA
cut-child source whose already-reduced core attains all three accepted
upper bounds. No reducedness, embedding or graph-size premise is assumed. -/
theorem every_n_has_actual_saturating_outer_source (n : Nat) (hn : 4 ≤ n) :
    ∃ S : Source.{0,0,0} (Fin n), Reduced S ∧ Nonempty (OriginalOuterEmbedding S.network.graph) ∧
      Nonempty (PositivePairRates S.Edge) ∧ Nonempty (HybridProbabilities S.network) ∧
      (hybrids S.network).card = 2*n-2 ∧ Fintype.card S.Vertex = 6*n-5 ∧
      Fintype.card S.Edge = 8*n-8 ∧ (∀ x : Fin n, S.calendar.age (S.network.leaf x) = 0) := by
  refine ⟨admittedSource n hn,admitted_source_already_reduced n hn,
    ⟨actual_outer_embedding n hn⟩,⟨originalRates n⟩,⟨originalInheritance n hn⟩,
    exact_hybrid_count n hn,exact_vertex_count n hn,exact_edge_count n hn,?_⟩
  exact original_tips_contemporaneous n

/-- Saturation gives the usual sharpness consequence against ANY proposed
smaller uniform bound on admitted reduced outer-labelled physical cores. -/
theorem no_strictly_smaller_hybrid_bound (n : Nat) (hn : 4 ≤ n) (b : Nat) (hb : b < 2*n-2) :
    ¬ (∀ S : Source.{0,0,0} (Fin n), Reduced S → Nonempty (OriginalOuterEmbedding S.network.graph) →
      (hybrids S.network).card ≤ b) := by
  intro hall
  have h := hall (admittedSource n hn) (admitted_source_already_reduced n hn) ⟨actual_outer_embedding n hn⟩
  change (hybrids (network n hn)).card ≤ b at h
  rw [exact_hybrid_count] at h
  omega

theorem no_strictly_smaller_vertex_bound (n : Nat) (hn : 4 ≤ n) (b : Nat) (hb : b < 6*n-5) :
    ¬ (∀ S : Source.{0,0,0} (Fin n), Reduced S → Nonempty (OriginalOuterEmbedding S.network.graph) →
      Fintype.card S.Vertex ≤ b) := by
  intro hall
  have h := hall (admittedSource n hn) (admitted_source_already_reduced n hn) ⟨actual_outer_embedding n hn⟩
  change Fintype.card (Vertex n) ≤ b at h
  rw [exact_vertex_count n hn] at h
  omega

theorem no_strictly_smaller_edge_bound (n : Nat) (hn : 4 ≤ n) (b : Nat) (hb : b < 8*n-8) :
    ¬ (∀ S : Source.{0,0,0} (Fin n), Reduced S → Nonempty (OriginalOuterEmbedding S.network.graph) →
      Fintype.card S.Edge ≤ b) := by
  intro hall
  have h := hall (admittedSource n hn) (admitted_source_already_reduced n hn) ⟨actual_outer_embedding n hn⟩
  change Fintype.card (Edge n) ≤ b at h
  rw [exact_edge_count n hn] at h
  omega

#print axioms every_n_has_actual_saturating_outer_source
#print axioms no_strictly_smaller_hybrid_bound
#print axioms no_strictly_smaller_vertex_bound
#print axioms no_strictly_smaller_edge_bound
end G1AllNActualOuterSourceSharpness
