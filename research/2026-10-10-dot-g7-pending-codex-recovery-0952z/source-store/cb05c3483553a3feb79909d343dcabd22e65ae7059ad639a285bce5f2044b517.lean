import SourceNetwork
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin

/-!
# Census of original finite binary sources

New formal proof: dot's dedicated Lean lane, 2026-10-01.
Uses Samuel Alexander research's edge-indexed raw source API at the exact
baseline. Counts original edge IDs and original hybrid vertices; parallel
arcs remain distinct. No compressed core or source-size replacement is used.

These are graph census identities supporting G7's fixed n/r source census.
They do not prove the biological compiler or optimal policy frontier.
-/

namespace GProgram.G7

open Nanuq.Source
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem sum_inDegree (G : EdgeGraph V E) :
    (∑ v, G.inDegree v) = Fintype.card E := by
  classical
  simp only [EdgeGraph.inDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_outDegree (G : EdgeGraph V E) :
    (∑ v, G.outDegree v) = Fintype.card E := by
  classical
  simp only [EdgeGraph.outDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

noncomputable def hybridCount (N : RootedBinary V E X) : Nat := by
  classical
  exact (Finset.univ.filter N.graph.IsHybrid).card

noncomputable def leafSet (N : RootedBinary V E X) : Finset V := by
  classical
  exact Finset.univ.image N.leaf

theorem leafSet_card (N : RootedBinary V E X) :
    (leafSet N).card = Fintype.card X := by
  classical
  simp [leafSet, Finset.card_image_of_injective, N.leaf.injective]

theorem degree_local_in (N : RootedBinary V E X) (v : V) :
    N.graph.inDegree v + (if v = N.root then 1 else 0) =
      1 + (if N.graph.IsHybrid v then 1 else 0) := by
  classical
  by_cases hr : v = N.root
  · subst v
    have hn : ¬ N.graph.IsHybrid N.root := by
      intro hh
      have h0 := N.root_degrees.1
      rw [hh.1] at h0
      cases h0
    simp [N.root_degrees.1, hn]
  · by_cases hl : ∃ x, N.leaf x = v
    · obtain ⟨x, rfl⟩ := hl
      have hn : ¬ N.graph.IsHybrid (N.leaf x) := by
        intro hh
        have h1 := (N.leaf_degrees x).1
        rw [hh.1] at h1
        cases h1
      simp [hr, (N.leaf_degrees x).1, hn]
    · rcases N.internal_degrees v hr (fun x hx => hl ⟨x, hx⟩) with ht | hh
      · have hn : ¬ N.graph.IsHybrid v := by
          intro hh
          rw [hh.1] at ht
          omega
        simp [hr, ht.1, hn]
      · simp [hr, hh, hh.1]

theorem degree_local_out (N : RootedBinary V E X) (v : V) :
    N.graph.outDegree v + 2 * (if v ∈ leafSet N then 1 else 0) +
      (if N.graph.IsHybrid v then 1 else 0) = 2 := by
  classical
  by_cases hr : v = N.root
  · subst v
    have hn : ¬ N.graph.IsHybrid N.root := by
      intro hh
      have h0 := hh.1
      rw [N.root_degrees.1] at h0
      omega
    have hl : N.root ∉ leafSet N := by
      simp only [leafSet, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact N.leaf_ne_root
    simp [N.root_degrees.2, hn, hl]
  · by_cases hl : ∃ x, N.leaf x = v
    · obtain ⟨x, rfl⟩ := hl
      have hn : ¬ N.graph.IsHybrid (N.leaf x) := by
        intro hh
        have h0 := hh.2
        rw [(N.leaf_degrees x).2] at h0
        omega
      have hm : N.leaf x ∈ leafSet N := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
      simp [(N.leaf_degrees x).2, hn, hm]
    · have hm : v ∉ leafSet N := by simpa [leafSet] using hl
      rcases N.internal_degrees v hr (fun x hx => hl ⟨x, hx⟩) with ht | hh
      · have hn : ¬ N.graph.IsHybrid v := by
          intro hh
          rw [hh.2] at ht
          omega
        simp [ht.2, hm, hn]
      · simp [hh, hh.2, hm]

theorem original_census (N : RootedBinary V E X) :
    Fintype.card V + 1 = 2 * Fintype.card X + 2 * hybridCount N ∧
    Fintype.card E + 2 = 2 * Fintype.card X + 3 * hybridCount N := by
  classical
  have hi := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => degree_local_in N v)
  have ho := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => degree_local_out N v)
  have hc : (∑ v : V, if N.graph.IsHybrid v then 1 else 0) = hybridCount N := by
    simp only [hybridCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hl : (∑ v : V, if v ∈ leafSet N then 1 else 0) = Fintype.card X := by
    rw [← leafSet_card N]
    simp
  simp only [Finset.sum_add_distrib, sum_inDegree, sum_outDegree,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hi ho
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hc, hl,
    ← Finset.mul_sum] at hi ho
  simp only [Nat.cast_id, mul_one] at hi ho
  omega

#print axioms sum_inDegree
#print axioms sum_outDegree
#print axioms original_census

end GProgram.G7
