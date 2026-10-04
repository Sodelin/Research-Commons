import G1SharpCoreCombCutChild

/-! Actual bridge-deletion blobs of the all-n family are already reduced.
Every module blob contains its two ORIGINAL hybrids; every taxon blob has
one port. The nonroot hybrid-port injection derives ≥3, with no supplied
reducedness or abstract module decomposition. -/
namespace G1SharpCoreCombReduced
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombAdmission G1SharpCoreCombCutChild G1CutChildPorts
open scoped Classical

theorem actual_module_same_blob (n : Nat) (hn : 4 ≤ n) (i : Module n) (k : LocalVertex) :
    (network n hn).graph.SameBlob (.inl (i,0)) (.inl (i,k)) := by
  let N := network n hn
  have h03 : N.graph.SameBlob (.inl (i,0)) (.inl (i,3)) :=
    N.graph.nonbridge_sameBlob (actual_hybrid_parent_nonbridge N (i,0)
      ((original_module_hybrid n hn i 3).mpr (Or.inl rfl)))
  have h23 : N.graph.SameBlob (.inl (i,2)) (.inl (i,3)) :=
    N.graph.nonbridge_sameBlob (actual_hybrid_parent_nonbridge N (i,4)
      ((original_module_hybrid n hn i 3).mpr (Or.inl rfl)))
  have h24 : N.graph.SameBlob (.inl (i,2)) (.inl (i,4)) :=
    N.graph.nonbridge_sameBlob (actual_hybrid_parent_nonbridge N (i,5)
      ((original_module_hybrid n hn i 4).mpr (Or.inr rfl)))
  have h14 : N.graph.SameBlob (.inl (i,1)) (.inl (i,4)) :=
    N.graph.nonbridge_sameBlob (actual_hybrid_parent_nonbridge N (i,2)
      ((original_module_hybrid n hn i 4).mpr (Or.inr rfl)))
  have h02 := h03.trans (N.graph.sameBlob_symm h23)
  have h04 := h02.trans h24
  fin_cases k
  · exact .refl
  · exact h04.trans (N.graph.sameBlob_symm h14)
  · exact h02
  · exact h03
  · exact h04

theorem actual_module_blob_two_hybrids (n : Nat) (hn : 4 ≤ n) (i : Module n) (k : LocalVertex) :
    2 ≤ (blobHybrids (network n hn) ((network n hn).graph.blobOf (.inl (i,k)))).card := by
  let N := network n hn
  have hsub : ({Sum.inl (i,(3:LocalVertex)),Sum.inl (i,(4:LocalVertex))} : Finset (Vertex n)) ⊆
      blobHybrids N (N.graph.blobOf (.inl (i,k))) := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    all_goals apply Finset.mem_filter.mpr
    all_goals refine ⟨Finset.mem_univ _,?_,?_⟩
    · exact (original_module_hybrid n hn i 3).mpr (Or.inl rfl)
    · exact Quotient.sound ((N.graph.sameBlob_symm (actual_module_same_blob n hn i 3)).trans (actual_module_same_blob n hn i k))
    · exact (original_module_hybrid n hn i 4).mpr (Or.inr rfl)
    · exact Quotient.sound ((N.graph.sameBlob_symm (actual_module_same_blob n hn i 4)).trans (actual_module_same_blob n hn i k))
  have hc := Finset.card_le_card hsub
  simpa using hc

lemma actual_leaf_port_one {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X) (x : X) :
    Fintype.card (N.BlobPort (N.graph.blobOf (N.leaf x))) = 1 := by
  rw [actual_quotient_port_card]
  have hset : allPorts N (N.graph.blobOf (N.leaf x)) =
      Finset.univ.filter (fun e : E => N.graph.target e = N.leaf x) := by
    ext e
    simp only [allPorts,outPorts,inPorts,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨hb,hs⟩ | ⟨hb,ht⟩)
      · exact False.elim (N.no_edge_source_leaf x e ((N.blobOf_leaf_eq_iff x _).mp hs))
      · exact (N.blobOf_leaf_eq_iff x _).mp ht
    · intro he
      exact Or.inr ⟨N.leaf_incoming_bridge x he,congrArg N.graph.blobOf he⟩
  rw [hset]
  exact (N.leaf_degrees x).1

theorem actual_reduced (n : Nat) (hn : 4 ≤ n) :
    ∀ b : (network n hn).graph.Blob, b ≠ (network n hn).graph.blobOf (network n hn).root →
      Fintype.card ((network n hn).BlobPort b) ≠ 2 := by
  intro b hb
  induction b using Quotient.inductionOn with
  | h v =>
    cases v with
    | inl pair =>
      rcases pair with ⟨i,k⟩
      have hhy := actual_module_blob_two_hybrids n hn i k
      have hp := actual_nonroot_hybrid_port_bound (network n hn) (actual_cut_child n hn) _ hb
      rw [← actual_quotient_port_card] at hp
      change (blobHybrids (network n hn) ((network n hn).graph.blobOf (.inl (i,k)))).card + 1 ≤
        Fintype.card ((network n hn).BlobPort ((network n hn).graph.blobOf (.inl (i,k)))) at hp
      change Fintype.card ((network n hn).BlobPort ((network n hn).graph.blobOf (.inl (i,k)))) ≠ 2
      omega
    | inr x =>
      change Fintype.card ((network n hn).BlobPort ((network n hn).graph.blobOf ((network n hn).leaf x))) ≠ 2
      rw [actual_leaf_port_one]
      decide

#print axioms actual_reduced
end G1SharpCoreCombReduced
