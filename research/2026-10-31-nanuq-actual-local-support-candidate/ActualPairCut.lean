import ActualCrossingCuts

/-! UNCOMPILED literal original switching-edge readout for the queried FIRST
pair. No choice frequency or syntactic-edge identification is used. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.GraphSyntax
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem actual_first_pair_cut_iff (N : RootedBinary V E X) (q : Fin 4 ↪ X) :
    Resolution.xy_zw ∈ N.rawDisplayedQuartets q ↔
      ∃ S : N.Switching, ∃ e : S.Edge,
        (S.graph.DReach (S.graph.target e) (N.leaf (q 0)) ∧
         S.graph.DReach (S.graph.target e) (N.leaf (q 1)) ∧
         ¬S.graph.DReach (S.graph.target e) (N.leaf (q 2)) ∧
         ¬S.graph.DReach (S.graph.target e) (N.leaf (q 3))) ∨
        (¬S.graph.DReach (S.graph.target e) (N.leaf (q 0)) ∧
         ¬S.graph.DReach (S.graph.target e) (N.leaf (q 1)) ∧
         S.graph.DReach (S.graph.target e) (N.leaf (q 2)) ∧
         S.graph.DReach (S.graph.target e) (N.leaf (q 3))) := by
  rw [actual_resolution_mem_iff]
  constructor
  · rintro ⟨S,e,he,h|h⟩
    · refine ⟨S,e,Or.inr ?_⟩
      exact ⟨(source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mp h.1,
        (source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mp h.2.1,
        (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mp h.2.2.1,
        (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mp h.2.2.2⟩
    · refine ⟨S,e,Or.inl ?_⟩
      exact ⟨(target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mp h.2.2.1,
        (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mp h.2.2.2,
        (source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mp h.1,
        (source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mp h.2.1⟩
  · rintro ⟨S,e,h|h⟩
    · refine ⟨S,e,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic e,
        Or.inr ?_⟩
      exact ⟨(source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mpr h.2.2.1,
        (source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mpr h.2.2.2,
        (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mpr h.1,
        (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mpr h.2.1⟩
    · refine ⟨S,e,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic e,
        Or.inl ?_⟩
      exact ⟨(source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mpr h.1,
        (source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
        N.root S.selected_rooted e _).mpr h.2.1,
        (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mpr h.2.2.1,
        (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e _).mpr h.2.2.2⟩

end Nanuq.ActualCutClusters
