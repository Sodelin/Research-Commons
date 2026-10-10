import G1LiteralSemidirectedPhysicalCutReadout

/-! Literal marked switching/delete/root-suppression CUT readouts coincide
with the complete rooted switching tree serialization. The sole-root-arc
case is removed only because it has ALL taxa on one side; the two-root-arc
case is identified by actual complementary graph components. -/
namespace G1SemidirectedSwitchingCutsEqualRooted
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open G1ActualFormerRootPorts G1FormerRootHybridDirections G1LiteralSemidirectedRootSuppression
open G1RootSubdivisionPlanarAdmission G1LiteralSemidirectedSwitchingTransport
open G1ActualRootedSwitchingPhysicalCuts G1ActualSelectedRootCutCases
open G1LiteralSemidirectedPhysicalCutReadout
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma mem_proper_edge_cut_image {A : Type*} [DecidableEq A] (edges : Finset A)
    (side : A → Finset X) (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ ((edges.image side).filter (fun D => D.Nonempty ∧ (panel \ D).Nonempty)).image
      (fun D => {D,panel \ D}) ↔
    ∃ e ∈ edges, (side e).Nonempty ∧ (panel \ side e).Nonempty ∧ {side e,panel \ side e} = cut := by
  simp only [Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨D,⟨⟨e,he,rfl⟩,hn,hc⟩,hcut⟩
    exact ⟨e,he,hn,hc,hcut⟩
  · rintro ⟨e,he,hn,hc,hcut⟩
    exact ⟨side e,⟨⟨e,he,rfl⟩,hn,hc⟩,hcut⟩

lemma mem_actual_rooted_physical_cuts (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) (cut : Finset (Finset X)) : cut ∈ actualRootedSwitchingPhysicalCuts N S panel ↔
    ∃ e : S.Edge, (actualSelectedTargetSide N S panel e).Nonempty ∧
      (panel \ actualSelectedTargetSide N S panel e).Nonempty ∧
      {actualSelectedTargetSide N S panel e,panel \ actualSelectedTargetSide N S panel e} = cut := by
  simp only [actualRootedSwitchingPhysicalCuts,mem_proper_edge_cut_image,Finset.mem_univ,true_and]

lemma mem_actual_semidirected_physical_cuts (N : RootedBinary V E X) (ports : RootPorts N)
    (M : SemidirectedSwitching N ports) (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ actualSemidirectedSwitchingPhysicalCuts N ports M panel ↔
    ∃ e : SuppressedEdge N, M.keep e ∧ (semidirectedCutSide N ports M panel e).Nonempty ∧
      (panel \ semidirectedCutSide N ports M panel e).Nonempty ∧
      {semidirectedCutSide N ports M panel e,panel \ semidirectedCutSide N ports M panel e} = cut := by
  simp only [actualSemidirectedSwitchingPhysicalCuts,mem_proper_edge_cut_image,Finset.mem_filter,Finset.mem_univ,true_and]

lemma actual_physical_side_original_target (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) (e : S.Edge) :
    actualSelectedTargetSide N S panel e = sampledDescendants N S panel (N.graph.target e.val) :=
  actual_selected_target_side_descendants N S panel e

/-- All cuts of ONE actual suppressed switching are the cuts of ONE original
rooted switching. No split union is used to infer whole-tree co-occurrence. -/
theorem actual_semidirected_switching_cuts_equal_rooted (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (panel : Finset X) :
    actualSemidirectedSwitchingPhysicalCuts N ports (toSemidirectedSwitching N ports S) panel =
      actualRootedSwitchingPhysicalCuts N S panel := by
  ext cut
  rw [mem_actual_semidirected_physical_cuts,mem_actual_rooted_physical_cuts]
  constructor
  · rintro ⟨e,hk,hn,hc,hcut⟩
    cases e with
    | inl e =>
      have hside := actual_kept_semidirected_side_original N ports S panel e hk
      rw [hside] at hn hc hcut
      exact ⟨⟨e.val,hk⟩,hn,hc,hcut⟩
    | inr e =>
      cases e
      have hside := actual_merged_semidirected_side_original N ports S panel hk.1
      rw [hside] at hn hc hcut
      exact ⟨⟨ports.first,hk.1⟩,hn,hc,hcut⟩
  · rintro ⟨e,hn,hc,hcut⟩
    rcases actual_original_edge_cases N ports e.val with hf | hs | hk
    · have hfkeep : S.keep ports.first := hf ▸ e.property
      have heq : e = ⟨ports.first,hfkeep⟩ := Subtype.ext hf
      rw [heq] at hn hc hcut
      have hskeep : S.keep ports.second := by
        by_contra hsnot
        rw [actual_physical_side_original_target,actual_single_root_arc_descendants_full N ports S hsnot] at hc
        simpa using hc
      have hside := actual_merged_semidirected_side_original N ports S panel hfkeep
      refine ⟨.inr (),⟨hfkeep,hskeep⟩,?_,?_,?_⟩ <;> rwa [hside]
    · have hskeep : S.keep ports.second := hs ▸ e.property
      have heq : e = ⟨ports.second,hskeep⟩ := Subtype.ext hs
      rw [heq] at hn hc hcut
      have hfkeep : S.keep ports.first := by
        by_contra hfnot
        have hfull : sampledDescendants N S panel (N.graph.target ports.second) = panel :=
          actual_single_root_arc_descendants_full N (reversePorts N ports) S hfnot panel
        rw [actual_physical_side_original_target,hfull] at hc
        simpa using hc
      let C := sampledDescendants N S panel (N.graph.target ports.first)
      have hsub : C ⊆ panel := Finset.filter_subset _ _
      have hdouble : panel \ (panel \ C) = C := Finset.sdiff_sdiff_eq_self hsub
      have hsecond := actual_two_selected_root_clusters_complement N ports S hfkeep hskeep panel
      have hfirst := actual_physical_side_original_target N S panel ⟨ports.first,hfkeep⟩
      have hside := (actual_merged_semidirected_side_original N ports S panel hfkeep).trans hfirst
      rw [actual_physical_side_original_target,hsecond] at hn hc hcut
      change (panel \ C).Nonempty at hn
      change (panel \ (panel \ C)).Nonempty at hc
      rw [hdouble] at hc
      change {panel \ C,panel \ (panel \ C)} = cut at hcut
      rw [hdouble] at hcut
      refine ⟨.inr (),⟨hfkeep,hskeep⟩,?_,?_,?_⟩
      · rw [hside]; exact hc
      · rw [hside]; exact hn
      · rw [hside]; exact (Finset.pair_comm C (panel \ C)).trans hcut
    · have hside := actual_kept_semidirected_side_original N ports S panel ⟨e.val,hk⟩ e.property
      refine ⟨.inl ⟨e.val,hk⟩,e.property,?_,?_,?_⟩ <;> rwa [hside]

#print axioms actual_semidirected_switching_cuts_equal_rooted
end G1SemidirectedSwitchingCutsEqualRooted
