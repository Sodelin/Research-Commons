import G1SemidirectedSwitchingCutsEqualRooted

/-! BOTH-DIRECTION binding of literal semidirected marked-switching cut
readouts to existing actual normalized rooted-partner readouts. Complete
co-occurring tree-cut families are bound BEFORE split unions and quartets;
the empty panel has no displayed labelled tree. No desired target equality
is a field or hypothesis, and no abstract split-compatible order substitutes
for a real graph switching. -/
namespace G1LiteralSemidirectedTargetReadoutBinding
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest GProgram.G5.Normalization
open UnifiedLean.Source.NativeFairCurrentPosition
open GProgram.G5.AttainedChronology
open G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression G1LiteralSemidirectedSwitchingTransport
open G1SemidirectedSwitchingRoundTrip G1ActualRootedSwitchingPhysicalCuts
open G1LiteralSemidirectedPhysicalCutReadout G1SemidirectedSwitchingCutsEqualRooted
open G1ActualDisplayedClusterSplitTransport G1ActualWholeUnrootedCutTreeFamily G1AcceptedNontrivialSplitTarget
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_semidirected_physical_cut_row_eq_evaluator (N : RootedBinary V E X) (ports : RootPorts N)
    (M : SemidirectedSwitching N ports) (panel : Finset X) {T : Genealogy X}
    (eval : PrunedAt N (toRootedSwitching N ports M) panel N.root (some T)) :
    actualSemidirectedSwitchingPhysicalCuts N ports M panel = rootSuppressedCuts T := by
  let S := toRootedSwitching N ports M
  have hc := actual_semidirected_cut_readout_keep_congr N ports
    (toSemidirectedSwitching N ports S) M (actual_semidirected_switching_round_trip N ports M) panel
  exact hc.symm.trans ((actual_semidirected_switching_cuts_equal_rooted N ports S panel).trans
    (actual_rooted_physical_cuts_iff_normalized_tree N S panel eval))

/-- One family member comes from ONE literal selected semidirected graph.
Empty-panel pruning produces no labelled tree, matching the actual evaluator. -/
def actualSemidirectedCutTreeFamily (N : RootedBinary V E X) (ports : RootPorts N) (panel : Finset X) :
    Set (Finset (Finset (Finset X))) :=
  {cuts | panel.Nonempty ∧ ∃ M : SemidirectedSwitching N ports,
    actualSemidirectedSwitchingPhysicalCuts N ports M panel = cuts}

/-- Full switching/delete/root-suppression correspondence to the WHOLE
unrooted cut-tree family, for every original sampled taxon panel. -/
theorem actual_semidirected_tree_family_iff_rooted (N : RootedBinary V E X) (C : Calendar N.graph)
    (ports : RootPorts N) (panel : Finset X) (cuts : Finset (Finset (Finset X))) :
    cuts ∈ actualSemidirectedCutTreeFamily N ports panel ↔
      cuts ∈ actualDisplayedUnrootedCutTreeFamily N C panel := by
  rw [actual_unrooted_cut_tree_family_iff_evaluator]
  constructor
  · rintro ⟨hn,M,hm⟩
    let S := toRootedSwitching N ports M
    obtain ⟨T,eval,_,_⟩ := nonempty_root_pruning_tree_exists N C S panel hn
    exact ⟨S,T,eval,(actual_semidirected_physical_cut_row_eq_evaluator N ports M panel eval).symm.trans hm⟩
  · rintro ⟨S,T,eval,hcuts⟩
    have hl : T.leaves = panel := by
      have h := prunedAt_exact_leaves N S panel eval
      rw [sampledDescendants_root] at h
      exact h
    refine ⟨hl ▸ tree_leaves_nonempty T,toSemidirectedSwitching N ports S,?_⟩
    exact (actual_semidirected_switching_cuts_equal_rooted N ports S panel).trans
      ((actual_rooted_physical_cuts_iff_normalized_tree N S panel eval).trans hcuts)

def actualSemidirectedNontrivialSplits (N : RootedBinary V E X) (ports : RootPorts N) (panel : Finset X) :
    Set (Finset (Finset X)) :=
  {cut | NontrivialCut cut ∧ ∃ cuts ∈ actualSemidirectedCutTreeFamily N ports panel, cut ∈ cuts}

theorem actual_semidirected_nontrivial_S_iff_rooted (N : RootedBinary V E X) (C : Calendar N.graph)
    (ports : RootPorts N) (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ actualSemidirectedNontrivialSplits N ports panel ↔ cut ∈ acceptedDisplayedSplits N panel := by
  change (NontrivialCut cut ∧ ∃ cuts ∈ actualSemidirectedCutTreeFamily N ports panel, cut ∈ cuts) ↔ _
  simp only [actual_semidirected_tree_family_iff_rooted N C ports panel]
  rw [acceptedDisplayedSplits,Finset.mem_filter,←actual_whole_cut_family_union_is_proper_split_union N C panel]
  simp only [Finset.mem_biUnion]
  exact and_comm

noncomputable def actualSemidirectedQuartets (N : RootedBinary V E X) (ports : RootPorts N)
    (q : Fin 4 ↪ X) : Finset Nanuq.Quartet.Resolution :=
  allResolutions.filter (fun r => ∃ M : SemidirectedSwitching N ports,
    ∃ cut ∈ actualSemidirectedSwitchingPhysicalCuts N ports M Finset.univ,
      cutDisplaysFirst cut ((resolutionPermutation r).trans q))

/-- Exact DISTINCT quartet support, from literal selected semidirected
edge deletion, equals the actual normalized/root-suppressed quartet target. -/
theorem actual_semidirected_Q_equals_rooted (N : RootedBinary V E X) (C : Calendar N.graph)
    (ports : RootPorts N) (q : Fin 4 ↪ X) :
    actualSemidirectedQuartets N ports q = normalizedDisplayedCutQuartets N q := by
  ext r
  simp only [actualSemidirectedQuartets,normalizedDisplayedCutQuartets,Finset.mem_filter,mem_allResolutions,true_and]
  constructor
  · rintro ⟨M,cut,hcut,hside⟩
    let S := toRootedSwitching N ports M
    obtain ⟨T,eval,_,_⟩ := nonempty_root_pruning_tree_exists N C S Finset.univ ⟨q 0,Finset.mem_univ _⟩
    refine ⟨S,T,eval,cut,?_,hside⟩
    rwa [actual_semidirected_physical_cut_row_eq_evaluator N ports M Finset.univ eval] at hcut
  · rintro ⟨S,T,eval,cut,hcut,hside⟩
    refine ⟨toSemidirectedSwitching N ports S,cut,?_,hside⟩
    rwa [actual_semidirected_switching_cuts_equal_rooted N ports S Finset.univ,
      actual_rooted_physical_cuts_iff_normalized_tree N S Finset.univ eval]

#print axioms actual_semidirected_tree_family_iff_rooted
#print axioms actual_semidirected_Q_equals_rooted
end G1LiteralSemidirectedTargetReadoutBinding
