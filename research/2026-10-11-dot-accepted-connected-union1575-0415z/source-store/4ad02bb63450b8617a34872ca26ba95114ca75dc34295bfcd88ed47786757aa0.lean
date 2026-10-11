import G1ActualSelectedRootCutCases

/-! Literal semidirected displayed CUT readout: select real marked edge IDs,
delete ONE chosen selected edge, and retain its unordered proper taxon sides.
Dead unlabelled branches contribute no proper cut, and degree-two/root
suppression identifies equal cuts. No rooted target is used in the definition. -/
namespace G1LiteralSemidirectedPhysicalCutReadout
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression G1LiteralSemidirectedSwitchingTransport
open G1SemidirectedSwitchingRoundTrip G1SemidirectedSelectedRetainedCutPaths G1SemidirectedMergedRootCutPaths
open G1SelectedOriginalDeletionPathEquivalence G1ActualRootedSwitchingPhysicalCuts
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

def selectedCutSideVertex (N : RootedBinary V E X) (ports : RootPorts N) : SuppressedEdge N → SuppressedVertex N
  | .inl e => keptTarget N e
  | .inr _ => firstChild N ports

noncomputable def semidirectedCutSide (N : RootedBinary V E X) (ports : RootPorts N)
    (M : SemidirectedSwitching N ports) (panel : Finset X) (e : SuppressedEdge N) : Finset X :=
  panel.filter (fun x => (suppressedGraph N ports).UReach (fun f => M.keep f ∧ f ≠ e)
    (selectedCutSideVertex N ports e) (suppressedLeaf N x))

noncomputable def actualSemidirectedSwitchingPhysicalCuts (N : RootedBinary V E X) (ports : RootPorts N)
    (M : SemidirectedSwitching N ports) (panel : Finset X) : Finset (Finset (Finset X)) :=
  (((Finset.univ.filter M.keep).image (semidirectedCutSide N ports M panel)).filter
    (fun D => D.Nonempty ∧ (panel \ D).Nonempty)).image (fun D => {D,panel \ D})

lemma actual_kept_semidirected_side_original (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (panel : Finset X) (e : KeptEdge N) (hk : S.keep e.val) :
    semidirectedCutSide N ports (toSemidirectedSwitching N ports S) panel (.inl e) =
      actualSelectedTargetSide N S panel ⟨e.val,hk⟩ := by
  ext x
  simp only [semidirectedCutSide,actualSelectedTargetSide,Finset.mem_filter]
  apply and_congr_right
  intro _
  exact (actual_retained_selected_cut_path_iff N ports S e (keptTarget N e) (suppressedLeaf N x)).trans
    (actual_selected_without_iff_original N S ⟨e.val,hk⟩ (N.graph.target e.val) (N.leaf x)).symm

lemma actual_merged_semidirected_side_original (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (panel : Finset X) (hf : S.keep ports.first) :
    semidirectedCutSide N ports (toSemidirectedSwitching N ports S) panel (.inr ()) =
      actualSelectedTargetSide N S panel ⟨ports.first,hf⟩ := by
  ext x
  simp only [semidirectedCutSide,actualSelectedTargetSide,Finset.mem_filter]
  apply and_congr_right
  intro _
  exact (actual_merged_root_cut_path_iff N ports S (firstChild N ports) (suppressedLeaf N x)).trans
    (actual_selected_without_iff_original N S ⟨ports.first,hf⟩ (N.graph.target ports.first) (N.leaf x)).symm

lemma actual_semidirected_cut_readout_keep_congr (N : RootedBinary V E X) (ports : RootPorts N)
    (M L : SemidirectedSwitching N ports) (hkeep : ∀ e, M.keep e ↔ L.keep e) (panel : Finset X) :
    actualSemidirectedSwitchingPhysicalCuts N ports M panel = actualSemidirectedSwitchingPhysicalCuts N ports L panel := by
  have hk : M.keep = L.keep := funext (fun e => propext (hkeep e))
  have hs : semidirectedCutSide N ports M panel = semidirectedCutSide N ports L panel := by
    funext e
    simp only [semidirectedCutSide,hk]
  simp only [actualSemidirectedSwitchingPhysicalCuts,hk,hs]

#print axioms actual_kept_semidirected_side_original
end G1LiteralSemidirectedPhysicalCutReadout
