import G1JointUnrankedForestAssembly

namespace G1JointForestPreservation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open G1NonrootBigonKernel G1JointSeparatedSourceGeometry G1ActualJointEpoch G1ActualJointProgram
open G1JointUnrankedForestAssembly
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma encoded_pruned_panel_separation (N : RootedBinary V E X) {sample : Copy → X}
    (s : State V E Copy) (hs : SourceValid N sample s) (inside outside : Finset Copy)
    (hpure : PrunedPanelSeparated s inside outside) :
    PrunedPanelSeparated (state (admittedCode N sample s hs)) inside outside := by
  intro l hl
  have hl' : l ∈ s.live := hl
  have hg : (state (admittedCode N sample s hs)).genealogy l = s.genealogy l :=
    decode_encode_live_genealogy N.root s hs.forest hl'
  rw [hg]
  exact hpure l hl'

lemma actual_boundary_pruned_panel_separation (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) (inside outside : Finset Copy)
    (hpure : PrunedPanelSeparated (state s) inside outside) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N op s).support) : PrunedPanelSeparated (state d) inside outside := by
  cases op with
  | exit e =>
      have he : d = exitCode N s e := by simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact encoded_pruned_panel_separation N _ (exitEdge_source_valid N sample _ s.property e) inside outside hpure
  | ordinary e deg =>
      have he : d = ordinaryCode N s e := by simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact encoded_pruned_panel_separation N _ (enterEdge_source_valid N sample _ s.property e) inside outside hpure
  | root =>
      have he : d = rootCode N s := by simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact encoded_pruned_panel_separation N _ (enterRoot_source_valid N sample _ s.property) inside outside hpure
  | common H =>
      have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact encoded_pruned_panel_separation N _ (pulse_source_valid H sample _ s.property _) inside outside hpure
  | independent H gamma =>
      obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      rw [← hc]
      exact encoded_pruned_panel_separation N _ (pulse_source_valid H sample _ s.property coin) inside outside hpure

lemma actual_agenda_pruned_panel_separation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hagenda : SeparatedAgenda N r inside outside ops s)
    (hpure : PrunedPanelSeparated (state s) inside outside) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) : PrunedPanelSeparated (state d) inside outside := by
  induction ops generalizing s with
  | nil =>
      have he : d = s := by simpa [sourceProgram,PMF.mem_support_pure_iff] using hd
      exact he ▸ hpure
  | cons op ops ih =>
      obtain ⟨hsep,htail⟩ := hagenda
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      apply ih z (htail z hz) _ hdz
      cases op with
      | interval t =>
          exact population_separated_pruned_panels (state z) z.property.forest inside outside
            (actual_epoch_separation N r inside outside t s hsep hz)
      | boundary b => exact actual_boundary_pruned_panel_separation N b s inside outside hpure hz

lemma current_root_panel_prune_none (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hkeep : keep ⊆ s.live) {l : Copy} (hl : l ∈ s.live)
    (hn : l ∉ keep) : (s.genealogy l).prune keep = none := by
  apply (UnifiedLean.Source.SourceForestSilentPruning.prune_none_iff_no_selected_leaves keep (s.genealogy l)).mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hleaf,hxkeep⟩ := Finset.mem_inter.mp hx
  have hxanc := (hs.leaf_fiber l hl x).mp hleaf
  have hxrep := hs.representative x (hkeep hxkeep)
  have he : x = l := hxrep.symm.trans hxanc
  exact hn (he ▸ hxkeep)

lemma current_root_partition_pure (s : State V E Copy) (hs : Valid s)
    (inside outside : Finset Copy) (hpart : inside ∪ outside = s.live)
    (hdis : Disjoint inside outside) : PrunedPanelSeparated s inside outside := by
  have hi : inside ⊆ s.live := hpart ▸ Finset.subset_union_left
  have ho : outside ⊆ s.live := hpart ▸ Finset.subset_union_right
  intro l hl
  by_cases hli : l ∈ inside
  · right
    exact current_root_panel_prune_none s hs outside ho hl
      (fun hlo => Finset.disjoint_left.mp hdis hli hlo)
  · left
    exact current_root_panel_prune_none s hs inside hi hl hli

#print axioms actual_agenda_pruned_panel_separation
#print axioms current_root_partition_pure
end G1JointForestPreservation
