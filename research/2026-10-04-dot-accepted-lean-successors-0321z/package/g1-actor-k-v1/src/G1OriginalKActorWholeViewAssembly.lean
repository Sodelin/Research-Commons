import G1CanonicalKActorExteriorHistory

/-! Reconstruct the WHOLE original causal quotient from a K-only actor and
the actual original exterior endpoint. No hidden live identifier/orientation
is demanded by the close interface; every original label/population survives. -/
namespace G1OriginalKActorWholeViewAssembly
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalOpaqueExteriorView G1OriginalCurrentRootReconstruction G1ContextualForestReplacement
open G1JointUnrankedForestAssembly G1SameOriginalExteriorContinuation G1UnrankedSingleExitLabel
open G1UnrankedSourceView G1OriginalWholeCausalView G1OriginalOpaqueKActorOutput
open scoped Classical
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

lemma actual_original_cohort_prune_none (initial d : State V E Copy)
    (hi : Valid initial) (hd : Valid d) (hr : Reconstructs initial.genealogy initial.live d)
    (roots : Finset Copy) (l : Copy) (hl : l ∈ d.live)
    (hn : (d.genealogy l).prune roots = none) :
    (d.genealogy l).prune (originalExteriorCopies initial roots) = none := by
  apply (prune_none_iff_no_selected_leaves _ _).mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxleaf,hxcohort⟩ := Finset.mem_inter.mp hx
  have hroot : initial.ancestor x ∈ roots := (Finset.mem_filter.mp hxcohort).2
  have howner : d.ancestor x = l := (hd.leaf_fiber l hl x).mp hxleaf
  have hco := actual_reconstruction_cohort initial d hi hd hr x
  have hrootleaf : initial.ancestor x ∈ (d.genealogy l).leaves :=
    (hd.leaf_fiber l hl _).mpr (hco.symm.trans howner)
  have hm := Finset.mem_inter.mpr ⟨hrootleaf,hroot⟩
  rw [(prune_none_iff_no_selected_leaves _ _).mp hn] at hm
  exact Finset.notMem_empty _ hm

theorem actual_original_cohort_purity (initial d : State V E Copy)
    (hi : Valid initial) (hd : Valid d) (hr : Reconstructs initial.genealogy initial.live d)
    (inside outside : Finset Copy) (pure : PrunedPanelSeparated d inside outside) :
    PrunedPanelSeparated d (originalExteriorCopies initial inside) (originalExteriorCopies initial outside) := by
  intro l hl
  exact (pure l hl).imp (actual_original_cohort_prune_none initial d hi hd hr inside l hl)
    (actual_original_cohort_prune_none initial d hi hd hr outside l hl)

lemma actual_original_cohort_cover (initial : State V E Copy) (hi : Valid initial)
    (inside outside : Finset Copy) (partition : inside ∪ outside = initial.live) :
    originalExteriorCopies initial inside ∪ originalExteriorCopies initial outside = Finset.univ := by
  ext x
  have hx : initial.ancestor x ∈ inside ∪ outside := partition.symm ▸ hi.ancestor_live x
  simpa only [originalExteriorCopies,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,
    iff_true] using Finset.mem_union.mp hx

noncomputable def closeOriginalKActor (initial : State V E Copy) (inside : Finset Copy)
    (exit : Location V E) (K : Finset (UnrankedTree Copy)) (outside : G1UnrankedSourceView.UnrankedView V E Copy) :=
  unrankedJoinedPanelView (originalExteriorCopies initial inside)
    (originalActorKView initial inside exit K,outside)

theorem actual_K_only_actor_whole_original_close (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (initial : Code N sample)
    (inside outside : Finset Copy) (partition : inside ∪ outside = (state initial).live)
    (exit : Location V E) {d : Code N sample} (hd : d ∈ (sourceProgram N r phase initial).support)
    (pure : PrunedPanelSeparated (state d) inside outside)
    (single : ∀ x ∈ inside, copyLocation (state d) x = exit) :
    closeOriginalKActor (state initial) inside exit (sourceUnrankedForest (state d) inside)
      (unrankedView (selectedView (state d) (originalExteriorCopies (state initial) outside))) =
      wholeOriginalView N d := by
  have hr := actual_program_reconstruction_support N r phase initial hd
  have hactor := actual_original_opaque_K_actor_output (state initial) (state d)
    initial.property.forest d.property.forest hr inside outside partition pure exit single
    (actual_program_register_support N r phase initial hd)
  have hpure := actual_original_cohort_purity (state initial) (state d)
    initial.property.forest d.property.forest hr inside outside pure
  have hview := actual_joined_panel_view (state d) d.property.forest
    (originalExteriorCopies (state initial) inside) (originalExteriorCopies (state initial) outside) hpure
  rw [actual_original_cohort_cover (state initial) initial.property.forest inside outside partition] at hview
  rw [closeOriginalKActor,hactor]
  exact (actual_unranked_joined_panel (originalExteriorCopies (state initial) inside)
    (selectedView (state d) (originalExteriorCopies (state initial) inside),
      selectedView (state d) (originalExteriorCopies (state initial) outside))).symm.trans
        (congrArg unrankedView hview.symm)

#print axioms actual_original_cohort_purity
#print axioms actual_K_only_actor_whole_original_close
end G1OriginalKActorWholeViewAssembly
