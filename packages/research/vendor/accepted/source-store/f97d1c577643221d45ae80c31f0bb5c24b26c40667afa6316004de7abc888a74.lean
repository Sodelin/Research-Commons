import G1OriginalOpaqueExteriorView
import G1UnrankedExteriorHistoryKInsertion

/-! The true CURRENT-root K is joint with the complete actual ORIGINAL exterior
descendant-labelled checkpoint trajectory. All initial opaque subtrees and Γ
are restored, and every trajectory checkpoint is real source support. -/
namespace G1OriginalExteriorHistoryProduct
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalCurrentRootReconstruction G1ContextualForestReplacement
open G1ActualJointProgram G1ActualJointEpoch G1JointSeparatedSourceGeometry
open G1JointUnrankedForestAssembly G1ActualJointStageHistory
open G1UnrankedSourceView G1UnrankedActualFuture G1UnrankedExteriorHistoryKInsertion
open G1ActualKProductInsertion G1OriginalOpaqueExteriorView
open G1ActualJointOpaqueContext
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_stage_history_checkpoint_properties (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (input : Copy → Genealogy Copy)
    (keep inside outside : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample)
    (hr : Reconstructs input keep (state s)) (sep : SeparatedAgenda N r inside outside ops s)
    (finalPure : ∀ d ∈ (sourceProgram N r ops s).support, PrunedPanelSeparated (state d) inside outside)
    {tr : List (Code N sample)} (ht : tr ∈ (sourceStageHistory N r ops s).support) :
    ∀ d ∈ tr, Reconstructs input keep (state d) ∧ PrunedPanelSeparated (state d) inside outside := by
  induction ops generalizing s tr with
  | nil =>
    have he : tr = [s] := by simpa [sourceStageHistory] using ht
    subst tr
    intro d hd
    have he : d = s := by simpa using hd
    subst d
    exact ⟨hr,finalPure s (by simp [sourceProgram])⟩
  | cons op ops ih =>
    obtain ⟨hsep,htail⟩ := sep
    obtain ⟨z,hz,ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
    obtain ⟨tail,htailSource,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
    have hzrec : Reconstructs input keep (state z) := by
      cases op with
      | interval t => exact actual_time_reconstruction_support N r input keep t s hr hz
      | boundary b => exact actual_boundary_reconstruction_support N input keep b s hr hz
    have tailPure : ∀ d ∈ (sourceProgram N r ops z).support, PrunedPanelSeparated (state d) inside outside := by
      intro d hd
      exact finalPure d ((PMF.mem_support_bind_iff _ _ _).mpr ⟨z,hz,hd⟩)
    intro d hd
    rcases List.mem_cons.mp hd with he | hd
    · subst d
      exact ⟨hr,population_separated_pruned_panels (state s) s.property.forest inside outside hsep⟩
    · exact ih z hzrec (htail z hz) tailPure htailSource d hd

noncomputable def originalExteriorHistory (N : RootedBinary V E X) {sample : Copy → X}
    (initial : Code N sample) (outside : Finset Copy) (tr : List (Code N sample)) :
    List (UnrankedView V E Copy) :=
  tr.map (fun d => unrankedView (selectedView (state d) (originalExteriorCopies (state initial) outside)))

theorem actual_original_exterior_history_lift (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (phase : List (ProgramStep N))
    (s : Code N sample) (partition : inside ∪ outside = (state s).live)
    (sep : SeparatedAgenda N r inside outside phase s)
    (finalPure : ∀ d ∈ (sourceProgram N r phase s).support, PrunedPanelSeparated (state d) inside outside)
    {tr : List (Code N sample)} (ht : tr ∈ (sourceStageHistory N r phase s).support) :
    (exteriorHistory N outside tr).map (opaqueExteriorView (state s) outside) =
      originalExteriorHistory N s outside tr := by
  simp only [exteriorHistory,originalExteriorHistory,List.map_map]
  apply List.map_congr_left
  intro d hd
  obtain ⟨hrec,hpure⟩ := actual_stage_history_checkpoint_properties N r (state s).genealogy
    (state s).live inside outside phase s (actual_initial_reconstruction (state s) s.property.forest)
    sep finalPure ht d hd
  exact actual_opaque_original_exterior_view (state s) (state d) s.property.forest d.property.forest
    hrec inside outside partition hpure

/-- This is a JOINT law with ALL original exterior checkpoint clades,
populations and Γ, computed from the true contemporaneous source trajectory.
An unrelated endpoint marginal or newly sampled static history is insufficient. -/
theorem actual_K_original_whole_exterior_history_product (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (inside outside : Finset Copy)
    (phase : List (ProgramStep N)) (s : Code N sample) (hi : inside ⊆ (state s).live)
    (partition : inside ∪ outside = (state s).live)
    (sep : SeparatedAgenda N r inside outside phase s)
    (finalPure : ∀ d ∈ (sourceProgram N r phase s).support, PrunedPanelSeparated (state d) inside outside) :
    (sourceStageHistory N r phase s).map (fun tr =>
      (sourceUnrankedForest (state (tr.getLastD s)) inside,originalExteriorHistory N s outside tr)) =
    independentProduct (actualCurrentRootK N r phase s inside hi)
      ((sourceStageHistory N r phase s).map (originalExteriorHistory N s outside)) := by
  let lift := fun v : Finset (UnrankedTree Copy) × List (UnrankedView V E Copy) =>
    (v.1,v.2.map (opaqueExteriorView (state s) outside))
  have h := congrArg (fun p => p.map lift)
    (actual_K_whole_exterior_history_product N r inside outside phase s hi sep)
  rw [PMF.map_comp] at h
  change (sourceStageHistory N r phase s).map
    ((fun v : Finset (UnrankedTree Copy) × List (UnrankedView V E Copy) =>
      (id v.1,List.map (opaqueExteriorView (state s) outside) v.2)) ∘
      (fun tr => (sourceUnrankedForest (state (tr.getLastD s)) inside,exteriorHistory N outside tr))) =
    (independentProduct (actualCurrentRootK N r phase s inside hi)
      ((sourceStageHistory N r phase s).map (exteriorHistory N outside))).map
        (fun v => (id v.1,List.map (opaqueExteriorView (state s) outside) v.2)) at h
  rw [independentProduct_map] at h
  have houtside : ((sourceStageHistory N r phase s).map (exteriorHistory N outside)).map
      (List.map (opaqueExteriorView (state s) outside)) =
      (sourceStageHistory N r phase s).map (originalExteriorHistory N s outside) := by
    rw [PMF.map_comp]
    apply map_eq_of_eq_on_support
    intro tr ht
    exact actual_original_exterior_history_lift N r inside outside phase s partition sep finalPure ht
  rw [PMF.map_id,houtside] at h
  calc
    _ = _ := by
      apply map_eq_of_eq_on_support
      intro tr ht
      exact congrArg (fun path => (sourceUnrankedForest (state (tr.getLastD s)) inside,path))
        (actual_original_exterior_history_lift N r inside outside phase s partition sep finalPure ht).symm
    _ = _ := h

#print axioms actual_original_exterior_history_lift
#print axioms actual_K_original_whole_exterior_history_product
end G1OriginalExteriorHistoryProduct
