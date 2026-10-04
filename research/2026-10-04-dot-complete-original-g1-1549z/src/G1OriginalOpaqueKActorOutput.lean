import G1KOnlyCurrentRootExitView

/-! K-only output restores EVERY original inside descendant-labelled opaque
tree, population and SAME register. Its only dynamic actor input is the true
CURRENT-root forest K; old descendant counts are unrestricted. -/
namespace G1OriginalOpaqueKActorOutput
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceForestSilentPruning
open G1UnrankedSourceView G1OriginalOpaqueExteriorView G1KOnlyCurrentRootExitView
open G1OriginalCurrentRootReconstruction G1ContextualForestReplacement
open G1ActualJointOpaqueContext G1ActualKProductInsertion
open scoped Classical
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def originalActorKView (initial : State V E Copy) (inside : Finset Copy)
    (exit : Location V E) (forest : Finset (UnrankedTree Copy)) : UnrankedView V E Copy :=
  opaqueExteriorView initial inside (currentRootExitView inside exit initial.register forest)

theorem actual_original_opaque_K_actor_output (initial d : State V E Copy)
    (hi : Valid initial) (hd : Valid d)
    (reconstructs : Reconstructs initial.genealogy initial.live d)
    (inside outside : Finset Copy) (partition : inside ∪ outside = initial.live)
    (pure : G1JointUnrankedForestAssembly.PrunedPanelSeparated d inside outside)
    (exit : Location V E) (single : ∀ x ∈ inside, copyLocation d x = exit)
    (sameRegister : d.register = initial.register) :
    originalActorKView initial inside exit (sourceUnrankedForest d inside) =
      unrankedView (selectedView d (originalExteriorCopies initial inside)) := by
  rw [originalActorKView,actual_current_root_exit_view d hd inside exit initial.register single sameRegister]
  apply actual_opaque_original_exterior_view initial d hi hd reconstructs outside inside
  · rw [Finset.union_comm]
    exact partition
  · intro l hl
    exact (pure l hl).symm

/-- The marginal K is the independently initialized CURRENT-root source,
with its own copy-dependent clock bound and actual original operations. -/
theorem actual_current_root_K_marginal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (initial : Code N sample)
    (inside : Finset Copy) (hi : inside ⊆ (state initial).live) :
    (sourceProgram N r phase initial).map (fun d => sourceUnrankedForest (state d) inside) =
      actualCurrentRootK N r phase initial inside hi := by
  rw [actualCurrentRootK,←actual_current_panel_program_law N r phase initial inside hi,PMF.map_comp]
  rfl

/-- Actual whole-original-descendant actor output equals the TRUE small K
grafted into the saved original input forest. Conditions are physical final
purity/single exit; the canonical frontier theorem derives them later. -/
theorem actual_private_original_row_is_K_graft (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (initial : Code N sample)
    (inside outside : Finset Copy) (hi : inside ⊆ (state initial).live)
    (partition : inside ∪ outside = (state initial).live) (exit : Location V E)
    (physical : ∀ d ∈ (sourceProgram N r phase initial).support,
      G1JointUnrankedForestAssembly.PrunedPanelSeparated (state d) inside outside ∧
        ∀ x ∈ inside, copyLocation (state d) x = exit) :
    (sourceProgram N r phase initial).map
      (fun d => unrankedView (selectedView (state d) (originalExteriorCopies (state initial) inside))) =
    (actualCurrentRootK N r phase initial inside hi).map (originalActorKView (state initial) inside exit) := by
  rw [←actual_current_root_K_marginal N r phase initial inside hi,PMF.map_comp]
  apply map_eq_of_eq_on_support
  intro d hd
  exact (actual_original_opaque_K_actor_output (state initial) (state d)
    initial.property.forest d.property.forest (actual_program_reconstruction_support N r phase initial hd)
    inside outside partition (physical d hd).1 exit (physical d hd).2
    (actual_program_register_support N r phase initial hd)).symm

#print axioms actual_private_original_row_is_K_graft
end G1OriginalOpaqueKActorOutput
