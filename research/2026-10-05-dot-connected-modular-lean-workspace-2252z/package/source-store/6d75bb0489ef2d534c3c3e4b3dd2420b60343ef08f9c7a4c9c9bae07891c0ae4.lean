import G1CanonicalOriginalKOnlyActorRow

/-! K-only original actor output is JOINT with EVERY original exterior
checkpoint, rather than a separate endpoint marginal. Initial opaque input
trees and the SAME original register are retained explicitly. -/
namespace G1KOnlyActorWholeExteriorHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1ActualJointProgram G1ActualJointEpoch G1ActualJointOpaqueContext G1ActualJointStageHistory
open G1OriginalOpaqueExteriorView G1OriginalExteriorHistoryProduct G1ActualHistoryEnrichedKMacro
open G1OriginalCurrentRootReconstruction G1ContextualForestReplacement G1ActualKProductInsertion
open G1OriginalOpaqueKActorOutput
open scoped Classical
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

theorem actual_K_only_actor_original_outside_history_product (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (initial : Code N sample)
    (inside outside : Finset Copy) (hi : inside ⊆ (state initial).live)
    (partition : inside ∪ outside = (state initial).live)
    (sep : SeparatedAgenda N r inside outside phase initial) (exit : Location V E)
    (physical : ∀ d ∈ (sourceProgram N r phase initial).support,
      G1JointUnrankedForestAssembly.PrunedPanelSeparated (state d) inside outside ∧
        ∀ x ∈ inside, copyLocation (state d) x = exit) :
    (sourceStageHistory N r phase initial).map (fun tr =>
      (unrankedView (selectedView (state (tr.getLastD initial)) (originalExteriorCopies (state initial) inside)),
        originalExteriorHistory N initial outside tr)) =
      independentProduct
        ((actualCurrentRootK N r phase initial inside hi).map (originalActorKView (state initial) inside exit))
        ((sourceStageHistory N r phase initial).map (originalExteriorHistory N initial outside)) := by
  let actor := originalActorKView (state initial) inside exit
  have hprod := actual_K_original_whole_exterior_history_product N r inside outside phase initial hi
    partition sep (fun d hd => (physical d hd).1)
  calc
    _ = (sourceStageHistory N r phase initial).map (fun tr =>
        (actor (sourceUnrankedForest (state (tr.getLastD initial)) inside),
          originalExteriorHistory N initial outside tr)) := by
      apply map_eq_of_eq_on_support
      intro tr ht
      have hd := real_history_end_support N r phase initial tr ht
      apply Prod.ext
      · exact (actual_original_opaque_K_actor_output (state initial) (state (tr.getLastD initial))
          initial.property.forest (tr.getLastD initial).property.forest
          (actual_program_reconstruction_support N r phase initial hd) inside outside partition
          (physical _ hd).1 exit (physical _ hd).2 (actual_program_register_support N r phase initial hd)).symm
      · rfl
    _ = ((sourceStageHistory N r phase initial).map (fun tr =>
        (sourceUnrankedForest (state (tr.getLastD initial)) inside,originalExteriorHistory N initial outside tr))).map
          (fun data => (actor data.1,data.2)) := by rw [PMF.map_comp]; rfl
    _ = _ := by
      rw [hprod]
      change (independentProduct _ _).map (fun data => (actor data.1,id data.2)) = _
      rw [independentProduct_map,PMF.map_id]

#print axioms actual_K_only_actor_original_outside_history_product
end G1KOnlyActorWholeExteriorHistory
