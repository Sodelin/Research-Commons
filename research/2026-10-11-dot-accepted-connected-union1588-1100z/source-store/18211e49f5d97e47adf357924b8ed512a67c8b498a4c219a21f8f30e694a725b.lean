import G1OriginalKActorWholeViewAssembly

/-! K-only actor close through the SAME actual original future and unbounded
ancestral completion, jointly with EVERY original exterior checkpoint. The
physical root condition is on REAL original source support only. -/
namespace G1KOnlyActorSameCompletedFuture
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalOpaqueExteriorView G1OriginalExteriorHistoryProduct G1UnrankedSourceView
open G1OriginalWholeCausalView G1SourceMacroActualCompletion G1ActualKProductInsertion
open G1ActualJointEpoch G1ActualJointProgram G1ActualJointStageHistory G1ActualHistoryEnrichedKMacro
open G1OriginalKActorWholeViewAssembly
open scoped Classical
variable {V E X Copy Obs : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def actualKActorCompletedHistoryRow (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase future : List (ProgramStep N)) (initial : Code N sample)
    (inside outside : Finset Copy) (hi : inside ⊆ (state initial).live) (exit : Location V E)
    (readout : UnrankedView V E Copy → Obs) : PMF (List (UnrankedView V E Copy) × Obs) :=
  (independentProduct (actualCurrentRootK N r phase initial inside hi)
    ((sourceStageHistory N r phase initial).map (originalExteriorHistory N initial outside))).bind
      (fun data => (actualCompletedTerminal N r future initial readout
        (closeOriginalKActor (state initial) inside exit data.1
          (data.2.getLastD (unrankedView (selectedView (state initial)
            (originalExteriorCopies (state initial) outside)))))).map (fun o => (data.2,o)))

theorem actual_K_only_actor_same_completed_original_future (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase future : List (ProgramStep N)) (initial : Code N sample)
    (inside outside : Finset Copy) (hi : inside ⊆ (state initial).live)
    (partition : inside ∪ outside = (state initial).live)
    (sep : SeparatedAgenda N r inside outside phase initial) (exit : Location V E)
    (physical : ∀ d ∈ (sourceProgram N r phase initial).support,
      G1JointUnrankedForestAssembly.PrunedPanelSeparated (state d) inside outside ∧
        ∀ x ∈ inside, copyLocation (state d) x = exit)
    (rootSupport : ∀ d ∈ (sourceProgram N r phase initial).support,
      ∀ z ∈ (sourceProgram N r future d).support, AncestralRoot N z)
    (readout : UnrankedView V E Copy → Obs) :
    (sourceStageHistory N r phase initial).bind (fun tr =>
      (((sourceProgram N r future (tr.getLastD initial)).bind (completionKernel N r)).map
        (fun z => readout (wholeOriginalView N z))).map
          (fun o => (originalExteriorHistory N initial outside tr,o))) =
      actualKActorCompletedHistoryRow N r phase future initial inside outside hi exit readout := by
  let finish := fun data : Finset (UnrankedTree Copy) × List (UnrankedView V E Copy) =>
    (actualCompletedTerminal N r future initial readout
      (closeOriginalKActor (state initial) inside exit data.1
        (data.2.getLastD (unrankedView (selectedView (state initial)
          (originalExteriorCopies (state initial) outside)))))).map (fun o => (data.2,o))
  have hprod := actual_K_original_whole_exterior_history_product N r inside outside phase initial hi
    partition sep (fun d hd => (physical d hd).1)
  calc
    _ = (sourceStageHistory N r phase initial).bind (fun tr => finish
        (sourceUnrankedForest (state (tr.getLastD initial)) inside,originalExteriorHistory N initial outside tr)) := by
      apply bind_eq_of_eq_on_support
      intro tr ht
      have hd := real_history_end_support N r phase initial tr ht
      have hclose := actual_K_only_actor_whole_original_close N r phase initial inside outside partition exit hd
        (physical _ hd).1 (physical _ hd).2
      dsimp only [finish]
      simp only [originalExteriorHistory,List.getLastD_map]
      rw [hclose,actual_completed_terminal_at_source N r future initial (tr.getLastD initial)
        (rootSupport _ hd)]
    _ = ((sourceStageHistory N r phase initial).map (fun tr =>
        (sourceUnrankedForest (state (tr.getLastD initial)) inside,
          originalExteriorHistory N initial outside tr))).bind finish := by rw [PMF.bind_map]; rfl
    _ = _ := by rw [hprod]; rfl

#print axioms actual_K_only_actor_same_completed_original_future
end G1KOnlyActorSameCompletedFuture
