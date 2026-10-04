import G1OriginalForestKOnlyInsertion

/-!
# K insertion retaining the whole actual exterior stage trajectory

Contributor: dot, 2026-10-03. Each original agenda checkpoint retains its
complete exterior unranked genealogy, population and SAME-register state.
Individual within-epoch clock/calendar event-time readers remain outside G1.
-/
namespace G1UnrankedExteriorHistoryKInsertion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1UnrankedActualFuture G1ActualUnrankedKMacro
open G1ActualJointProgram G1ActualJointEpoch G1ActualJointOpaqueContext
open G1ActualJointStageHistory G1ActualKProductInsertion
open G1ContextualForestReplacement
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma history_last_default {A : Type*} (tr : List A) (hne : tr ≠ []) (a b : A) :
    tr.getLastD a = tr.getLastD b := by
  cases tr with
  | nil => exact False.elim (hne rfl)
  | cons x xs => simp only [List.getLastD_cons]

theorem actual_source_history_nonempty (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    {tr : List (Code N sample)} (ht : tr ∈ (sourceStageHistory N r ops s).support) : tr ≠ [] := by
  cases ops with
  | nil =>
      have he : tr = [s] := by simpa [sourceStageHistory] using ht
      rw [he]
      simp
  | cons op ops =>
      obtain ⟨d,hd,ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      obtain ⟨tr,htr,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
      simp

theorem actual_source_history_end (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceStageHistory N r ops s).map (fun tr => tr.getLastD s) = sourceProgram N r ops s := by
  induction ops generalizing s with
  | nil => simp [sourceStageHistory,sourceProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [sourceStageHistory,sourceProgram,PMF.map_bind]
      congr 1
      funext d
      rw [PMF.map_comp]
      calc
        _ = (sourceStageHistory N r ops d).map (fun tr => tr.getLastD d) := by
          apply map_eq_of_eq_on_support
          intro tr ht
          simp only [Function.comp_def,List.getLastD_cons]
          exact history_last_default tr (actual_source_history_nonempty N r ops d ht) s d
        _ = _ := ih d

noncomputable def exteriorHistory (N : RootedBinary V E X) {sample : Copy → X}
    (outside : Finset Copy) (tr : List (Code N sample)) : List (UnrankedView V E Copy) :=
  tr.map (fun d => unrankedView (selectedView (state d) outside))

/-- The complete actual exterior checkpoint trajectory is independent of the
component's full unranked K conditional on the exact original entering state.
The exterior trajectory is produced by its actual contemporaneous process. -/
theorem actual_K_whole_exterior_history_product (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (phase : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live)
    (hsep : SeparatedAgenda N r inside outside phase s) :
    (sourceStageHistory N r phase s).map (fun tr =>
      (sourceUnrankedForest (state (tr.getLastD s)) inside,exteriorHistory N outside tr)) =
      independentProduct (actualCurrentRootK N r phase s inside hi)
        ((sourceStageHistory N r phase s).map (exteriorHistory N outside)) := by
  let f := fun tr : List (SelectedIndex N sample inside) =>
    unrankedForest (tr.getLastD (projection N inside s)).val
  let g := fun tr : List (SelectedIndex N sample outside) =>
    tr.map (fun v => unrankedView v.val)
  have h := congrArg (fun p => p.map (fun v => (f v.1,g v.2)))
    (actual_joint_exterior_history_retained N r inside outside phase s hsep)
  rw [independentProduct_map] at h
  simp only [PMF.map_comp,Function.comp_def,f,g,List.getLastD_map,List.map_map] at h
  simp only [projection] at h
  have hk : (sourceStageHistory N r phase s).map
      (fun tr => sourceUnrankedForest (state (tr.getLastD s)) inside) =
      actualCurrentRootK N r phase s inside hi := by
    change (sourceStageHistory N r phase s).map
      ((fun d : Code N sample => sourceUnrankedForest (state d) inside) ∘
        (fun tr => tr.getLastD s)) = _
    rw [← PMF.map_comp,actual_source_history_end]
    unfold actualCurrentRootK
    rw [← actual_current_panel_program_law,PMF.map_comp]
    rfl
  change (sourceStageHistory N r phase s).map (fun tr =>
      (sourceUnrankedForest (state (tr.getLastD s)) inside,exteriorHistory N outside tr)) =
    independentProduct ((sourceStageHistory N r phase s).map
      (fun tr => sourceUnrankedForest (state (tr.getLastD s)) inside))
      ((sourceStageHistory N r phase s).map (exteriorHistory N outside)) at h
  rw [hk] at h
  exact h

/-- K-only insertion retains the ENTIRE actual exterior unranked checkpoint
history and then continues the SAME original process. The observer may retain
that exterior causal history, including old subtree/population/register data.
No independent reconstruction or resampling of its marginal is used. -/
theorem actual_K_whole_exterior_history_same_future {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live)
    (hsep : SeparatedAgenda N r inside outside phase s)
    (hphysical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (readout : List (UnrankedView V E Copy) → UnrankedView V E Copy → Obs) :
    (sourceStageHistory N r phase s).bind (fun tr =>
      (sourceProgram N r future (tr.getLastD s)).map (fun d =>
        readout (exteriorHistory N outside tr)
          (unrankedView (selectedView (state d) (inside ∪ outside))))) =
      (independentProduct (actualCurrentRootK N r phase s inside hi)
        ((sourceStageHistory N r phase s).map (exteriorHistory N outside))).bind
          (fun data => actualKContinuation N r inside outside p future s (readout data.2)
            (data.1,data.2.getLastD (unrankedView (selectedView (state s) outside)))) := by
  rw [← actual_K_whole_exterior_history_product N r inside outside phase s hi hsep,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro tr ht
  have hd : tr.getLastD s ∈ (sourceProgram N r phase s).support := by
    rw [← actual_source_history_end N r phase s]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tr,ht,rfl⟩
  have he : (exteriorHistory N outside tr).getLastD
      (unrankedView (selectedView (state s) outside)) =
      unrankedView (selectedView (state (tr.getLastD s)) outside) := List.getLastD_map
  simp only [Function.comp_apply,he]
  exact (actualKContinuation_at_actual_exit N r inside outside p future s
    (tr.getLastD s) (hphysical _ hd) (readout (exteriorHistory N outside tr))).symm

#print axioms actual_K_whole_exterior_history_product
#print axioms actual_K_whole_exterior_history_same_future
end G1UnrankedExteriorHistoryKInsertion
