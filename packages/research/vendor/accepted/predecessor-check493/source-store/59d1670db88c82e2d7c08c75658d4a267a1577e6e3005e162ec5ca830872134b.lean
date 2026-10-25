import G1ActualHistoryEnrichedKMacro

/-! The actual full original unranked source checkpoint trajectory factors
through its full labelled causal view. Fixed original exterior panels have
representation-independent JOINT history and final-interface laws. -/
namespace G1OriginalHistoryQuotient
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualJointProgram G1ActualJointStageHistory G1UnrankedSourceView
open G1UnrankedActualGenerator G1UnrankedActualFuture G1OriginalWholeCausalView
open G1UnrankedExteriorHistoryKInsertion
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def unrankedStageHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N) → UnrankedIndex N sample Finset.univ →
      PMF (List (UnrankedIndex N sample Finset.univ))
  | [],v => PMF.pure [v]
  | op::ops,v => (unrankedProgramStep N r Finset.univ op v).bind
      (fun w => (unrankedStageHistory N r ops w).map (List.cons v))

theorem actual_unranked_full_stage_history (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceStageHistory N r ops s).map (List.map (unrankedProjection N Finset.univ)) =
      unrankedStageHistory N r ops (unrankedProjection N Finset.univ s) := by
  induction ops generalizing s with
  | nil => simp [sourceStageHistory,unrankedStageHistory,PMF.pure_map]
  | cons op ops ih =>
    rw [sourceStageHistory,PMF.map_bind]
    have hcons (d : Code N sample) :
        ((sourceStageHistory N r ops d).map (List.cons s)).map (List.map (unrankedProjection N Finset.univ)) =
        (unrankedStageHistory N r ops (unrankedProjection N Finset.univ d)).map
          (List.cons (unrankedProjection N Finset.univ s)) := by
      rw [PMF.map_comp]
      have he : List.map (unrankedProjection N Finset.univ) ∘ List.cons s =
          List.cons (unrankedProjection N Finset.univ s) ∘ List.map (unrankedProjection N Finset.univ) := by
        funext tr; rfl
      rw [he,←PMF.map_comp,ih]
    simp_rw [hcons]
    change (sourceProgramStep N r op s).bind
      ((fun v => (unrankedStageHistory N r ops v).map (List.cons (unrankedProjection N Finset.univ s))) ∘
        unrankedProjection N Finset.univ) = _
    rw [←PMF.bind_map,actual_unranked_program_step]
    rfl

theorem actual_whole_stage_history_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s z : Code N sample)
    (h : wholeOriginalView N s = wholeOriginalView N z) :
    (sourceStageHistory N r ops s).map (List.map (wholeOriginalView N)) =
      (sourceStageHistory N r ops z).map (List.map (wholeOriginalView N)) := by
  have hi : unrankedProjection N Finset.univ s = unrankedProjection N Finset.univ z := Subtype.ext h
  have hs := congrArg (fun p => p.map (List.map Subtype.val)) (actual_unranked_full_stage_history N r ops s)
  have hz := congrArg (fun p => p.map (List.map Subtype.val)) (actual_unranked_full_stage_history N r ops z)
  simp only [PMF.map_comp,List.map_map,Function.comp_def] at hs hz
  rw [hi] at hs
  exact hs.trans hz.symm

noncomputable def restrictWholeView (keep : Finset Copy) (v : UnrankedView V E Copy) : UnrankedView V E Copy where
  genealogy x := if x ∈ keep then (v.genealogy x).bind (pruneTree keep) else none
  population x := if x ∈ keep then v.population x else none
  register := v.register

lemma actual_restrict_whole_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) :
    restrictWholeView keep (wholeOriginalView N s) = unrankedView (selectedView (state s) keep) := by
  apply UnrankedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · simp only [restrictWholeView,wholeOriginalView,unrankedView,selectedView,selectedGenealogy,
        if_pos hx,if_pos (Finset.mem_univ x),prune_all,optionUnranked,Option.map_some,Option.bind_some]
      rfl
    · simp [restrictWholeView,unrankedView,selectedView,selectedGenealogy,hx,optionUnranked]
  · funext x
    simp [restrictWholeView,wholeOriginalView,unrankedView,selectedView,selectedLocation]
  · rfl

noncomputable def originalObservedPhaseRow (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (outside : Finset Copy) (s : Code N sample) :
    PMF (List (UnrankedView V E Copy) × Code N sample) :=
  (sourceStageHistory N r phase s).map (fun tr => (exteriorHistory N outside tr,tr.getLastD s))

noncomputable def historyFinalView (N : RootedBinary V E X) {sample : Copy → X}
    (v : List (UnrankedView V E Copy) × Code N sample) := (v.1,wholeOriginalView N v.2)

/-- Fixed original exterior panels reveal full clades/populations/register at
EVERY original checkpoint, and remain JOINT with the whole final causal view. -/
theorem actual_original_observed_history_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (outside : Finset Copy)
    (s z : Code N sample) (h : wholeOriginalView N s = wholeOriginalView N z) :
    (originalObservedPhaseRow N r phase outside s).map (historyFinalView N) =
      (originalObservedPhaseRow N r phase outside z).map (historyFinalView N) := by
  let observe := fun tr : List (UnrankedView V E Copy) =>
    (tr.map (restrictWholeView outside),tr.getLastD (wholeOriginalView N s))
  have hs : (originalObservedPhaseRow N r phase outside s).map (historyFinalView N) =
      ((sourceStageHistory N r phase s).map (List.map (wholeOriginalView N))).map observe := by
    rw [originalObservedPhaseRow,PMF.map_comp,PMF.map_comp]
    congr 1
    funext tr
    simp only [observe,historyFinalView,Function.comp_apply,List.map_map,List.getLastD_map,exteriorHistory]
    congr 1
    apply List.map_congr_left
    intro d _
    exact (actual_restrict_whole_view N outside d).symm
  have hz : (originalObservedPhaseRow N r phase outside z).map (historyFinalView N) =
      ((sourceStageHistory N r phase z).map (List.map (wholeOriginalView N))).map observe := by
    rw [originalObservedPhaseRow,PMF.map_comp,PMF.map_comp]
    congr 1
    funext tr
    simp only [observe,historyFinalView,Function.comp_apply,List.map_map,List.getLastD_map,exteriorHistory]
    apply Prod.ext
    · apply List.map_congr_left
      intro d _
      exact (actual_restrict_whole_view N outside d).symm
    · calc
        wholeOriginalView N (tr.getLastD z) =
          (tr.map (wholeOriginalView N)).getLastD (wholeOriginalView N z) := (List.getLastD_map).symm
        _ = (tr.map (wholeOriginalView N)).getLastD (wholeOriginalView N s) := by rw [h]
        _ = wholeOriginalView N (tr.getLastD s) := List.getLastD_map
  rw [hs,hz,actual_whole_stage_history_row_independent N r phase s z h]

#print axioms actual_original_observed_history_row_independent
end G1OriginalHistoryQuotient
