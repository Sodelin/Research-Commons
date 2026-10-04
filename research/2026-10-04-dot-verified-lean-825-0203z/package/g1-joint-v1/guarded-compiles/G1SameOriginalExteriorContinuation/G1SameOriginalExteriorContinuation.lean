import G1ActualJointOpaqueContext

/-!
# Continue the SAME actual original source after the isolated joint phase

Contributor: dot, 2026-10-03. The continuation below is constructed from the
actual full-source program, including original boundary operations and rates.
Its view-representation independence is derived from actual source transport.
No desired continuation/output equality is assumed. This permits renewed
inside/exterior interactions and retained-root operations after the interface.
-/
namespace G1SameOriginalExteriorContinuation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open G1JointUnrankedForestAssembly G1JointForestPreservation G1ActualJointProgram
open G1ActualJointOpaqueContext G1ActualJointEpoch
open G1OpaqueSourceGrafting G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def joinedPanelView (inside : Finset Copy)
    (v : SelectedView V E Copy × SelectedView V E Copy) : SelectedView V E Copy where
  genealogy x := if x ∈ inside then v.1.genealogy x else v.2.genealogy x
  population x := if x ∈ inside then v.1.population x else v.2.population x
  register := v.1.register

lemma actual_joined_panel_view (s : State V E Copy) (hs : Valid s)
    (inside outside : Finset Copy) (hpure : PrunedPanelSeparated s inside outside) :
    selectedView s (inside ∪ outside) =
      joinedPanelView inside (selectedView s inside,selectedView s outside) := by
  apply SelectedView.ext
  · funext x
    by_cases hi : x ∈ inside
    · have hpI : (s.genealogy (s.ancestor x)).prune inside ≠ none := by
        intro hn
        have hx := Finset.mem_inter.mpr
          ⟨(hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl,hi⟩
        rw [(prune_none_iff_no_selected_leaves _ _).mp hn] at hx
        exact Finset.notMem_empty _ hx
      have hpO := (hpure _ (hs.ancestor_live x)).resolve_left hpI
      simp only [selectedView,selectedGenealogy,joinedPanelView,if_pos hi,
        Finset.mem_union,hi,true_or,if_true]
      exact prune_union_of_right_empty _ inside outside hpO
    · by_cases ho : x ∈ outside
      · have hpO : (s.genealogy (s.ancestor x)).prune outside ≠ none := by
          intro hn
          have hx := Finset.mem_inter.mpr
            ⟨(hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl,ho⟩
          rw [(prune_none_iff_no_selected_leaves _ _).mp hn] at hx
          exact Finset.notMem_empty _ hx
        have hpI := (hpure _ (hs.ancestor_live x)).resolve_right hpO
        simp only [selectedView,selectedGenealogy,joinedPanelView,if_neg hi,
          Finset.mem_union,hi,ho,false_or,if_true]
        exact prune_union_of_left_empty _ inside outside hpI
      · simp [selectedView,selectedGenealogy,joinedPanelView,hi,ho]
  · funext x
    by_cases hi : x ∈ inside <;> by_cases ho : x ∈ outside <;>
      simp [selectedView,selectedLocation,joinedPanelView,hi,ho]
  · rfl

lemma actual_future_view_row_independent {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (future : List (ProgramStep N)) (s z : Code N sample)
    (hv : selectedView (state s) keep = selectedView (state z) keep)
    (readout : SelectedView V E Copy → Obs) :
    (sourceProgram N r future s).map (fun d => readout (selectedView (state d) keep)) =
      (sourceProgram N r future z).map (fun d => readout (selectedView (state d) keep)) := by
  have he : projection N keep s = projection N keep z := Subtype.ext hv
  have hs := congrArg (fun p => p.map (fun v : SelectedIndex N sample keep => readout v.val))
    (actual_source_program_projection N r keep future s)
  have hz := congrArg (fun p => p.map (fun v : SelectedIndex N sample keep => readout v.val))
    (actual_source_program_projection N r keep future z)
  simp only [PMF.map_comp,Function.comp_def] at hs hz
  rw [he] at hs
  exact hs.trans hz.symm

noncomputable def actualOriginalContinuation {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (future : List (ProgramStep N)) (fallback : Code N sample)
    (readout : SelectedView V E Copy → Obs) (v : SelectedView V E Copy) : PMF Obs :=
  if h : ∃ d : Code N sample, selectedView (state d) keep = v then
    (sourceProgram N r future (Classical.choose h)).map
      (fun d => readout (selectedView (state d) keep))
  else (sourceProgram N r future fallback).map (fun d => readout (selectedView (state d) keep))

lemma actualOriginalContinuation_at_actual_view {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (future : List (ProgramStep N)) (fallback d : Code N sample)
    (readout : SelectedView V E Copy → Obs) :
    actualOriginalContinuation N r keep future fallback readout (selectedView (state d) keep) =
      (sourceProgram N r future d).map (fun z => readout (selectedView (state z) keep)) := by
  have hv : ∃ z : Code N sample, selectedView (state z) keep = selectedView (state d) keep := ⟨d,rfl⟩
  rw [actualOriginalContinuation,dif_pos hv]
  exact actual_future_view_row_independent N r keep future _ d (Classical.choose_spec hv) readout

lemma actual_source_program_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops future : List (ProgramStep N)) (s : Code N sample) :
    sourceProgram N r (ops ++ future) s =
      (sourceProgram N r ops s).bind (sourceProgram N r future) := by
  induction ops generalizing s with
  | nil => simp [sourceProgram]
  | cons op ops ih =>
      simp only [List.cons_append,sourceProgram,PMF.bind_bind]
      congr 1
      funext a
      exact ih a

/-- The source-derived inside K and simultaneously evolving exterior process
are inserted before the SAME actual original future program. Root-blob and
cross-panel operations after the interface are unrestricted. -/
theorem actual_same_original_exterior_continuation {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (inside outside : Finset Copy)
    (ops future : List (ProgramStep N)) (s : Code N sample)
    (hpart : inside ∪ outside = (state s).live) (hdis : Disjoint inside outside)
    (hagenda : SeparatedAgenda N r inside outside ops s)
    (readout : SelectedView V E Copy → Obs) :
    (sourceProgram N r (ops ++ future) s).map
      (fun d => readout (selectedView (state d) (state s).live)) =
      (independentProduct
        (currentPanelProgramLaw N r ops s inside (hpart ▸ Finset.subset_union_left))
        (currentPanelProgramLaw N r ops s outside (hpart ▸ Finset.subset_union_right))).bind
          (fun v => actualOriginalContinuation N r (state s).live future s readout (joinedPanelView inside v)) := by
  rw [actual_source_program_append,PMF.map_bind,
    ← actual_joint_smaller_current_sources N r inside outside ops s
      (hpart ▸ Finset.subset_union_left) (hpart ▸ Finset.subset_union_right) hagenda,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro d hd
  have hview := actual_joined_panel_view (state d) d.property.forest inside outside
    (actual_agenda_pruned_panel_separation N r inside outside ops s hagenda
      (current_root_partition_pure (state s) s.property.forest inside outside hpart hdis) hd)
  rw [hpart] at hview
  simp only [Function.comp_apply]
  rw [← hview,actualOriginalContinuation_at_actual_view]

#print axioms actual_same_original_exterior_continuation

/-- The SAME original future process produces the exact COMPLETE original
descendant-labelled rooted UNRANKED forest after all later interactions.
Every initially carried subtree is restored; root/exterior randomness persists. -/
theorem actual_same_original_full_forest_continuation (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (inside outside : Finset Copy)
    (ops future : List (ProgramStep N)) (s : Code N sample)
    (hpart : inside ∪ outside = (state s).live) (hdis : Disjoint inside outside)
    (hagenda : SeparatedAgenda N r inside outside ops s) :
    (sourceProgram N r (ops ++ future) s).map (rootForest N) =
      (independentProduct
        (currentPanelProgramLaw N r ops s inside (hpart ▸ Finset.subset_union_left))
        (currentPanelProgramLaw N r ops s outside (hpart ▸ Finset.subset_union_right))).bind
          (fun v => actualOriginalContinuation N r (state s).live future s
            (fun w => (unrankedForest w).image (graftUnranked (state s).genealogy))
            (joinedPanelView inside v)) := by
  rw [actual_original_whole_forest_kernel_law N r (ops ++ future) s,
    originalCurrentRootKernel,PMF.map_comp]
  simpa only [Function.comp_def,sourceUnrankedForest] using
    actual_same_original_exterior_continuation N r inside outside ops future s hpart hdis hagenda
      (fun w => (unrankedForest w).image (graftUnranked (state s).genealogy))

#print axioms actual_same_original_full_forest_continuation
end G1SameOriginalExteriorContinuation
