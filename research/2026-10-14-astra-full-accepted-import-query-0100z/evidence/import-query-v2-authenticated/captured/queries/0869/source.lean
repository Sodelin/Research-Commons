import G1OriginalActorPrivateWordKernel

/-! Actual open/close data operations on the ORIGINAL unranked carrier.
Opening prunes the retained base into one descendant actor plus the remaining
base; closing joins that actual full actor view back. Both derive their
whole causal reconstruction from actual source-valid pure fibres. -/
namespace G1OriginalUnrankedActorOpenClose
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UnrankedGenealogyObservation UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UniformizedSourceStep
open G1UnrankedSourceView G1NestedOriginalSourceProjection G1JointUnrankedForestAssembly
open G1UnrankedSingleExitLabel G1SameOriginalExteriorContinuation
open scoped Classical
variable {V E Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def restrictOriginalView (keep : Finset Copy) (view : UnrankedView V E Copy) : UnrankedView V E Copy where
  genealogy x := if x ∈ keep then (view.genealogy x).bind (pruneTree keep) else none
  population x := if x ∈ keep then view.population x else none
  register := view.register

lemma actual_option_unranked_prune (keep : Finset Copy) (a : Option (Genealogy Copy)) :
    (optionUnranked a).bind (pruneTree keep) = optionUnranked (a.bind (fun t => t.prune keep)) := by
  cases a with
  | none => rfl
  | some a => exact prune_toUnranked keep a

lemma actual_restrict_original_unranked (keep : Finset Copy) (view : SelectedView V E Copy) :
    restrictOriginalView keep (unrankedView view) = unrankedView (restrictSelected keep view) := by
  apply UnrankedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · simp only [restrictOriginalView,restrictSelected,unrankedView,if_pos hx]
      exact actual_option_unranked_prune keep _
    · simp [restrictOriginalView,restrictSelected,unrankedView,hx,optionUnranked]
  · funext x; simp only [restrictOriginalView,restrictSelected,unrankedView]
  · rfl

/-- The actual actor input is obtained from the original unranked base alone,
with every original opaque subtree, population and SAME register retained. -/
theorem actual_original_unranked_subpanel (s : State V E Copy) (small large : Finset Copy) (h : small ⊆ large) :
    restrictOriginalView small (unrankedView (selectedView s large)) = unrankedView (selectedView s small) := by
  rw [actual_restrict_original_unranked,actual_nested_selected_view s small large h]

noncomputable def openOriginalActor (inside base : Finset Copy) (view : UnrankedView V E Copy) :=
  (restrictOriginalView (base \ inside) view,restrictOriginalView inside view)

noncomputable def closeOriginalActor (inside : Finset Copy) (base actor : UnrankedView V E Copy) :=
  unrankedJoinedPanelView inside (actor,base)

lemma actual_original_open_coordinates (s : State V E Copy) (inside base : Finset Copy) (hi : inside ⊆ base) :
    openOriginalActor inside base (unrankedView (selectedView s base)) =
      (unrankedView (selectedView s (base \ inside)),unrankedView (selectedView s inside)) := by
  simp only [openOriginalActor,actual_original_unranked_subpanel s _ base Finset.sdiff_subset,
    actual_original_unranked_subpanel s inside base hi]

lemma actual_split_base_cover (inside base : Finset Copy) (hi : inside ⊆ base) :
    inside ∪ (base \ inside) = base := by
  ext x
  by_cases hx : x ∈ inside
  · simp only [Finset.mem_union,Finset.mem_sdiff,hx,true_or,iff_true]
    exact ⟨fun _ => hi hx,fun _ => trivial⟩
  · simp [hx]

/-- Opening changes no actual full original causal base view. Source-valid
pure fibres derive this exact quotient equality; no desired output field. -/
theorem actual_original_open_close_identity (s : State V E Copy) (hs : Valid s)
    (inside base : Finset Copy) (hi : inside ⊆ base)
    (hp : PrunedPanelSeparated s inside (base \ inside)) :
    let split := openOriginalActor inside base (unrankedView (selectedView s base))
    closeOriginalActor inside split.1 split.2 = unrankedView (selectedView s base) := by
  rw [actual_original_open_coordinates s inside base hi]
  dsimp only [closeOriginalActor]
  have h := actual_joined_panel_view s hs inside (base \ inside) hp
  rw [actual_split_base_cover inside base hi] at h
  exact (actual_unranked_joined_panel inside (selectedView s inside,selectedView s (base \ inside))).symm.trans
    (congrArg unrankedView h.symm)

/-- Closing is exact original causal coarsening after the literal cut, even
when delivered roots share a retained-base population. Only forest purity
is needed; no post-close population separation restriction is added. -/
theorem actual_original_actor_close (s : State V E Copy) (hs : Valid s) (inside outside : Finset Copy)
    (hp : PrunedPanelSeparated s inside outside) :
    closeOriginalActor inside (unrankedView (selectedView s outside)) (unrankedView (selectedView s inside)) =
      unrankedView (selectedView s (inside ∪ outside)) := by
  exact (actual_unranked_joined_panel inside (selectedView s inside,selectedView s outside)).symm.trans
    (congrArg unrankedView (actual_joined_panel_view s hs inside outside hp).symm)

#print axioms actual_original_open_close_identity
#print axioms actual_original_actor_close
end G1OriginalUnrankedActorOpenClose
