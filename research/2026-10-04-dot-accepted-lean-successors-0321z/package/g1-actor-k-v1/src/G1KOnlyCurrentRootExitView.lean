import G1CanonicalOriginatedHistoryPlanner

/-! A K-only CURRENT-root actor interface at one actual original exit.
Every root's unranked subtree is reconstructed from the complete labelled
forest; hidden survivor IDs and child orientations are absent from the view. -/
namespace G1KOnlyCurrentRootExitView
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceForestSilentPruning
open G1UnrankedSourceView G1UnrankedSingleExitLabel
open scoped Classical
variable {V E Copy : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy]

noncomputable def rootTreeAt (forest : Finset (UnrankedTree Copy)) (x : Copy) : Option (UnrankedTree Copy) :=
  if h : ∃ tree ∈ forest, x ∈ treeLeaves tree then some (Classical.choose h) else none

noncomputable def currentRootExitView (inside : Finset Copy) (exit : Location V E)
    (register : V → Bool) (forest : Finset (UnrankedTree Copy)) : UnrankedView V E Copy where
  genealogy x := if x ∈ inside then rootTreeAt forest x else none
  population x := if x ∈ inside then some exit else none
  register := register

/-- Source validity supplies every root fibre. No forest validity or desired
output-view equality is an assumed field of the reconstructed K label. -/
theorem actual_current_root_exit_view (d : State V E Copy) (hd : Valid d) (inside : Finset Copy)
    (exit : Location V E) (register : V → Bool)
    (single : ∀ x ∈ inside, copyLocation d x = exit) (sameRegister : d.register = register) :
    currentRootExitView inside exit register (sourceUnrankedForest d inside) =
      unrankedView (selectedView d inside) := by
  apply UnrankedView.ext
  · funext x
    by_cases hx : x ∈ inside
    · have hw : ∃ tree ∈ sourceUnrankedForest d inside, x ∈ treeLeaves tree :=
        (source_unranked_forest_covers d hd inside x).mpr hx
      change (if x ∈ inside then rootTreeAt (sourceUnrankedForest d inside) x else none) =
        optionUnranked ((selectedView d inside).genealogy x)
      rw [if_pos hx,rootTreeAt,dif_pos hw]
      exact (actual_unranked_subtree_from_forest d hd inside x hx (Classical.choose hw)
        (Classical.choose_spec hw).1 (Classical.choose_spec hw).2).symm
    · simp [currentRootExitView,unrankedView,selectedView,selectedGenealogy,optionUnranked,hx]
  · funext x
    by_cases hx : x ∈ inside
    · simp [currentRootExitView,unrankedView,selectedView,selectedLocation,hx,single x hx]
    · simp [currentRootExitView,unrankedView,selectedView,selectedLocation,hx]
  · exact sameRegister.symm

#print axioms actual_current_root_exit_view
end G1KOnlyCurrentRootExitView
