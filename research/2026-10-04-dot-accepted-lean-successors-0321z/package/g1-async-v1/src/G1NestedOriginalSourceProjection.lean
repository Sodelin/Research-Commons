import G1CrossingActorKernelFusion

/-! Actual nested labelled selected views, retaining original populations and
SAME register. Needed to derive concurrent three-panel tensor laws without a
supplied factorization hypothesis. -/
namespace G1NestedOriginalSourceProjection
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.UniformizedSourceStep
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma join_pruned_bind_prune (keep : Finset Copy) (a b : Option (Genealogy Copy)) :
    (Genealogy.joinPruned a b).bind (fun t => t.prune keep) =
      Genealogy.joinPruned (a.bind (fun t => t.prune keep)) (b.bind (fun t => t.prune keep)) := by
  cases a <;> cases b <;> simp [Genealogy.joinPruned,Genealogy.prune]
  split <;> simp_all

lemma actual_genealogy_nested_prune (small large : Finset Copy) (h : small ⊆ large) (t : Genealogy Copy) :
    (t.prune large).bind (fun tree => tree.prune small) = t.prune small := by
  induction t with
  | leaf x =>
      by_cases hx : x ∈ small
      · simp [Genealogy.prune,hx,h hx]
      · by_cases hl : x ∈ large <;> simp [Genealogy.prune,hx,hl]
  | graft a b iha ihb =>
      rw [Genealogy.prune,join_pruned_bind_prune,iha,ihb]
      rfl

noncomputable def restrictSelected (keep : Finset Copy) (v : SelectedView V E Copy) : SelectedView V E Copy where
  genealogy x := if x ∈ keep then (v.genealogy x).bind (fun t => t.prune keep) else none
  population x := if x ∈ keep then v.population x else none
  register := v.register

lemma actual_nested_selected_view (s : State V E Copy) (small large : Finset Copy) (h : small ⊆ large) :
    restrictSelected small (selectedView s large) = selectedView s small := by
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ small
    · simp only [restrictSelected,selectedView,selectedGenealogy,if_pos hx,if_pos (h hx)]
      exact actual_genealogy_nested_prune small large h _
    · simp [restrictSelected,selectedView,selectedGenealogy,hx]
  · funext x
    by_cases hx : x ∈ small
    · simp [restrictSelected,selectedView,selectedLocation,hx,h hx]
    · simp [restrictSelected,selectedView,selectedLocation,hx]
  · rfl

lemma actual_smaller_view_from_larger (s z : State V E Copy) (small large : Finset Copy)
    (h : small ⊆ large) (heq : selectedView s large = selectedView z large) :
    selectedView s small = selectedView z small := by
  rw [←actual_nested_selected_view s small large h,←actual_nested_selected_view z small large h,heq]

noncomputable def subIndex (N : RootedBinary V E X) {sample : Copy → X}
    (small large : Finset Copy) (_h : small ⊆ large) (v : SelectedIndex N sample large) :
    SelectedIndex N sample small := projection N small (representative N large v)

/-- The canonical restriction is independent of the representative hidden by
the actual larger selected source carrier. -/
theorem actual_subindex_projection (N : RootedBinary V E X) {sample : Copy → X}
    (small large : Finset Copy) (h : small ⊆ large) (s : Code N sample) :
    subIndex N small large h (projection N large s) = projection N small s := by
  apply Subtype.ext
  exact actual_smaller_view_from_larger _ _ small large h (representative_view N large _)

#print axioms actual_subindex_projection
end G1NestedOriginalSourceProjection
