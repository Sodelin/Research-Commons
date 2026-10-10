import G1ActualJointStageHistory

/-!
# Whole unranked genealogy/population/SAME-register source interface

Contributor: dot, 2026-10-03. The exact inherited child-swap quotient is
applied to EVERY labelled current subtree. Population and register data stay
original. This is the interface needed to admit the unranked G1 label alone.
-/
namespace G1UnrankedSourceView
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical BigOperators
variable {V E Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

@[ext] structure UnrankedView (V E Copy : Type*) where
  genealogy : Copy → Option (UnrankedTree Copy)
  population : Copy → Option (Location V E)
  register : V → Bool

def unrankedView (v : SelectedView V E Copy) : UnrankedView V E Copy :=
  ⟨fun x => optionUnranked (v.genealogy x),v.population,v.register⟩

lemma optionEquiv_of_unranked_eq {a b : Option (Genealogy Copy)}
    (h : optionUnranked a = optionUnranked b) : OptionEquiv a b := by
  cases a with
  | none => cases b <;> first | trivial | cases h
  | some a =>
      cases b with
      | none => cases h
      | some b => exact (toUnranked_eq_iff a b).mp (Option.some.inj h)

lemma unranked_view_genealogy (v w : SelectedView V E Copy) (h : unrankedView v = unrankedView w) (x : Copy) :
    optionUnranked (v.genealogy x) = optionUnranked (w.genealogy x) :=
  congrArg (fun q : UnrankedView V E Copy => q.genealogy x) h

lemma unranked_view_population (v w : SelectedView V E Copy) (h : unrankedView v = unrankedView w) :
    v.population = w.population := congrArg UnrankedView.population h

lemma unranked_view_register (v w : SelectedView V E Copy) (h : unrankedView v = unrankedView w) :
    v.register = w.register := congrArg UnrankedView.register h

lemma unranked_view_block_leaves (v w : SelectedView V E Copy) (h : unrankedView v = unrankedView w) (x : Copy) :
    Genealogy.optionLeaves (v.genealogy x) = Genealogy.optionLeaves (w.genealogy x) := by
  have he := congrArg optionTreeLeaves (unranked_view_genealogy v w h x)
  simpa only [optionUnranked_leaves] using he

theorem actual_unranked_population_blocks (v w : SelectedView V E Copy)
    (h : unrankedView v = unrankedView w) (keep : Finset Copy) (place : Location V E) :
    viewPopulationBlocks v keep place = viewPopulationBlocks w keep place := by
  unfold viewPopulationBlocks
  rw [unranked_view_population v w h]
  congr 1
  funext x
  exact unranked_view_block_leaves v w h x

lemma unranked_block_tree (v w : SelectedView V E Copy) (h : unrankedView v = unrankedView w)
    (A : Finset Copy) : OptionEquiv (viewBlockTree v A) (viewBlockTree w A) := by
  unfold viewBlockTree
  split_ifs with ha
  · exact optionEquiv_of_unranked_eq (unranked_view_genealogy v w h (Classical.choose ha))
  · trivial

/-- The ORIGINAL selected subtree graft descends to the exact child-swap
quotient; no associativity, label erasure or count-only readout is introduced. -/
theorem actual_unranked_projected_merger (v w : SelectedView V E Copy)
    (h : unrankedView v = unrankedView w) (A B : Finset Copy) :
    unrankedView (projectedMerge v A B) = unrankedView (projectedMerge w A B) := by
  apply UnrankedView.ext
  · funext x
    by_cases hx : x ∈ A ∪ B
    · change optionUnranked (if x ∈ A ∪ B then _ else _) = optionUnranked (if x ∈ A ∪ B then _ else _)
      rw [if_pos hx,if_pos hx]
      exact optionUnranked_eq (joinPruned_respects (unranked_block_tree v w h A) (unranked_block_tree v w h B))
    · simpa only [unrankedView,projectedMerge,if_neg hx] using unranked_view_genealogy v w h x
  · exact unranked_view_population v w h
  · exact unranked_view_register v w h

#print axioms actual_unranked_population_blocks
#print axioms actual_unranked_projected_merger
end G1UnrankedSourceView
