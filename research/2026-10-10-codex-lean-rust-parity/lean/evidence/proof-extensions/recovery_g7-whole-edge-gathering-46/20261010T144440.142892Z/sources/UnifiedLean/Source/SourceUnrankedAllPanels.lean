import UnifiedLean.Source.SourceUnrankedCopyProjectivity

/-!
# Actual same-source rooted unranked law for EVERY selected copy panel

Contributor: dot, 2026-10-02. Adds the genuine empty-panel identity to the
already proved nonempty cross-carrier source/completion theorem. This keeps
the inherited all-selected-subsets quantifier without a nonempty loophole.
-/
namespace UnifiedLean.Source.SourceUnrankedAllPanels
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceUnrankedCopyProjectivity
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma original_empty_panel_forest (s : State V E Copy) :
    sourceUnrankedForest s ∅ = ∅ := by
  ext q
  simp [mem_sourceUnrankedForest]

lemma no_copy_unranked_forest [IsEmpty Copy] (s : State V E Copy) :
    sourceUnrankedForest s Finset.univ = ∅ := by
  simp [sourceUnrankedForest,unrankedForest]

/-- Entire actual same-original-source complete unranked projectivity, for
EVERY original selected panel, including the empty genealogy law. The smaller
source is independently initialized on exactly those original copy IDs. -/
theorem actual_complete_unranked_all_panel_projectivity (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (naturalCompletedLaw N C sample H p common r).map
      (fun s => sourceUnrankedForest (state s) keep) =
      (naturalCompletedUnrankedLaw N C (selectedSample sample keep) H p common r).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
  by_cases hk : keep.Nonempty
  · exact actual_complete_unranked_copy_projectivity N C sample keep hk H p common r
  · have he : keep = ∅ := Finset.not_nonempty_iff_eq_empty.mp hk
    subst keep
    letI : IsEmpty (SelectedCopy (∅ : Finset Copy)) := ⟨fun x => Finset.notMem_empty _ x.property⟩
    rw [naturalCompletedUnrankedLaw,PMF.map_comp]
    simp only [Function.comp_def,original_empty_panel_forest,no_copy_unranked_forest,Finset.image_empty]
    exact (PMF.map_const _ _).trans (PMF.map_const _ _).symm

#print axioms actual_complete_unranked_all_panel_projectivity
end UnifiedLean.Source.SourceUnrankedAllPanels
