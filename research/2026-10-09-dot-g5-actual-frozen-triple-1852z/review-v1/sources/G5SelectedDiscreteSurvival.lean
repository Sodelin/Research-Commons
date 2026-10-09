import G5SelectedSingletonCarrier
import G5ActualNoMergerReadout

/-!
# Selected genealogy-discreteness survival from the actual full source

Contributor: dot, 2026-10-09. SOURCE DRAFT / COMPILER UNCHECKED.
This is a genealogy-only Boolean readout. Its exact probability is derived
using the actual small-copy state constructed from the selected-singleton
view, then the actual no-loss-of-roots source theorem. Original populations
and register are retained internally and never added to the observations.
-/
namespace GProgram.G5.SelectedDiscreteSurvival
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G5.OriginalProgramSurvival
open GProgram.G5.SelectedSingletonCarrier
open GProgram.G5.ActualNoMergerReadout
open scoped Classical NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def DiscreteView (keep : Finset Copy) (v : SelectedView V E Copy) : Prop :=
  ∀ x ∈ keep, ∀ y ∈ keep, y ∈ Genealogy.optionLeaves (v.genealogy x) → x = y

lemma lifted_genealogy_leaf_member (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy)
    (s : Code N (selectedSample sample keep)) (x y : SelectedCopy keep) :
    y.val ∈ Genealogy.optionLeaves
      ((liftView keep (selectedView (state s) Finset.univ)).genealogy x.val) ↔
      (state s).ancestor y = (state s).ancestor x := by
  rw [lifted_original_genealogy]
  change y.val ∈ (mapLabels Subtype.val
    ((state s).genealogy ((state s).ancestor x))).leaves ↔ _
  rw [mapLabels_leaves]
  constructor
  · intro h
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp h
    have he : z = y := Subtype.ext hzy
    subst z
    exact (s.property.forest.leaf_fiber _ (s.property.forest.ancestor_live x) y).mp hz
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨y, (s.property.forest.leaf_fiber _
      (s.property.forest.ancestor_live x) y).mpr h, rfl⟩

theorem lifted_discrete_view_iff (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy)
    (s : Code N (selectedSample sample keep)) :
    DiscreteView keep (liftView keep (selectedView (state s) Finset.univ)) ↔
      Function.Injective (state s).ancestor := by
  constructor
  · intro h x y hxy
    apply Subtype.ext
    exact h x.val x.property y.val y.property
      ((lifted_genealogy_leaf_member N keep s x y).mpr hxy.symm)
  · intro hi x hx y hy hm
    have he := (lifted_genealogy_leaf_member N keep s ⟨x,hx⟩ ⟨y,hy⟩).mp hm
    exact congrArg Subtype.val (hi he).symm

/-- Boolean genealogy readout on the exact shared view carrier. -/
noncomputable def selectedDiscreteReadout (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (v : JoinedIndex N sample keep) : Bool :=
  decide (DiscreteView keep v.val)

lemma selected_discrete_small_readout (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy)
    (s : Code N (selectedSample sample keep)) :
    selectedDiscreteReadout N keep (joinedProjection N keep (.inr s)) =
      discreteReadout N s := by
  unfold selectedDiscreteReadout discreteReadout
  congr 1
  exact propext (lifted_discrete_view_iff N keep s)

/-- Exact selected no-merger probability during an actual frozen epoch.
Extra full-source roots can merge invisibly; their no-ANY-merger event is
never substituted for this selected genealogy event. -/
theorem actual_selected_discrete_survival (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) (hs : SingletonSelected keep (selectedView (state s) keep))
    (t : ℝ≥0) :
    ((((sourceTimeKernel N r t s).map
      (fun d => joinedProjection N keep (.inl d))).map
        (selectedDiscreteReadout N keep)) true).toReal =
      Real.exp (-(totalRate N r (selectedSingletonCode N keep s) * (t : ℝ))) := by
  rw [actual_selected_singleton_epoch N r keep s hs t, PMF.map_comp]
  have hf : (selectedDiscreteReadout N keep ∘
      fun d => joinedProjection N keep (.inr d)) = discreteReadout N := by
    funext d
    exact selected_discrete_small_readout N keep d
  rw [hf]
  apply actual_discrete_survival
  rw [selected_singleton_code_ancestor]
  exact Function.injective_id

#print axioms lifted_genealogy_leaf_member
#print axioms lifted_discrete_view_iff
#print axioms selected_discrete_small_readout
#print axioms actual_selected_discrete_survival
end GProgram.G5.SelectedDiscreteSurvival

