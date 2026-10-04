import G1ActualRootBlobPopulationFootprint

/-! The actual COMPLETE original root-blob/ancestral causal view factors
through base. Full original descendant trees are restored; no old labels or
register information are dropped. Unreleased FINAL K outputs are not joined
into this current observer before their physical close/promotion. -/
namespace G1ActualRootBlobBaseObserver
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1OriginalWholeCausalView G1JointUnrankedForestAssembly
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler
open G1CanonicalFiniteActiveEpochAdmission G1NaturalActiveActorFrontier G1CanonicalWholeOriginalActiveEpoch
open G1ActualRootBlobPopulationFootprint
open scoped Classical
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Source validity derives that any tree currently in the root blob has
ALL its original labelled leaves in base. No assumed tree equality or panel
purity field is needed to exclude prematurely exposed private descendants. -/
theorem actual_root_blob_whole_view_is_base (N : RootedBinary V E X) (s : State V E Copy)
    (hs : Valid s) (privateCopies : Finset Copy)
    (hoff : ∀ x ∈ privateCopies, ¬ OriginalRootBlobPopulation N (copyLocation s x)) :
    originalRootBlobView N (unrankedView (selectedView s Finset.univ)) =
      originalRootBlobView N (unrankedView (selectedView s (Finset.univ \ privateCopies))) := by
  apply UnrankedView.ext
  · funext x
    by_cases hroot : OriginalRootBlobPopulation N (copyLocation s x)
    · have hn : x ∉ privateCopies := fun hx => hoff x hx hroot
      have hx : x ∈ Finset.univ \ privateCopies := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩
      have hsubset : (s.genealogy (s.ancestor x)).leaves ⊆ Finset.univ \ privateCopies := by
        intro y hy
        have hanc : s.ancestor y = s.ancestor x := (hs.leaf_fiber _ (hs.ancestor_live x) y).mp hy
        have hpop := merged_copies_same_population s hanc
        have hyroot : OriginalRootBlobPopulation N (copyLocation s y) := hpop.symm ▸ hroot
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hm => hoff y hm hyroot⟩
      have hprune : (s.genealogy (s.ancestor x)).prune (Finset.univ \ privateCopies) =
          some (s.genealogy (s.ancestor x)) :=
        (prune_eq_of_leaf_membership _ _ Finset.univ (fun y hy =>
          ⟨fun _ => Finset.mem_univ _,fun _ => hsubset hy⟩)).trans (prune_all _)
      simp only [originalRootBlobView,unrankedView,selectedView,selectedLocation,Finset.mem_univ,if_true,
        if_pos hx,observedRootPopulation,hroot,selectedGenealogy,optionUnranked,prune_all,hprune]
    · by_cases hx : x ∈ privateCopies
      · simp [originalRootBlobView,unrankedView,selectedView,selectedLocation,hx,observedRootPopulation,hroot]
      · simp [originalRootBlobView,unrankedView,selectedView,selectedLocation,hx,observedRootPopulation,hroot]
  · funext x
    by_cases hroot : OriginalRootBlobPopulation N (copyLocation s x)
    · have hx : x ∉ privateCopies := fun hm => hoff x hm hroot
      simp [originalRootBlobView,unrankedView,selectedView,selectedLocation,hx,observedRootPopulation,hroot]
    · by_cases hx : x ∈ privateCopies <;>
        simp [originalRootBlobView,unrankedView,selectedView,selectedLocation,hx,observedRootPopulation,hroot]
  · rfl

universe u v w
variable {Y : Type w} [Fintype Y]

/-- Complete CURRENT original root-blob history is read only from the real
original base coordinate while all private actors remain physically inside
their spans. Released actors must first be promoted into base. -/
theorem actual_original_root_blob_view_from_active_base (O : Source.{u,v,w} Y)
    (H : OriginalParentRegistry O.network) {T : Source Y} (D : Decoration O T) (hD : Originated O H D)
    (actors : List (BridgeActor T)) {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → Y}
    (s : Code O.network sample)
    (hregion : ∀ actor ∈ actors, ∀ x ∈ G1ActiveCoreBridgeCohorts.originalInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    originalRootBlobView O.network (wholeOriginalView O.network s) =
      originalRootBlobView O.network (unrankedView (selectedView (state s) (activeOriginalBase O D sample actors))) := by
  apply actual_root_blob_whole_view_is_base O.network (state s) s.property.forest
    (G1ActualFinitePanelProgramTensor.panelUnion (activeOriginalPanels O D sample actors))
  intro x hx
  obtain ⟨keep,hkeep,hx⟩ := (actual_panel_union_member _ x).mp hx
  obtain ⟨actor,ha,rfl⟩ := List.mem_map.mp hkeep
  exact actual_private_span_outside_original_root_blob O H D hD actor _ (hregion actor ha x hx)

#print axioms actual_root_blob_whole_view_is_base
#print axioms actual_original_root_blob_view_from_active_base
end G1ActualRootBlobBaseObserver
