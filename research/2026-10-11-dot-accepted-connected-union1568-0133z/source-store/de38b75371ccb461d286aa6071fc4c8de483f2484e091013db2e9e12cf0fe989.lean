import G1OriginalCompletedForestReconstruction

/-! Recover the entire original labelled causal view from a CURRENT-root
interface, using the actual supported opaque reconstruction. No original
descendant label or population is erased. Contributor: dot, 2026-10-03. -/
namespace G1OriginalWholeCausalView
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open G1UnrankedSourceView G1UnrankedActualFuture G1UnrankedSingleExitLabel
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma prune_all (t : Genealogy Copy) : t.prune Finset.univ = some t := by
  induction t with
  | leaf x => simp [Genealogy.prune]
  | graft a b ha hb => simp [Genealogy.prune,ha,hb,Genealogy.joinPruned]

noncomputable def wholeOriginalView (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : UnrankedView V E Copy :=
  unrankedView (selectedView (state s) Finset.univ)

lemma whole_forest_eq (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :
    sourceUnrankedForest (state s) Finset.univ = rootForest N s := by
  ext q
  rw [mem_sourceUnrankedForest,rootForest,Finset.mem_image]
  constructor
  · rintro ⟨x,_,t,ht,hq⟩
    have he : (state s).genealogy ((state s).ancestor x) = t :=
      Option.some.inj ((prune_all _).symm.trans ht)
    exact ⟨(state s).ancestor x,s.property.forest.ancestor_live x,he ▸ hq⟩
  · rintro ⟨l,hl,hq⟩
    refine ⟨l,Finset.mem_univ _,(state s).genealogy l,?_,hq⟩
    have hr : (state s).ancestor l = l := s.property.forest.representative l hl
    rw [hr]
    exact prune_all _

/-- The true original live representatives supply population witnesses. The
full labelled opaque forest determines every original-copy clade, so their
current-root population readout determines every original-copy population. -/
theorem actual_original_whole_causal_view
    (N : RootedBinary V E X) {sample : Copy → X}
    (input : Copy → Genealogy Copy) (keep : Finset Copy) (s z : Code N sample)
    (hs : Reconstructs input keep (state s)) (hz : Reconstructs input keep (state z))
    (h : unrankedView (selectedView (state s) keep) =
      unrankedView (selectedView (state z) keep)) :
    wholeOriginalView N s = wholeOriginalView N z := by
  have hF : sourceUnrankedForest (state s) keep = sourceUnrankedForest (state z) keep := by
    simpa only [sourceUnrankedForest,actual_unranked_view_forest] using
      congrArg unrankedViewForest h
  have hwhole : rootForest N s = rootForest N z := by
    rw [actual_whole_forest_reconstruction N input keep s hs,
      actual_whole_forest_reconstruction N input keep z hz,hF]
  have hg : (wholeOriginalView N s).genealogy = (wholeOriginalView N z).genealogy :=
    actual_forest_determines_unranked_genealogies (state s) (state z)
      s.property.forest z.property.forest Finset.univ
      (by rw [whole_forest_eq,whole_forest_eq,hwhole])
  apply UnrankedView.ext
  · exact hg
  · funext x
    let l := (state s).ancestor x
    have hl : l ∈ (state s).live := s.property.forest.ancestor_live x
    have hlk : l ∈ keep := hs.live_subset hl
    have hleaf : l ∈ ((state s).genealogy ((state s).ancestor x)).leaves :=
      (s.property.forest.leaf_fiber l hl l).mpr (s.property.forest.representative l hl)
    have heLeaves : ((state s).genealogy ((state s).ancestor x)).leaves =
        ((state z).genealogy ((state z).ancestor x)).leaves := by
      have he := congrArg (fun f => optionTreeLeaves (f x)) hg
      simpa [wholeOriginalView,unrankedView,selectedView,selectedGenealogy,prune_all,
        optionUnranked,optionTreeLeaves,treeLeaves,toUnranked] using he
    have hzl : (state z).ancestor l = (state z).ancestor x :=
      (z.property.forest.leaf_fiber _ (z.property.forest.ancestor_live x) l).mp (heLeaves ▸ hleaf)
    have hp := congrArg (fun f => f l) (unranked_view_population _ _ h)
    have hp' : copyLocation (state s) l = copyLocation (state z) l := by
      simpa [selectedView,selectedLocation,hlk] using hp
    have hsl : (state s).ancestor l = (state s).ancestor x := s.property.forest.representative l hl
    have hx : copyLocation (state s) x = copyLocation (state z) x :=
      (merged_copies_same_population (state s) hsl).symm.trans
        (hp'.trans (merged_copies_same_population (state z) hzl))
    simpa [wholeOriginalView,unrankedView,selectedView,selectedLocation] using congrArg some hx
  · change (state s).register = (state z).register
    exact unranked_view_register _ _ h

theorem actual_supported_current_view_lifts_to_whole
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (phase : List (ProgramStep N)) (initial s z : Code N sample)
    (hs : s ∈ (sourceProgram N r phase initial).support)
    (hz : z ∈ (sourceProgram N r phase initial).support)
    (h : unrankedView (selectedView (state s) (state initial).live) =
      unrankedView (selectedView (state z) (state initial).live)) :
    wholeOriginalView N s = wholeOriginalView N z :=
  actual_original_whole_causal_view N (state initial).genealogy (state initial).live s z
    (actual_program_reconstruction_support N r phase initial hs)
    (actual_program_reconstruction_support N r phase initial hz) h

#print axioms actual_original_whole_causal_view
#print axioms actual_supported_current_view_lifts_to_whole
end G1OriginalWholeCausalView
