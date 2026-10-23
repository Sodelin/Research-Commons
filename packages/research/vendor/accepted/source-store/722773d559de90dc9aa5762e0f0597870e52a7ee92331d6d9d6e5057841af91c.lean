import G1ActualFinitePanelProgramTensor

/-! Finite complete ORIGINAL descendant-cohort unranked coordinates, with
an actual base complement. Their union reconstructs every original tree,
population and SAME register under actual pure fibres and full copy cover. -/
namespace G1FiniteOriginalCausalCoordinates
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1JointUnrankedForestAssembly G1SameOriginalExteriorContinuation
open G1UnrankedSingleExitLabel G1OriginalWholeCausalView G1ActualFinitePanelProgramTensor
open scoped Classical
universe u v w z
variable {V : Type u} {E : Type v} {X : Type w} {Copy : Type z}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

abbrev OriginalPanelViews (V : Type u) (E : Type v) (Copy : Type z) : List (Finset Copy) → Type (max u v z)
  | [] => PUnit
  | _::keeps => UnrankedView V E Copy × OriginalPanelViews V E Copy keeps

noncomputable def originalPanelViews (s : State V E Copy) :
    (keeps : List (Finset Copy)) → OriginalPanelViews V E Copy keeps
  | [] => PUnit.unit
  | keep::keeps => (unrankedView (selectedView s keep),originalPanelViews s keeps)

noncomputable def quotientPanelCoordinates (N : RootedBinary V E X) {sample : Copy → X} :
    (keeps : List (Finset Copy)) → PanelIndex.{u,v,w,z,0} N sample keeps → OriginalPanelViews V E Copy keeps
  | [],_ => PUnit.unit
  | _::keeps,v => (unrankedView v.1.val,quotientPanelCoordinates N keeps v.2)

theorem actual_quotient_panel_projection (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keeps : List (Finset Copy)) :
    quotientPanelCoordinates N keeps (panelProjection.{u,v,w,z,0} N keeps s) = originalPanelViews (state s) keeps := by
  induction keeps with
  | nil => rfl
  | cons keep keeps ih => simp only [quotientPanelCoordinates,panelProjection,originalPanelViews,projection,ih]

noncomputable def joinOriginalPanelViews (register : V → Bool) :
    (keeps : List (Finset Copy)) → OriginalPanelViews V E Copy keeps → UnrankedView V E Copy
  | [],_ => ⟨fun _ => none,fun _ => none,register⟩
  | keep::keeps,v => unrankedJoinedPanelView keep (v.1,joinOriginalPanelViews register keeps v.2)

noncomputable def PureOriginalPanels (s : State V E Copy) : List (Finset Copy) → Prop
  | [] => True
  | keep::keeps => PrunedPanelSeparated s keep (panelUnion keeps) ∧ PureOriginalPanels s keeps

theorem actual_finite_original_panel_view_reconstruction (s : State V E Copy) (hs : Valid s)
    (keeps : List (Finset Copy)) (hp : PureOriginalPanels s keeps) :
    joinOriginalPanelViews s.register keeps (originalPanelViews s keeps) =
      unrankedView (selectedView s (panelUnion keeps)) := by
  induction keeps with
  | nil =>
    apply UnrankedView.ext
    · funext x; simp [joinOriginalPanelViews,panelUnion,unrankedView,selectedView,selectedGenealogy,optionUnranked]
    · funext x; simp [joinOriginalPanelViews,originalPanelViews,panelUnion,unrankedView,selectedView,selectedLocation]
    · rfl
  | cons keep keeps ih =>
    simp only [joinOriginalPanelViews,originalPanelViews,panelUnion]
    rw [ih hp.2]
    exact (actual_unranked_joined_panel keep (selectedView s keep,selectedView s (panelUnion keeps))).symm.trans
      (congrArg unrankedView (actual_joined_panel_view s hs keep (panelUnion keeps) hp.1).symm)

/-- Complete ORIGINAL source-state reconstruction, with no original label,
clade, population or exposed register dropped at the active actor interface. -/
theorem actual_finite_original_whole_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keeps : List (Finset Copy)) (cover : panelUnion keeps = Finset.univ)
    (hp : PureOriginalPanels (state s) keeps) :
    joinOriginalPanelViews (state s).register keeps (quotientPanelCoordinates N keeps (panelProjection.{u,v,w,z,0} N keeps s)) =
      wholeOriginalView N s := by
  rw [actual_quotient_panel_projection,actual_finite_original_panel_view_reconstruction (state s) s.property.forest keeps hp,cover]
  rfl

noncomputable def activeOriginalPanelFamily (actors : List (Finset Copy)) : List (Finset Copy) :=
  actors ++ [Finset.univ \ panelUnion actors]

lemma panel_union_append (actors base : List (Finset Copy)) :
    panelUnion (actors ++ base) = panelUnion actors ∪ panelUnion base := by
  induction actors with
  | nil => simp [panelUnion]
  | cons keep actors ih => simp only [List.cons_append,panelUnion,ih,Finset.union_assoc]

/-- The original base complement is CONSTRUCTED from all original actor
cohorts, so full original copy coverage is not a supplied output identity. -/
theorem actual_active_original_panel_cover (actors : List (Finset Copy)) :
    panelUnion (activeOriginalPanelFamily actors) = Finset.univ := by
  rw [activeOriginalPanelFamily,panel_union_append]
  simp only [panelUnion,Finset.union_empty]
  ext x
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and,iff_true]
  exact em _

#print axioms actual_finite_original_whole_view
#print axioms actual_active_original_panel_cover
end G1FiniteOriginalCausalCoordinates
