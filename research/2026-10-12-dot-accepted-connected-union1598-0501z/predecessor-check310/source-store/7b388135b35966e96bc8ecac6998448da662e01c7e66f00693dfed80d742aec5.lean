import G1ActualJointProgram
import G1OriginalCurrentRootReconstruction

/-! Independently initialized ACTUAL current-root carriers, allowing
heterogeneous exterior populations. Contributor: dot, 2026-10-03. -/
namespace G1ActualCurrentPanelInitialization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCopyCarrierTransport
open G1OriginalCurrentRootReconstruction
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def currentPanelState (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) : State V E (SelectedCopy keep) where
  live := Finset.univ
  ancestor := id
  genealogy := Genealogy.leaf
  location := fun l => (state s).location l.val
  register := (state s).register
  history := []

lemma currentPanelState_valid (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) : Valid (currentPanelState N s keep) := by
  constructor
  · intro x; exact Finset.mem_univ _
  · intro l _; rfl
  · intro l _ x; exact Finset.mem_singleton
  · intro l _; trivial

lemma currentPanelState_source_valid (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hkeep : keep ⊆ (state s).live) :
    SourceValid N (selectedSample sample keep) (currentPanelState N s keep) := by
  refine ⟨currentPanelState_valid N s keep,?_⟩
  intro l
  have h := s.property.original_descendant l.val
  change DescendsTo N ((state s).location ((state s).ancestor l.val)) (sample l.val) at h
  have hr : (state s).ancestor l.val = l.val := s.property.forest.representative l.val (hkeep l.property)
  rw [hr] at h
  exact h

noncomputable def currentPanelCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hkeep : keep ⊆ (state s).live) :
    Code N (selectedSample sample keep) :=
  admittedCode N _ (currentPanelState N s keep) (currentPanelState_source_valid N s keep hkeep)

lemma currentPanelCode_ancestor (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hkeep : keep ⊆ (state s).live)
    (l : SelectedCopy keep) : (state (currentPanelCode N s keep hkeep)).ancestor l = l := rfl

lemma currentPanelCode_genealogy (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hkeep : keep ⊆ (state s).live)
    (l : SelectedCopy keep) : (state (currentPanelCode N s keep hkeep)).genealogy l = .leaf l := by
  exact decode_encode_live_genealogy N.root _ (currentPanelState_valid N s keep) (Finset.mem_univ _)

lemma currentPanelCode_location (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hkeep : keep ⊆ (state s).live)
    (l : SelectedCopy keep) : (state (currentPanelCode N s keep hkeep)).location l = (state s).location l.val := by
  exact decode_encode_live_population N.root _ (currentPanelState_valid N s keep) (Finset.mem_univ _)

lemma original_current_panel_prune (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hkeep : keep ⊆ s.live) {l : Copy} (hl : l ∈ keep) :
    (s.genealogy l).prune keep = some (.leaf l) := by
  apply prune_singleton_tree keep _ (hs.wellLabelled l (hkeep hl)) l
  ext x
  rw [Finset.mem_inter,hs.leaf_fiber l (hkeep hl) x,Finset.mem_singleton]
  constructor
  · rintro ⟨hanc,hx⟩
    exact (hs.representative x (hkeep hx)).symm.trans hanc
  · intro h; subst x
    exact ⟨hs.representative l (hkeep hl),hl⟩

/-- The actual larger state and the newly initialized current-root panel
share their complete original-labelled selected view, INCLUDING SAME Γ. -/
theorem actual_current_panel_initialization (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hkeep : keep ⊆ (state s).live) :
    selectedView (state s) keep =
      liftView keep (selectedView (state (currentPanelCode N s keep hkeep)) Finset.univ) := by
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · let l : SelectedCopy keep := ⟨x,hx⟩
      rw [lifted_original_genealogy keep _ l]
      change selectedGenealogy (state s) keep x = _
      have hr : (state s).ancestor x = x := s.property.forest.representative x (hkeep hx)
      have hp : ((state s).genealogy x).prune keep = some (.leaf x) :=
        original_current_panel_prune _ s.property.forest keep hkeep hx
      rw [selectedGenealogy,if_pos hx,hr,hp,currentPanelCode_ancestor,currentPanelCode_genealogy]
      rfl
    · simp [selectedView,selectedGenealogy,liftView,hx]
  · funext x
    by_cases hx : x ∈ keep
    · let l : SelectedCopy keep := ⟨x,hx⟩
      rw [lifted_original_population keep _ l]
      have hr : (state s).ancestor x = x := s.property.forest.representative x (hkeep hx)
      simp only [selectedView,selectedLocation,if_pos hx,copyLocation,hr,currentPanelCode_ancestor,currentPanelCode_location]
      rfl
    · simp [selectedView,selectedLocation,liftView,hx]
  · rfl

#print axioms actual_current_panel_initialization
end G1ActualCurrentPanelInitialization
