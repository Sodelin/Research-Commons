import G7FiniteForestReassembly
import G7EffectivePopulationCoefficients

/-!
# Constructive admitted range for disjoint original-copy panel products

Contributor: Codex / lean_reuse_successor, 2026-10-10.
New proof derivative; original providers are unchanged. This glues two actually
source-valid smaller-copy states on a panel and its complement, retaining the
original graph, sample assignments, ordered genealogy labels and populations.
The inherited joinViews uses the left register; the constructed state does so
as well. Same entering registers remain a separate epoch-law premise.

Historical/current provider search found exact mapLabels, selected-view
encode/decode and deterministic reassembly providers, but no constructive
joined-state range theorem. This source is a draft until separately checked.
-/

namespace GProgram.G7.ConstructivePanelJoin
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.WholeAncestorPanelCode
open GProgram.G7.PopulationForestReassembly
open GProgram.G7.FiniteForestReassembly
open GProgram.G7.EffectivePopulationCoefficients
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma complement_mem (keep : Finset Copy) (x : Copy) (hx : x ∉ keep) :
    x ∈ Finset.univ \ keep := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩

lemma complement_not_mem (keep : Finset Copy)
    (x : SelectedCopy (Finset.univ \ keep)) : x.val ∉ keep :=
  (Finset.mem_sdiff.mp x.property).2

/-- A concrete full state, with no search over the full snapshot universe. -/
noncomputable def joinedState (keep : Finset Copy)
    (a : State V E (SelectedCopy keep))
    (b : State V E (SelectedCopy (Finset.univ \ keep))) : State V E Copy where
  live := Finset.univ.filter (fun x => if hx : x ∈ keep then
    (⟨x,hx⟩ : SelectedCopy keep) ∈ a.live else
    (⟨x,complement_mem keep x hx⟩ : SelectedCopy (Finset.univ \ keep)) ∈ b.live)
  ancestor x := if hx : x ∈ keep then (a.ancestor ⟨x,hx⟩).val
    else (b.ancestor ⟨x,complement_mem keep x hx⟩).val
  genealogy x := if hx : x ∈ keep then mapLabels Subtype.val (a.genealogy ⟨x,hx⟩)
    else mapLabels Subtype.val (b.genealogy ⟨x,complement_mem keep x hx⟩)
  location x := if hx : x ∈ keep then a.location ⟨x,hx⟩
    else b.location ⟨x,complement_mem keep x hx⟩
  register := a.register
  history := []

variable (keep : Finset Copy)
variable (a : State V E (SelectedCopy keep))
variable (b : State V E (SelectedCopy (Finset.univ \ keep)))

lemma joined_live_left (x : SelectedCopy keep) :
    x.val ∈ (joinedState keep a b).live ↔ x ∈ a.live := by
  simp only [joinedState, Finset.mem_filter, Finset.mem_univ, true_and,
    dif_pos x.property]

lemma joined_live_right (x : SelectedCopy (Finset.univ \ keep)) :
    x.val ∈ (joinedState keep a b).live ↔ x ∈ b.live := by
  simp only [joinedState, Finset.mem_filter, Finset.mem_univ, true_and,
    dif_neg (complement_not_mem keep x)]

lemma joined_ancestor_left (x : SelectedCopy keep) :
    (joinedState keep a b).ancestor x.val = (a.ancestor x).val := by
  simp only [joinedState, dif_pos x.property]

lemma joined_ancestor_right (x : SelectedCopy (Finset.univ \ keep)) :
    (joinedState keep a b).ancestor x.val = (b.ancestor x).val := by
  simp only [joinedState, dif_neg (complement_not_mem keep x)]

lemma joined_genealogy_left (x : SelectedCopy keep) :
    (joinedState keep a b).genealogy x.val = mapLabels Subtype.val (a.genealogy x) := by
  simp only [joinedState, dif_pos x.property]

lemma joined_genealogy_right (x : SelectedCopy (Finset.univ \ keep)) :
    (joinedState keep a b).genealogy x.val = mapLabels Subtype.val (b.genealogy x) := by
  simp only [joinedState, dif_neg (complement_not_mem keep x)]

lemma joined_location_left (x : SelectedCopy keep) :
    (joinedState keep a b).location x.val = a.location x := by
  simp only [joinedState, dif_pos x.property]

lemma joined_location_right (x : SelectedCopy (Finset.univ \ keep)) :
    (joinedState keep a b).location x.val = b.location x := by
  simp only [joinedState, dif_neg (complement_not_mem keep x)]

lemma joined_copyLocation_left (x : SelectedCopy keep) :
    copyLocation (joinedState keep a b) x.val = copyLocation a x := by
  unfold copyLocation
  rw [joined_ancestor_left, joined_location_left]

lemma joined_copyLocation_right (x : SelectedCopy (Finset.univ \ keep)) :
    copyLocation (joinedState keep a b) x.val = copyLocation b x := by
  unfold copyLocation
  rw [joined_ancestor_right, joined_location_right]

lemma joined_closed : AncestorClosed (joinedState keep a b) keep := by
  intro x
  by_cases hx : x ∈ keep
  · rw [joined_ancestor_left keep a b ⟨x,hx⟩]
    exact ⟨fun _ => (a.ancestor ⟨x,hx⟩).property, fun _ => hx⟩
  · rw [joined_ancestor_right keep a b ⟨x,complement_mem keep x hx⟩]
    exact ⟨fun h => False.elim (hx h), fun h =>
      False.elim (complement_not_mem keep (b.ancestor ⟨x,complement_mem keep x hx⟩) h)⟩

lemma mapLabels_subtype_mem (panel : Finset Copy)
    (g : Genealogy (SelectedCopy panel)) (x : Copy) :
    x ∈ (mapLabels Subtype.val g).leaves ↔
      ∃ hx : x ∈ panel, (⟨x,hx⟩ : SelectedCopy panel) ∈ g.leaves := by
  rw [mapLabels_leaves]
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    subst x
    exact ⟨y.property,hy⟩
  · rintro ⟨hx,h⟩
    exact Finset.mem_image.mpr ⟨⟨x,hx⟩,h,rfl⟩

theorem joinedState_valid (ha : Valid a) (hb : Valid b) :
    Valid (joinedState keep a b) := by
  constructor
  · intro x
    by_cases hx : x ∈ keep
    · rw [joined_ancestor_left keep a b ⟨x,hx⟩]
      exact (joined_live_left keep a b (a.ancestor ⟨x,hx⟩)).mpr
        (ha.ancestor_live ⟨x,hx⟩)
    · rw [joined_ancestor_right keep a b ⟨x,complement_mem keep x hx⟩]
      exact (joined_live_right keep a b (b.ancestor ⟨x,complement_mem keep x hx⟩)).mpr
        (hb.ancestor_live ⟨x,complement_mem keep x hx⟩)
  · intro l hl
    by_cases hkeep : l ∈ keep
    · rw [joined_ancestor_left keep a b ⟨l,hkeep⟩]
      exact congrArg Subtype.val (ha.representative ⟨l,hkeep⟩
        ((joined_live_left keep a b ⟨l,hkeep⟩).mp hl))
    · rw [joined_ancestor_right keep a b ⟨l,complement_mem keep l hkeep⟩]
      exact congrArg Subtype.val (hb.representative ⟨l,complement_mem keep l hkeep⟩
        ((joined_live_right keep a b ⟨l,complement_mem keep l hkeep⟩).mp hl))
  · intro l hl x
    by_cases hkeep : l ∈ keep
    · have hll : (⟨l,hkeep⟩ : SelectedCopy keep) ∈ a.live :=
        (joined_live_left keep a b ⟨l,hkeep⟩).mp hl
      rw [joined_genealogy_left keep a b ⟨l,hkeep⟩, mapLabels_subtype_mem]
      constructor
      · rintro ⟨hx,hleaf⟩
        rw [joined_ancestor_left keep a b ⟨x,hx⟩]
        exact congrArg Subtype.val ((ha.leaf_fiber ⟨l,hkeep⟩ hll ⟨x,hx⟩).mp hleaf)
      · intro h
        have hx : x ∈ keep := (joined_closed keep a b x).mpr (by rw [h]; exact hkeep)
        refine ⟨hx,(ha.leaf_fiber ⟨l,hkeep⟩ hll ⟨x,hx⟩).mpr ?_⟩
        apply Subtype.ext
        rwa [joined_ancestor_left keep a b ⟨x,hx⟩] at h
    · let ll : SelectedCopy (Finset.univ \ keep) := ⟨l,complement_mem keep l hkeep⟩
      have hll : ll ∈ b.live := (joined_live_right keep a b ll).mp hl
      rw [joined_genealogy_right keep a b ll, mapLabels_subtype_mem]
      constructor
      · rintro ⟨hx,hleaf⟩
        rw [joined_ancestor_right keep a b ⟨x,hx⟩]
        exact congrArg Subtype.val ((hb.leaf_fiber ll hll ⟨x,hx⟩).mp hleaf)
      · intro h
        have hx : x ∈ Finset.univ \ keep :=
          (closed_complement (joinedState keep a b) keep (joined_closed keep a b) x).mpr
            (by rw [h]; exact ll.property)
        refine ⟨hx,(hb.leaf_fiber ll hll ⟨x,hx⟩).mpr ?_⟩
        apply Subtype.ext
        rwa [joined_ancestor_right keep a b ⟨x,hx⟩] at h
  · intro l hl
    by_cases hkeep : l ∈ keep
    · rw [joined_genealogy_left keep a b ⟨l,hkeep⟩]
      exact mapLabels_wellLabelled Subtype.val Subtype.val_injective _
        (ha.wellLabelled ⟨l,hkeep⟩ ((joined_live_left keep a b ⟨l,hkeep⟩).mp hl))
    · let ll : SelectedCopy (Finset.univ \ keep) := ⟨l,complement_mem keep l hkeep⟩
      rw [joined_genealogy_right keep a b ll]
      exact mapLabels_wellLabelled Subtype.val Subtype.val_injective _
        (hb.wellLabelled ll ((joined_live_right keep a b ll).mp hl))

theorem joinedState_sourceValid (N : RootedBinary V E X) (sample : Copy → X)
    (ha : SourceValid N (selectedSample sample keep) a)
    (hb : SourceValid N (selectedSample sample (Finset.univ \ keep)) b) :
    SourceValid N sample (joinedState keep a b) := by
  refine ⟨joinedState_valid keep a b ha.forest hb.forest,?_⟩
  intro x
  by_cases hx : x ∈ keep
  · rw [joined_copyLocation_left keep a b ⟨x,hx⟩]
    exact ha.original_descendant ⟨x,hx⟩
  · rw [joined_copyLocation_right keep a b ⟨x,complement_mem keep x hx⟩]
    exact hb.original_descendant ⟨x,complement_mem keep x hx⟩

theorem joinedState_view :
    selectedView (joinedState keep a b) Finset.univ = joinViews keep
      (liftView keep (selectedView a Finset.univ))
      (liftView (Finset.univ \ keep) (selectedView b Finset.univ)) := by
  apply SelectedView.ext
  · funext x
    change (if x ∈ Finset.univ then
      ((joinedState keep a b).genealogy ((joinedState keep a b).ancestor x)).prune Finset.univ
      else none) = if x ∈ keep then
        (liftView keep (selectedView a Finset.univ)).genealogy x else
        (liftView (Finset.univ \ keep) (selectedView b Finset.univ)).genealogy x
    rw [if_pos (Finset.mem_univ x),
      UnifiedLean.Source.SourceCompletedUnrankedTree.full_prune]
    by_cases hx : x ∈ keep
    · rw [if_pos hx, lifted_original_genealogy keep a ⟨x,hx⟩,
        joined_ancestor_left keep a b ⟨x,hx⟩, joined_genealogy_left]
    · rw [if_neg hx, lifted_original_genealogy (Finset.univ \ keep) b
        ⟨x,complement_mem keep x hx⟩,
        joined_ancestor_right keep a b ⟨x,complement_mem keep x hx⟩, joined_genealogy_right]
  · funext x
    change (if x ∈ Finset.univ then some (copyLocation (joinedState keep a b) x) else none) =
      if x ∈ keep then (liftView keep (selectedView a Finset.univ)).population x else
        (liftView (Finset.univ \ keep) (selectedView b Finset.univ)).population x
    rw [if_pos (Finset.mem_univ x)]
    by_cases hx : x ∈ keep
    · rw [if_pos hx,lifted_original_population keep a ⟨x,hx⟩,
        joined_copyLocation_left keep a b ⟨x,hx⟩]
    · rw [if_neg hx,lifted_original_population (Finset.univ \ keep) b
        ⟨x,complement_mem keep x hx⟩,
        joined_copyLocation_right keep a b ⟨x,complement_mem keep x hx⟩]
  · rfl

/-- The literal original encoder supplies a witness for every admitted local
panel pair. No equality of dead decoded garbage or ranked histories is used. -/
noncomputable def joinCode (N : RootedBinary V E X) {sample : Copy → X}
    (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) : Code N sample :=
  encodeActual N sample (joinedState keep (state a) (state b))
    (joinedState_sourceValid keep (state a) (state b) N sample a.property b.property)

theorem joinCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) :
    selectedView (state (joinCode keep N a b)) Finset.univ = joinViews keep
      (liftView keep (selectedView (state a) Finset.univ))
      (liftView (Finset.univ \ keep) (selectedView (state b) Finset.univ)) := by
  change selectedView (decodeSnapshot N.root (encodeSnapshot
    (joinedState keep (state a) (state b))
    (joinedState_sourceValid keep (state a) (state b) N sample a.property b.property).forest))
    Finset.univ = _
  rw [decode_encode_selectedView]
  exact joinedState_view keep (state a) (state b)

theorem admitted_join_view (N : RootedBinary V E X) {sample : Copy → X}
    (ab : SelectedIndex N (selectedSample sample keep) Finset.univ ×
      SelectedIndex N (selectedSample sample (Finset.univ \ keep)) Finset.univ) :
    ∃ d : Code N sample, selectedView (state d) Finset.univ = joinViews keep
      (liftView keep ab.1.val) (liftView (Finset.univ \ keep) ab.2.val) := by
  obtain ⟨a,ha⟩ := ab.1.property
  obtain ⟨b,hb⟩ := ab.2.property
  refine ⟨joinCode keep N a b,?_⟩
  rw [joinCode_view,ha,hb]

/-- For admitted panel products the inherited total index never falls back to
the entering index. This does not change the inherited executable search. -/
theorem joinIndex_value (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample)
    (ab : SelectedIndex N (selectedSample sample keep) Finset.univ ×
      SelectedIndex N (selectedSample sample (Finset.univ \ keep)) Finset.univ) :
    (joinIndex N s keep ab).val = joinViews keep
      (liftView keep ab.1.val) (liftView (Finset.univ \ keep) ab.2.val) := by
  unfold joinIndex viewIndex
  rw [dif_pos (admitted_join_view keep N ab)]

#print axioms joinedState_valid
#print axioms joinedState_sourceValid
#print axioms joinCode_view
#print axioms admitted_join_view
#print axioms joinIndex_value
end GProgram.G7.ConstructivePanelJoin
