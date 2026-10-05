import SourceForestKingmanPopulationProjection

/-!
# Silent original-population mergers under actual genealogy pruning

Contributor: dot, 2026-10-02. This fills the silent-merger component of the
inherited actual source generator/projectivity gate. The readout retains each
selected original copy's whole pruned genealogy, its ORIGINAL population and
the original shared register. Representative IDs may be invisible; they are
not substituted for selected labels. Source-legal mergers involving at most
one visible operand leave this readout unchanged. Transition-semigroup and
whole calendar/pulse projectivity are subsequent obligations.
-/
namespace UnifiedLean.Source.SourceForestSilentPruning
open GProgram.SourceForest
open scoped Classical
variable {V E Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

lemma genealogy_leaves_nonempty (t : Genealogy Copy) : t.leaves.Nonempty := by
  induction t with
  | leaf x => exact ⟨x,Finset.mem_singleton_self x⟩
  | graft a b ih _ =>
      obtain ⟨x,hx⟩ := ih
      exact ⟨x,Finset.mem_union.mpr (Or.inl hx)⟩

lemma optionLeaves_empty_iff_none (t : Option (Genealogy Copy)) :
    Genealogy.optionLeaves t = ∅ ↔ t = none := by
  cases t with
  | none => simp [Genealogy.optionLeaves]
  | some t =>
      simp only [Genealogy.optionLeaves,Option.some_ne_none,iff_false]
      exact (genealogy_leaves_nonempty t).ne_empty

lemma prune_none_iff_no_selected_leaves (keep : Finset Copy) (t : Genealogy Copy) :
    t.prune keep = none ↔ t.leaves ∩ keep = ∅ := by
  rw [← optionLeaves_empty_iff_none, Genealogy.prune_leaves]

/-- Selected copies retain full pruned merger subtrees, not just block counts. -/
noncomputable def selectedGenealogy (s : State V E Copy) (keep : Finset Copy)
    (x : Copy) : Option (Genealogy Copy) :=
  if x ∈ keep then (s.genealogy (s.ancestor x)).prune keep else none

noncomputable def selectedLocation (s : State V E Copy) (keep : Finset Copy)
    (x : Copy) : Option (Location V E) :=
  if x ∈ keep then some (copyLocation s x) else none

@[ext] structure SelectedView (V E Copy : Type*) where
  genealogy : Copy → Option (Genealogy Copy)
  population : Copy → Option (Location V E)
  register : V → Bool

noncomputable def selectedView (s : State V E Copy) (keep : Finset Copy) :
    SelectedView V E Copy where
  genealogy := selectedGenealogy s keep
  population := selectedLocation s keep
  register := s.register

lemma selected_label_not_in_invisible_operand (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {l x : Copy} (hl : l ∈ s.live)
    (hi : (s.genealogy l).prune keep = none) (hx : x ∈ keep) : s.ancestor x ≠ l := by
  intro heq
  have he : (s.genealogy l).leaves ∩ keep = ∅ :=
    (prune_none_iff_no_selected_leaves keep _).mp hi
  have hm : x ∈ (s.genealogy l).leaves ∩ keep :=
    Finset.mem_inter.mpr ⟨(hs.leaf_fiber l hl x).mpr heq,hx⟩
  rw [he] at hm
  exact Finset.notMem_empty _ hm

/-- Invisible operand means exactly an empty selected genealogy, not an
original representative ID outside keep. -/
lemma invisible_operand_iff_pruned_none (s : State V E Copy) (keep : Finset Copy)
    (l : Copy) : ¬ (selectedBlock s keep l).Nonempty ↔
      (s.genealogy l).prune keep = none := by
  rw [prune_none_iff_no_selected_leaves]
  exact Finset.not_nonempty_iff_eq_empty

/-- Full selected genealogy maps are invariant under a source-legal merger
with at least one invisible operand. -/
theorem selectedGenealogy_merge_silent (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hi : (s.genealogy a).prune keep = none ∨ (s.genealogy b).prune keep = none) :
    selectedGenealogy (merge s a b) keep = selectedGenealogy s keep := by
  funext x
  by_cases hx : x ∈ keep
  · simp only [selectedGenealogy,if_pos hx]
    by_cases hxb : s.ancestor x = b
    · simp only [merge,hxb,if_true,Genealogy.prune]
      rcases hi with ha | hb
      · simp [ha,Genealogy.joinPruned]
      · exact False.elim ((selected_label_not_in_invisible_operand s hs keep
          hm.second_live hb hx) hxb)
    · by_cases hxa : s.ancestor x = a
      · simp only [merge,if_neg hxb,hxa,if_true,Genealogy.prune]
        rcases hi with ha | hb
        · exact False.elim ((selected_label_not_in_invisible_operand s hs keep
            hm.first_live ha hx) hxa)
        · cases hp : (s.genealogy a).prune keep <;> simp [Genealogy.prune,hb,hp,Genealogy.joinPruned]
      · simp [merge,hxb,hxa]
  · simp only [selectedGenealogy,if_neg hx]

theorem selectedLocation_merge_unchanged (s : State V E Copy) (keep : Finset Copy)
    {a b : Copy} (hm : LegalMerge s a b) :
    selectedLocation (merge s a b) keep = selectedLocation s keep := by
  funext x
  unfold selectedLocation
  rw [merge_population_preserved s hm]

/-- Actual pruned forest/population/register state is unchanged. Silent
mergers are therefore zero terms in every readout's source generator. -/
theorem selectedView_merge_silent (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hi : ¬ (selectedBlock s keep a).Nonempty ∨ ¬ (selectedBlock s keep b).Nonempty) :
    selectedView (merge s a b) keep = selectedView s keep := by
  have hi' : (s.genealogy a).prune keep = none ∨ (s.genealogy b).prune keep = none :=
    hi.imp (invisible_operand_iff_pruned_none s keep a).mp
      (invisible_operand_iff_pruned_none s keep b).mp
  apply SelectedView.ext
  · exact selectedGenealogy_merge_silent s hs keep hm hi'
  · exact selectedLocation_merge_unchanged s keep hm
  · rfl

/-- The zero increment is derived from the ORIGINAL source merger/pruning
semantics, not postulated by a projected generator interface. -/
theorem silent_merger_readout_increment_zero (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hi : ¬ (selectedBlock s keep a).Nonempty ∨ ¬ (selectedBlock s keep b).Nonempty)
    (f : SelectedView V E Copy → ℝ) :
    f (selectedView (merge s a b) keep) - f (selectedView s keep) = 0 := by
  rw [selectedView_merge_silent s hs keep hm hi,sub_self]

#print axioms prune_none_iff_no_selected_leaves
#print axioms selected_label_not_in_invisible_operand
#print axioms invisible_operand_iff_pruned_none
#print axioms selectedGenealogy_merge_silent
#print axioms selectedLocation_merge_unchanged
#print axioms selectedView_merge_silent
#print axioms silent_merger_readout_increment_zero
end UnifiedLean.Source.SourceForestSilentPruning
