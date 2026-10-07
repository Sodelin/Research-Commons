import G2FaithfulPairAgeDecoration
import UnifiedLean.Source.UniformizedSourceStep

/-!
# Actual original-source graft ages

Contributor: dot (OpenAI), 6 October 2026. New reconstruction of the missing
deterministic interface. Original states, legal mergers, destination coding,
copy labels, locations and registers are unchanged. This is not recovery of
the missing historical source bytes or a probability/chronology assertion.
-/

namespace GProgram.G2.SourceGraftDecoration
set_option backward.isDefEq.respectTransparency false
open GProgram.SourceForest Nanuq.Source
open GProgram.G2.FaithfulPairAgeDecoration
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.SourceForestKingmanPopulationProjection
open scoped Classical

variable {V E Copy X : Type*} [DecidableEq Copy] [Fintype Copy]

/-- One matrix decorates every actual live genealogy on its own leaf pairs. -/
noncomputable def ForestDecorates (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) : Prop :=
  ∀ l ∈ s.live, ∃ d : Decoration (s.genealogy l),
    ∀ x ∈ (s.genealogy l).leaves, ∀ y ∈ (s.genealogy l).leaves,
      M x y = pairAge leafAge (s.genealogy l) d x y

/-- The actual merger changes exactly the two cross-operand ancestral blocks. -/
noncomputable def mergeAgeMatrix (s : State V E Copy) (a b : Copy) (age : ℝ)
    (M : Copy → Copy → ℝ) (x y : Copy) : ℝ :=
  if (s.ancestor x = a ∧ s.ancestor y = b) ∨
      (s.ancestor x = b ∧ s.ancestor y = a) then age else M x y

lemma same_operand_keeps_age (s : State V E Copy) {a b l x y : Copy}
    {age : ℝ} {M : Copy → Copy → ℝ} (hab : a ≠ b)
    (hx : s.ancestor x = l) (hy : s.ancestor y = l) :
    mergeAgeMatrix s a b age M x y = M x y := by
  have hn : ¬ ((l = a ∧ l = b) ∨ (l = b ∧ l = a)) := by
    intro h
    rcases h with h | h
    · exact hab (h.1.symm.trans h.2)
    · exact hab (h.2.symm.trans h.1)
  simp only [mergeAgeMatrix,hx,hy,if_neg hn]

/-- Graft the two actual operand decorations and retain every earlier graft.
No chronological inequality is assumed or needed for this identity. -/
theorem actual_merge_decorates (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) {a b : Copy} (hm : LegalMerge s a b)
    (age : ℝ) (hM : ForestDecorates leafAge M s) :
    ForestDecorates leafAge (mergeAgeMatrix s a b age M) (merge s a b) := by
  intro l hl
  have hll : l ∈ s.live := (Finset.mem_erase.mp hl).2
  by_cases hla : l = a
  · subst l
    obtain ⟨da,hda⟩ := hM a hm.first_live
    obtain ⟨db,hdb⟩ := hM b hm.second_live
    have hab : Disjoint (s.genealogy a).leaves (s.genealogy b).leaves := by
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      exact hm.different (((hs.leaf_fiber a hm.first_live x).mp hxa).symm.trans
        ((hs.leaf_fiber b hm.second_live x).mp hxb))
    have hg : (merge s a b).genealogy a = .graft (s.genealogy a) (s.genealogy b) := by
      simp [merge]
    rw [hg]
    refine ⟨(age,da,db),?_⟩
    intro x hx y hy
    by_cases hxa : x ∈ (s.genealogy a).leaves
    · by_cases hya : y ∈ (s.genealogy a).leaves
      · rw [pairAge_left leafAge _ _ (age,da,db) hxa hya,
          same_operand_keeps_age s hm.different
            ((hs.leaf_fiber a hm.first_live x).mp hxa)
            ((hs.leaf_fiber a hm.first_live y).mp hya)]
        exact hda x hxa y hya
      · have hyb : y ∈ (s.genealogy b).leaves := (Finset.mem_union.mp hy).resolve_left hya
        rw [pairAge_cross leafAge _ _ (age,da,db) hab hxa hyb]
        simp [mergeAgeMatrix,(hs.leaf_fiber a hm.first_live x).mp hxa,
          (hs.leaf_fiber b hm.second_live y).mp hyb]
    · have hxb : x ∈ (s.genealogy b).leaves := (Finset.mem_union.mp hx).resolve_left hxa
      by_cases hya : y ∈ (s.genealogy a).leaves
      · have hyb : y ∉ (s.genealogy b).leaves :=
          fun h => (Finset.disjoint_left.mp hab) hya h
        have hnleft : ¬ (x ∈ (s.genealogy a).leaves ∧ y ∈ (s.genealogy a).leaves) :=
          fun h => hxa h.1
        have hnright : ¬ (x ∈ (s.genealogy b).leaves ∧ y ∈ (s.genealogy b).leaves) :=
          fun h => hyb h.2
        simp only [pairAge,if_neg hnleft,if_neg hnright]
        simp [mergeAgeMatrix,(hs.leaf_fiber b hm.second_live x).mp hxb,
          (hs.leaf_fiber a hm.first_live y).mp hya]
      · have hyb : y ∈ (s.genealogy b).leaves := (Finset.mem_union.mp hy).resolve_left hya
        rw [pairAge_right leafAge _ _ (age,da,db) hab hxb hyb,
          same_operand_keeps_age s hm.different
            ((hs.leaf_fiber b hm.second_live x).mp hxb)
            ((hs.leaf_fiber b hm.second_live y).mp hyb)]
        exact hdb x hxb y hyb
  · have hg : (merge s a b).genealogy l = s.genealogy l := by
      simp only [merge,if_neg hla]
    rw [hg]
    obtain ⟨d,hd⟩ := hM l hll
    refine ⟨d,?_⟩
    intro x hx y hy
    rw [same_operand_keeps_age s hm.different
      ((hs.leaf_fiber l hll x).mp hx) ((hs.leaf_fiber l hll y).mp hy)]
    exact hd x hx y hy

/-- The original ancestor update joins exactly the two old operand blocks. -/
lemma merge_new_pair_iff (s : State V E Copy) {a b x y : Copy} (hab : a ≠ b) :
    (s.ancestor x ≠ s.ancestor y ∧ (merge s a b).ancestor x = (merge s a b).ancestor y) ↔
      ((s.ancestor x = a ∧ s.ancestor y = b) ∨
       (s.ancestor x = b ∧ s.ancestor y = a)) := by
  by_cases hx : s.ancestor x = b
  · by_cases hy : s.ancestor y = b
    · simp [merge,hx,hy,hab,Ne.symm hab]
    · simp only [merge,if_pos hx,if_neg hy]
      constructor
      · intro h
        exact Or.inr ⟨hx,h.2.symm⟩
      · intro h
        rcases h with h | h
        · exact False.elim (hy h.2)
        · exact ⟨fun e => hy (e.symm.trans hx),h.2.symm⟩
  · by_cases hy : s.ancestor y = b
    · simp only [merge,if_neg hx,if_pos hy]
      constructor
      · intro h
        exact Or.inl ⟨h.2,hy⟩
      · intro h
        rcases h with h | h
        · exact ⟨fun e => hx (e.trans hy),h.1⟩
        · exact False.elim (hx h.1)
    · simp only [merge,if_neg hx,if_neg hy]
      constructor
      · intro h
        exact False.elim (h.1 h.2)
      · intro h
        rcases h with h | h
        · exact False.elim (hy h.2)
        · exact False.elim (hx h.1)

variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- Destination-only readout: update a pair precisely when different old
ancestors become equal in the supplied actual destination state. -/
noncomputable def codedAgeUpdate (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (age : ℝ) (M : Copy → Copy → ℝ) (x y : Copy) : ℝ :=
  if (state s).ancestor x ≠ (state s).ancestor y ∧
      (state d).ancestor x = (state d).ancestor y then age else M x y

/-- This identifies the explicit coded update with the actual legal merger;
it is derived from the source destination and exact snapshot ancestor fields. -/
theorem coded_update_is_actual_graft (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (age : ℝ) (M : Copy → Copy → ℝ) :
    codedAgeUpdate N s (stepDestination N s (some p)) age M =
      mergeAgeMatrix (state s) p.2.val.1 p.2.val.2 age M := by
  have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  funext x y
  change (if (state s).ancestor x ≠ (state s).ancestor y ∧
      (merge (state s) p.2.val.1 p.2.val.2).ancestor x =
        (merge (state s) p.2.val.1 p.2.val.2).ancestor y then age else M x y) = _
  simp only [mergeAgeMatrix,merge_new_pair_iff (state s) hm.different]

lemma coded_self_update (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (age : ℝ) (M : Copy → Copy → ℝ) :
    codedAgeUpdate N s s age M = M := by
  funext x y
  simp [codedAgeUpdate]

lemma snapshot_preserves_decorates (root : V) (s : State V E Copy) (hs : Valid s)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (hM : ForestDecorates leafAge M s) :
    ForestDecorates leafAge M (decodeSnapshot root (encodeSnapshot s hs)) := by
  intro l hl
  have hl' : l ∈ s.live := hl
  rw [decode_encode_live_genealogy root s hs hl']
  exact hM l hl'

theorem coded_graft_decorates (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (s : Code N sample)
    (p : Choice N s) (age : ℝ) (hM : ForestDecorates leafAge M (state s)) :
    ForestDecorates leafAge (codedAgeUpdate N s (stepDestination N s (some p)) age M)
      (state (stepDestination N s (some p))) := by
  have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  rw [coded_update_is_actual_graft]
  exact snapshot_preserves_decorates N.root (merge (state s) p.2.val.1 p.2.val.2)
    (merge_valid (state s) s.property.forest hm) leafAge _
    (actual_merge_decorates leafAge M (state s) s.property.forest hm age hM)

lemma initial_forest_decorates (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (leafAge : Copy → ℝ) :
    ForestDecorates leafAge (fun x _ => leafAge x) (initial N sample register) := by
  intro l hl
  refine ⟨PUnit.unit,?_⟩
  intro x hx y hy
  have he : x = l := Finset.mem_singleton.mp hx
  subst x
  rfl

#print axioms same_operand_keeps_age
#print axioms actual_merge_decorates
#print axioms merge_new_pair_iff
#print axioms coded_update_is_actual_graft
#print axioms coded_self_update
#print axioms snapshot_preserves_decorates
#print axioms coded_graft_decorates
#print axioms initial_forest_decorates

end GProgram.G2.SourceGraftDecoration
