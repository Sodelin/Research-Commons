import G1ActualCurrentPanelInitialization

/-! Complete whole-forest assembly, with arbitrary original opaque input
subtrees restored. Contributor: dot, 2026-10-03. -/
namespace G1JointUnrankedForestAssembly
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceForestSilentPruning
open G1JointSeparatedSourceGeometry
open scoped Classical
variable {V E Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

def PrunedPanelSeparated (s : State V E Copy) (inside outside : Finset Copy) : Prop :=
  ∀ l ∈ s.live, (s.genealogy l).prune inside = none ∨ (s.genealogy l).prune outside = none

lemma population_separated_pruned_panels (s : State V E Copy) (hs : Valid s)
    (inside outside : Finset Copy) (hsep : PopulationSeparated s inside outside) :
    PrunedPanelSeparated s inside outside := by
  intro l hl
  by_cases hi : (s.genealogy l).prune inside = none
  · exact Or.inl hi
  · right
    apply (prune_none_iff_no_selected_leaves outside (s.genealogy l)).mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hni : ((s.genealogy l).leaves ∩ inside).Nonempty := by
      by_contra hn
      exact hi ((prune_none_iff_no_selected_leaves inside (s.genealogy l)).mpr (Finset.not_nonempty_iff_eq_empty.mp hn))
    obtain ⟨x,hx⟩ := hni
    obtain ⟨hxi,hxl⟩ := visible_copy_population s hs inside hl hx
    obtain ⟨hyo,hyl⟩ := visible_copy_population s hs outside hl hy
    exact hsep x hxi y hyo (hxl.trans hyl.symm)

lemma prune_eq_of_leaf_membership (t : Genealogy Copy) (A B : Finset Copy)
    (h : ∀ x ∈ t.leaves, x ∈ A ↔ x ∈ B) : t.prune A = t.prune B := by
  induction t with
  | leaf x => simp [Genealogy.prune,h x (Finset.mem_singleton_self _)]
  | graft a b iha ihb =>
      simp only [Genealogy.prune]
      rw [iha (fun x hx => h x (Finset.mem_union.mpr (Or.inl hx))),
        ihb (fun x hx => h x (Finset.mem_union.mpr (Or.inr hx)))]

lemma prune_union_of_left_empty (t : Genealogy Copy) (A B : Finset Copy)
    (h : t.prune A = none) : t.prune (A ∪ B) = t.prune B := by
  apply prune_eq_of_leaf_membership
  intro x hx
  have hn : x ∉ A := by
    intro ha
    have he := (prune_none_iff_no_selected_leaves A t).mp h
    have hm := Finset.mem_inter.mpr ⟨hx,ha⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  simp [hn]

lemma prune_union_of_right_empty (t : Genealogy Copy) (A B : Finset Copy)
    (h : t.prune B = none) : t.prune (A ∪ B) = t.prune A := by
  rw [Finset.union_comm]
  exact prune_union_of_left_empty t B A h

/-- No mixed current tree means union of the two full rooted unranked forest
sets retains EVERY original-labelled tree, with no count-only projection. -/
theorem actual_pruned_forest_union (s : State V E Copy) (hs : Valid s)
    (inside outside : Finset Copy) (hpure : PrunedPanelSeparated s inside outside) :
    sourceUnrankedForest s (inside ∪ outside) =
      sourceUnrankedForest s inside ∪ sourceUnrankedForest s outside := by
  ext q
  rw [Finset.mem_union]
  constructor
  · intro hq
    obtain ⟨x,hx,t,ht,he⟩ := (mem_sourceUnrankedForest s _ q).mp hq
    obtain hi | ho := hpure (s.ancestor x) (hs.ancestor_live x)
    · right
      have hxO : x ∈ outside := by
        rcases Finset.mem_union.mp hx with hxI | hxO
        · have hf : x ∈ (s.genealogy (s.ancestor x)).leaves ∩ inside :=
            Finset.mem_inter.mpr ⟨(hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl,hxI⟩
          rw [(prune_none_iff_no_selected_leaves inside _).mp hi] at hf
          exact False.elim (Finset.notMem_empty _ hf)
        · exact hxO
      rw [prune_union_of_left_empty _ inside outside hi] at ht
      exact (mem_sourceUnrankedForest s outside q).mpr ⟨x,hxO,t,ht,he⟩
    · left
      have hxI : x ∈ inside := by
        rcases Finset.mem_union.mp hx with hxI | hxO
        · exact hxI
        · have hf : x ∈ (s.genealogy (s.ancestor x)).leaves ∩ outside :=
            Finset.mem_inter.mpr ⟨(hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl,hxO⟩
          rw [(prune_none_iff_no_selected_leaves outside _).mp ho] at hf
          exact False.elim (Finset.notMem_empty _ hf)
      rw [prune_union_of_right_empty _ inside outside ho] at ht
      exact (mem_sourceUnrankedForest s inside q).mpr ⟨x,hxI,t,ht,he⟩
  · rintro (hq | hq)
    · obtain ⟨x,hx,t,ht,he⟩ := (mem_sourceUnrankedForest s inside q).mp hq
      obtain hi | ho := hpure (s.ancestor x) (hs.ancestor_live x)
      · rw [hi] at ht; contradiction
      · exact (mem_sourceUnrankedForest s _ q).mpr
          ⟨x,Finset.mem_union.mpr (Or.inl hx),t,(prune_union_of_right_empty _ inside outside ho).trans ht,he⟩
    · obtain ⟨x,hx,t,ht,he⟩ := (mem_sourceUnrankedForest s outside q).mp hq
      obtain hi | ho := hpure (s.ancestor x) (hs.ancestor_live x)
      · exact (mem_sourceUnrankedForest s _ q).mpr
          ⟨x,Finset.mem_union.mpr (Or.inr hx),t,(prune_union_of_left_empty _ inside outside hi).trans ht,he⟩
      · rw [ho] at ht; contradiction

#print axioms actual_pruned_forest_union
end G1JointUnrankedForestAssembly
