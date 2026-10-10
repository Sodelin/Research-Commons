import UnifiedLean.Source.SourceAncestralCompletion
import UnifiedLean.Source.UnrankedGenealogyObservation

/-!
# Actual completed ORIGINAL rooted unranked tree law

Contributor: dot, 2026-10-02. Instantiates the inherited exact child-swap
quotient on the constructed natural calendar-plus-ancestral-merger law.
Its supported output is one well-labelled binary tree with EVERY original
copy label, not an arbitrary supplied endpoint observer/law. The remaining
G2 obligations are its eventual continuous-time limit and transport to the
independently initialized selected-copy source. Timed closure is not claimed.
-/
namespace UnifiedLean.Source.SourceCompletedUnrankedTree
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical
variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy]

lemma full_prune (t : Genealogy Copy) : t.prune Finset.univ = some t := by
  induction t with
  | leaf x => simp [Genealogy.prune]
  | graft a b iha ihb => simp only [Genealogy.prune,iha,ihb,Genealogy.joinPruned]

lemma one_live_ancestor {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (hc : s.live.card = 1) : ∃ a ∈ s.live, ∀ x : Copy, s.ancestor x = a := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
  refine ⟨a,by rw [ha]; simp,?_⟩
  intro x
  have hx := hs.ancestor_live x
  simpa only [ha,Finset.mem_singleton] using hx

/-- Actual original-copy Valid fibres identify the completed tree's leaf set.
The observer discards only child order/hidden internal records, not leaf IDs. -/
theorem one_live_unranked_forest [Nonempty Copy] {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (hc : s.live.card = 1) :
    ∃ q : UnrankedTree Copy, sourceUnrankedForest s Finset.univ = {q} ∧
      treeWellLabelled q ∧ treeLeaves q = Finset.univ := by
  obtain ⟨a,ha,hanc⟩ := one_live_ancestor s hs hc
  refine ⟨toUnranked (s.genealogy a),?_,hs.wellLabelled a ha,?_⟩
  · ext q
    rw [mem_sourceUnrankedForest,Finset.mem_singleton]
    constructor
    · rintro ⟨x,_,t,ht,hq⟩
      rw [hanc x,full_prune] at ht
      have he : s.genealogy a = t := Option.some.inj ht
      exact hq.symm.trans (congrArg toUnranked he.symm)
    · intro hq
      obtain ⟨x⟩ := ‹Nonempty Copy›
      refine ⟨x,Finset.mem_univ x,s.genealogy a,?_,hq.symm⟩
      rw [hanc x,full_prune]
  · change (s.genealogy a).leaves = Finset.univ
    ext x
    rw [hs.leaf_fiber a ha x]
    simp [hanc x]

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

noncomputable def naturalCompletedUnrankedLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    PMF (Finset (UnrankedTree Copy)) :=
  (naturalCompletedLaw N C sample H p common r).map
    (fun s => sourceUnrankedForest (state s) Finset.univ)

/-- Concrete end-to-end constructed original graph/calendar/prior/completion
output: every supported forest is exactly one complete original-labelled
rooted UNRANKED binary tree. No arbitrary measured-colour/endpoint field. -/
theorem natural_completed_unranked_tree_support [Nonempty Copy] (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    {F : Finset (UnrankedTree Copy)}
    (hF : F ∈ (naturalCompletedUnrankedLaw N C sample H p common r).support) :
    ∃ q : UnrankedTree Copy, F = {q} ∧ treeWellLabelled q ∧ treeLeaves q = Finset.univ := by
  obtain ⟨s,hs,hobs⟩ := (PMF.mem_support_map_iff _ _ _).mp hF
  have hcard := (natural_completed_one_tree_support N C sample H p common r hs).2
  obtain ⟨q,hq,hw,hl⟩ := one_live_unranked_forest (state s) s.property.forest hcard
  exact ⟨q,hobs.symm.trans hq,hw,hl⟩

#print axioms one_live_unranked_forest
#print axioms natural_completed_unranked_tree_support
end UnifiedLean.Source.SourceCompletedUnrankedTree
