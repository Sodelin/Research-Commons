import UnifiedLean.Source.SourceNaturalInitialization
import Mathlib.Data.Finset.Union

/-!
# Actual labelled unranked genealogy observation

Contributor: GPT-6.1 Sol / continue_g_research, 2026-10-02.
Standard unordered-tree quotient mathematics is used, without a novelty claim.
The inherited original-copy Genealogy is quotiented only by recursively
generated child swaps. There is no associativity, leaf relabelling, or erasure
of binary ancestry topology. Actual selected-label pruning descends to this
quotient. A concrete finite unranked forest observer then instantiates the
already-derived natural calendar projection law.

This is an actual observer instance on the constructed finite source law.
Physical exponential winner/time/reset path identification, ancestral
completion, independently initialized smaller-copy law and timed observation
remain separate. No desired probability equality is a structure field.
-/
namespace UnifiedLean.Source.UnrankedGenealogyObservation
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical

variable {Copy : Type*} [DecidableEq Copy]

/-- Exact nonplane binary-tree equivalence: swaps at any graft, with only
equivalence closure and graft congruence. Labels and rooted topology remain. -/
inductive UnorderedEquiv : Genealogy Copy → Genealogy Copy → Prop
  | refl (a) : UnorderedEquiv a a
  | symm {a b} : UnorderedEquiv a b → UnorderedEquiv b a
  | trans {a b c} : UnorderedEquiv a b → UnorderedEquiv b c → UnorderedEquiv a c
  | graft {a b c d} : UnorderedEquiv a c → UnorderedEquiv b d →
      UnorderedEquiv (.graft a b) (.graft c d)
  | swap (a b) : UnorderedEquiv (.graft a b) (.graft b a)

def genealogySetoid : Setoid (Genealogy Copy) where
  r := UnorderedEquiv
  iseqv := ⟨UnorderedEquiv.refl, UnorderedEquiv.symm, UnorderedEquiv.trans⟩

abbrev UnrankedTree (Copy : Type*) := Quotient (genealogySetoid (Copy := Copy))

def toUnranked (a : Genealogy Copy) : UnrankedTree Copy := Quotient.mk _ a

theorem toUnranked_eq_iff (a b : Genealogy Copy) :
    toUnranked a = toUnranked b ↔ UnorderedEquiv a b :=
  Quotient.eq

theorem unordered_leaves {a b : Genealogy Copy} (h : UnorderedEquiv a b) :
    a.leaves = b.leaves := by
  induction h with
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | graft _ _ ih1 ih2 => simp only [Genealogy.leaves, ih1, ih2]
  | swap a b => exact Finset.union_comm _ _

theorem unordered_wellLabelled {a b : Genealogy Copy} (h : UnorderedEquiv a b) :
    a.WellLabelled ↔ b.WellLabelled := by
  induction h with
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @graft a b c d h1 h2 ih1 ih2 =>
      simp only [Genealogy.WellLabelled, ih1, ih2, unordered_leaves h1, unordered_leaves h2]
  | swap a b =>
      constructor
      · rintro ⟨ha,hb,hd⟩; exact ⟨hb,ha,hd.symm⟩
      · rintro ⟨hb,ha,hd⟩; exact ⟨ha,hb,hd.symm⟩

def treeLeaves : UnrankedTree Copy → Finset Copy :=
  Quotient.lift Genealogy.leaves (fun _ _ h => unordered_leaves h)

def treeWellLabelled : UnrankedTree Copy → Prop :=
  Quotient.lift Genealogy.WellLabelled (fun _ _ h => propext (unordered_wellLabelled h))

/-- No extra erasure of original leaf labels is introduced by the quotient. -/
theorem toUnranked_equal_leaves {a b : Genealogy Copy}
    (h : toUnranked a = toUnranked b) : a.leaves = b.leaves :=
  unordered_leaves ((toUnranked_eq_iff a b).mp h)

def OptionEquiv : Option (Genealogy Copy) → Option (Genealogy Copy) → Prop
  | none, none => True
  | some a, some b => UnorderedEquiv a b
  | _, _ => False

lemma optionEquiv_refl (a : Option (Genealogy Copy)) : OptionEquiv a a := by
  cases a with
  | none => trivial
  | some a => exact UnorderedEquiv.refl a

lemma optionEquiv_symm {a b : Option (Genealogy Copy)} (h : OptionEquiv a b) :
    OptionEquiv b a := by
  cases a <;> cases b <;> simp only [OptionEquiv] at h ⊢
  all_goals first | trivial | exact UnorderedEquiv.symm h

lemma optionEquiv_trans {a b c : Option (Genealogy Copy)}
    (h1 : OptionEquiv a b) (h2 : OptionEquiv b c) : OptionEquiv a c := by
  cases a <;> cases b <;> cases c <;> simp only [OptionEquiv] at h1 h2 ⊢
  all_goals first | trivial | contradiction | exact UnorderedEquiv.trans h1 h2

lemma joinPruned_respects {a b c d : Option (Genealogy Copy)}
    (h1 : OptionEquiv a c) (h2 : OptionEquiv b d) :
    OptionEquiv (Genealogy.joinPruned a b) (Genealogy.joinPruned c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [OptionEquiv, Genealogy.joinPruned] at h1 h2 ⊢
  all_goals first | trivial | contradiction | assumption | exact UnorderedEquiv.graft h1 h2

lemma joinPruned_swap (a b : Option (Genealogy Copy)) :
    OptionEquiv (Genealogy.joinPruned a b) (Genealogy.joinPruned b a) := by
  cases a <;> cases b <;> simp only [Genealogy.joinPruned, OptionEquiv]
  all_goals first | trivial | exact UnorderedEquiv.refl _ | exact UnorderedEquiv.swap _ _

/-- Selected-label restriction, including empty/unary suppression, is
well defined for exact rooted unranked binary genealogies. -/
theorem unordered_prune (keep : Finset Copy) {a b : Genealogy Copy}
    (h : UnorderedEquiv a b) : OptionEquiv (a.prune keep) (b.prune keep) := by
  induction h with
  | refl a => exact optionEquiv_refl _
  | symm _ ih => exact optionEquiv_symm ih
  | trans _ _ ih1 ih2 => exact optionEquiv_trans ih1 ih2
  | graft _ _ ih1 ih2 => exact joinPruned_respects ih1 ih2
  | swap a b => exact joinPruned_swap _ _

def optionUnranked (a : Option (Genealogy Copy)) : Option (UnrankedTree Copy) :=
  a.map toUnranked

lemma optionUnranked_eq {a b : Option (Genealogy Copy)} (h : OptionEquiv a b) :
    optionUnranked a = optionUnranked b := by
  cases a <;> cases b <;> simp only [OptionEquiv] at h
  all_goals first | rfl | exact congrArg some (Quotient.sound h)

def pruneTree (keep : Finset Copy) : UnrankedTree Copy → Option (UnrankedTree Copy) :=
  Quotient.lift (fun a => optionUnranked (a.prune keep))
    (fun _ _ h => optionUnranked_eq (unordered_prune keep h))

theorem prune_toUnranked (keep : Finset Copy) (a : Genealogy Copy) :
    pruneTree keep (toUnranked a) = optionUnranked (a.prune keep) := rfl

def optionTreeLeaves : Option (UnrankedTree Copy) → Finset Copy
  | none => ∅
  | some a => treeLeaves a

lemma optionUnranked_leaves (a : Option (Genealogy Copy)) :
    optionTreeLeaves (optionUnranked a) = Genealogy.optionLeaves a := by
  cases a <;> rfl

theorem pruneTree_leaves [Fintype Copy] (keep : Finset Copy) (a : UnrankedTree Copy) :
    optionTreeLeaves (pruneTree keep a) = treeLeaves a ∩ keep := by
  refine Quotient.inductionOn a ?_
  intro t
  change optionTreeLeaves (optionUnranked (t.prune keep)) = t.leaves ∩ keep
  rw [optionUnranked_leaves]
  exact Genealogy.prune_leaves keep t

variable {V E X : Type*} [Fintype Copy]

/-- A finite forest set of actual pruned unranked original-labelled trees.
Duplicate per-leaf records of one component are collapsed. Original population,
register, survivor IDs and global event history are not observations here. -/
noncomputable def unrankedForest (v : SelectedView V E Copy) : Finset (UnrankedTree Copy) :=
  Finset.univ.biUnion (fun x => match v.genealogy x with
    | none => ∅
    | some t => {toUnranked t})

noncomputable def sourceUnrankedForest (s : State V E Copy) (keep : Finset Copy) :
    Finset (UnrankedTree Copy) := unrankedForest (selectedView s keep)

lemma mem_unrankedForest (v : SelectedView V E Copy) (q : UnrankedTree Copy) :
    q ∈ unrankedForest v ↔
      ∃ x t, v.genealogy x = some t ∧ toUnranked t = q := by
  classical
  simp only [unrankedForest, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x,hx⟩
    cases ht : v.genealogy x with
    | none => simp [ht] at hx
    | some t =>
        have he : q = toUnranked t := by simpa [ht] using hx
        exact ⟨x,t,ht,he.symm⟩
  · rintro ⟨x,t,ht,rfl⟩
    exact ⟨x,by simp [ht]⟩

lemma mem_sourceUnrankedForest (s : State V E Copy) (keep : Finset Copy)
    (q : UnrankedTree Copy) : q ∈ sourceUnrankedForest s keep ↔
      ∃ x ∈ keep, ∃ t, (s.genealogy (s.ancestor x)).prune keep = some t ∧
        toUnranked t = q := by
  change q ∈ unrankedForest (selectedView s keep) ↔ _
  rw [mem_unrankedForest]
  constructor
  · rintro ⟨x,t,ht,hq⟩
    have hx : x ∈ keep := by
      by_contra hn
      simp [selectedView,selectedGenealogy,hn] at ht
    exact ⟨x,hx,t,by simpa [selectedView,selectedGenealogy,hx] using ht,hq⟩
  · rintro ⟨x,hx,t,ht,hq⟩
    exact ⟨x,t,by simpa [selectedView,selectedGenealogy,hx] using ht,hq⟩

lemma forest_member_live_witness (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {q : UnrankedTree Copy} (hq : q ∈ sourceUnrankedForest s keep) :
    ∃ l ∈ s.live, optionUnranked ((s.genealogy l).prune keep) = some q := by
  obtain ⟨x,hx,t,ht,hqt⟩ := (mem_sourceUnrankedForest s keep q).mp hq
  refine ⟨s.ancestor x,hs.ancestor_live x,?_⟩
  simp only [ht,optionUnranked,Option.map_some]
  exact congrArg some hqt

lemma treeLeaves_from_prune {t : Genealogy Copy} {keep : Finset Copy}
    {q : UnrankedTree Copy} (h : optionUnranked (t.prune keep) = some q) :
    treeLeaves q = t.leaves ∩ keep := by
  have hl := optionUnranked_leaves (t.prune keep)
  rw [h] at hl
  exact hl.trans (Genealogy.prune_leaves keep t)

/-- Every observed component is an actual well-labelled binary genealogy;
the observer does not create duplicate leaves or refitted components. -/
theorem source_unranked_forest_wellLabelled (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {q : UnrankedTree Copy} (hq : q ∈ sourceUnrankedForest s keep) :
    treeWellLabelled q := by
  obtain ⟨l,hl,hp⟩ := forest_member_live_witness s hs keep hq
  have hw := Genealogy.prune_wellLabelled keep (s.genealogy l) (hs.wellLabelled l hl)
  cases ht : (s.genealogy l).prune keep with
  | none => simp [ht,optionUnranked] at hp
  | some t =>
      have he : toUnranked t = q := by simpa [ht,optionUnranked] using hp
      rw [← he]
      change t.WellLabelled
      simpa only [ht,Genealogy.optionWellLabelled] using hw

/-- Exactly the selected original labels occur in the observed forest. -/
theorem source_unranked_forest_covers (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (x : Copy) :
    (∃ q ∈ sourceUnrankedForest s keep, x ∈ treeLeaves q) ↔ x ∈ keep := by
  constructor
  · rintro ⟨q,hq,hx⟩
    obtain ⟨l,hl,hp⟩ := forest_member_live_witness s hs keep hq
    rw [treeLeaves_from_prune hp] at hx
    exact (Finset.mem_inter.mp hx).2
  · intro hx
    have hxl : x ∈ (s.genealogy (s.ancestor x)).leaves :=
      (hs.leaf_fiber (s.ancestor x) (hs.ancestor_live x) x).mpr rfl
    have hpr := Genealogy.prune_leaves keep (s.genealogy (s.ancestor x))
    cases ht : (s.genealogy (s.ancestor x)).prune keep with
    | none =>
        rw [ht] at hpr
        have hi := Finset.mem_inter.mpr ⟨hxl,hx⟩
        rw [← hpr] at hi
        exact False.elim (Finset.notMem_empty x hi)
    | some t =>
        refine ⟨toUnranked t,(mem_sourceUnrankedForest s keep _).mpr ⟨x,hx,t,ht,rfl⟩,?_⟩
        rw [ht] at hpr
        change t.leaves = (s.genealogy (s.ancestor x)).leaves ∩ keep at hpr
        change x ∈ t.leaves
        rw [hpr]
        exact Finset.mem_inter.mpr ⟨hxl,hx⟩

/-- Distinct observed components partition the selected labels. The proof
uses the actual source leaf/ancestor fibres, not supplied partition metadata. -/
theorem source_unranked_forest_disjoint (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {q r : UnrankedTree Copy}
    (hq : q ∈ sourceUnrankedForest s keep) (hr : r ∈ sourceUnrankedForest s keep)
    (hqr : q ≠ r) : Disjoint (treeLeaves q) (treeLeaves r) := by
  apply Finset.disjoint_left.mpr
  intro x hxq hxr
  obtain ⟨l,hl,hpl⟩ := forest_member_live_witness s hs keep hq
  obtain ⟨m,hm,hpm⟩ := forest_member_live_witness s hs keep hr
  rw [treeLeaves_from_prune hpl] at hxq
  rw [treeLeaves_from_prune hpm] at hxr
  have hxl := (hs.leaf_fiber l hl x).mp (Finset.mem_inter.mp hxq).1
  have hxm := (hs.leaf_fiber m hm x).mp (Finset.mem_inter.mp hxr).1
  have hlm : l = m := hxl.symm.trans hxm
  rw [← hlm] at hpm
  exact hqr (Option.some.inj (hpl.symm.trans hpm))

theorem sourceUnrankedForest_of_same_selectedView (s t : State V E Copy)
    (keep : Finset Copy) (h : selectedView s keep = selectedView t keep) :
    sourceUnrankedForest s keep = sourceUnrankedForest t keep := by
  unfold sourceUnrankedForest
  rw [h]

variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- The supplied arbitrary-readout interface is now instantiated by an actual
unranked labelled forest observer on the constructed natural source law. -/
theorem natural_calendar_unranked_forest_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (keep : Finset Copy) :
    (naturalCalendarLaw N C sample H p common r).map
      (fun s => sourceUnrankedForest (state s) keep) =
    (naturalSelectedCalendarLaw N C sample H p common r keep).map
      (fun v => unrankedForest v.val) := by
  exact natural_calendar_endpoint_probability N C sample H p common r keep
    (fun v => unrankedForest v.val)

#print axioms toUnranked_eq_iff
#print axioms unordered_leaves
#print axioms unordered_wellLabelled
#print axioms unordered_prune
#print axioms pruneTree_leaves
#print axioms source_unranked_forest_wellLabelled
#print axioms source_unranked_forest_covers
#print axioms source_unranked_forest_disjoint
#print axioms sourceUnrankedForest_of_same_selectedView
#print axioms natural_calendar_unranked_forest_law
end UnifiedLean.Source.UnrankedGenealogyObservation
