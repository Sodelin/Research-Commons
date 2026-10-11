import G1UnrankedSourceView
import UnifiedLean.Source.SourceAncestralCompletion
import UnifiedLean.Source.SourceCompletionHarmonic

/-!
# Specified labelled-comb event on the actual inherited quotient

Contributor: dot (OpenAI), 11 October 2026.
SOURCE-ONLY DRAFT: no compiler or audit acceptance. This implements the concrete
single-event/obstruction portion of the reviewed handoff90f99164. It does not
identify no-A-clade with one labelled comb, evaluate its completion coefficient,
or supply a full physical source-law continuation or natural-bank average.
This extension does prove actual ancestral-completion SUPPORT exclusion.
-/
namespace DotG34.SpecifiedCombEvent
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView
variable {Copy V E : Type*} [DecidableEq Copy]

/-- The order is prescribed. For [A1,...,Ak], the first cherry is (B,A1),
then A2,...,Ak are attached in that order. Child orientation alone is erased. -/
def comb (b : Copy) (as : List Copy) : Genealogy Copy :=
  as.foldl (fun t a => .graft t (.leaf a)) (.leaf b)

/-- A separate obstruction, not the desired event: a nontrivial subtree
whose leaves omit the distinguished B copy. -/
def hasBad (b : Copy) : Genealogy Copy → Prop
  | .leaf _ => False
  | .graft l r =>
      (2 ≤ (l.leaves ∪ r.leaves).card ∧ b ∉ l.leaves ∪ r.leaves) ∨
        hasBad b l ∨ hasBad b r

lemma hasBad_unordered (b : Copy) {t u : Genealogy Copy}
    (h : UnorderedEquiv t u) : hasBad b t ↔ hasBad b u := by
  induction h with
  | refl t => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | graft h1 h2 ih1 ih2 =>
      simp only [hasBad, unordered_leaves h1, unordered_leaves h2, ih1, ih2]
  | swap t u =>
      simp only [hasBad, Finset.union_comm]
      tauto

def badOnUnranked (b : Copy) : UnrankedTree Copy → Prop :=
  Quotient.lift (hasBad b) (fun _ _ h => propext (hasBad_unordered b h))

lemma fold_contains_B (b : Copy) (as : List Copy) (t : Genealogy Copy)
    (hb : b ∈ t.leaves) :
    b ∈ (as.foldl (fun u a => .graft u (.leaf a)) t).leaves := by
  induction as generalizing t with
  | nil => exact hb
  | cons a as ih =>
      apply ih
      exact Finset.mem_union_left _ hb

lemma fold_no_bad (b : Copy) (as : List Copy) (t : Genealogy Copy)
    (hb : b ∈ t.leaves) (ht : ¬ hasBad b t) :
    ¬ hasBad b (as.foldl (fun u a => .graft u (.leaf a)) t) := by
  induction as generalizing t with
  | nil => exact ht
  | cons a as ih =>
      apply ih
      · exact Finset.mem_union_left _ hb
      · simp only [hasBad]
        have hm : b ∈ t.leaves ∪ (Genealogy.leaf a).leaves :=
          Finset.mem_union_left _ hb
        simp only [hm, not_true_eq_false, and_false, ht, or_false, false_or]

lemma comb_no_bad (b : Copy) (as : List Copy) : ¬ hasBad b (comb b as) := by
  apply fold_no_bad
  · simp [Genealogy.leaves]
  · simp [hasBad]

/-- Exactly one labelled target. No label permutation or associativity quotient. -/
def specifiedEvent (b : Copy) (as : List Copy) (q : UnrankedTree Copy) : Prop :=
  q = toUnranked (comb b as)

lemma bad_excludes_specified (b : Copy) (as : List Copy) (t : Genealogy Copy)
    (ht : hasBad b t) : ¬ specifiedEvent b as (toUnranked t) := by
  intro he
  have hq : toUnranked t = toUnranked (comb b as) := he
  exact comb_no_bad b as
    ((hasBad_unordered b ((toUnranked_eq_iff _ _).mp hq)).mp ht)

/-- The obstruction follows the original copy's current ancestor through the
actual source merger, including when its old representative is removed. -/
lemma actual_merge_preserves_bad (b : Copy) (s : State V E Copy)
    (a c x : Copy) (ht : hasBad b (s.genealogy (s.ancestor x))) :
    hasBad b ((merge s a c).genealogy ((merge s a c).ancestor x)) := by
  by_cases hx : s.ancestor x = c
  · simp only [merge, hx, if_pos, ite_true]
    exact Or.inr (Or.inr (by simpa only [hx] using ht))
  · by_cases ha : s.ancestor x = a
    · simp only [merge, if_neg hx, if_pos ha]
      exact Or.inr (Or.inl (by simpa only [ha] using ht))
    · simpa only [merge, if_neg hx, if_neg ha] using ht

lemma actual_merge_bad_excludes_specified (b : Copy) (as : List Copy)
    (s : State V E Copy) (a c x : Copy)
    (ht : hasBad b (s.genealogy (s.ancestor x))) :
    ¬ specifiedEvent b as
      (toUnranked ((merge s a c).genealogy ((merge s a c).ancestor x))) :=
  bad_excludes_specified b as _ (actual_merge_preserves_bad b s a c x ht)

/-- The actual unranked view retains one genealogy per selected copy.
The B coordinate selects its completed tree without observing a private bank.
Its identification with the legal completed-topology event is a later binding. -/
def viewEvent (b : Copy) (as : List Copy) (v : UnrankedView V E Copy) : Prop :=
  v.genealogy b = some (toUnranked (comb b as))

/-- Distinct original copy labels and the nonempty A panel required for the
inherited coefficient; these are not required merely to define the event. -/
def AdmissibleLabels (b : Copy) (as : List Copy) : Prop :=
  as.Nodup ∧ b ∉ as ∧ as ≠ []

-- Remaining substantive source consumer: under AdmissibleLabels, establish
-- target-compatible carried-pref support and the unique next prescribed
-- unordered pair. Its two ordered source choices may produce different Codes;
-- their event continuation agrees on the inherited child-swap quotient.
-- Then derive the coefficient2^k/((k+1)!k!) from the actual ancestral recurrence.
-- A-only obstruction alone does not exclude a wrong B-A2 first merger.
/- Source-only exact target-compatible-frontier extension. It is intended for
insertion into the same namespace; no new carrier/process is introduced. -/
def internalClades : Genealogy Copy → Finset (Finset Copy)
  | .leaf _ => ∅
  | .graft l r => insert (l.leaves ∪ r.leaves) (internalClades l ∪ internalClades r)

lemma internalClades_unordered {t u : Genealogy Copy} (h : UnorderedEquiv t u) :
    internalClades t = internalClades u := by
  induction h with
  | refl t => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | graft h1 h2 ih1 ih2 =>
      simp only [internalClades,unordered_leaves h1,unordered_leaves h2,ih1,ih2]
  | swap t u => simp only [internalClades,Finset.union_comm]

lemma internalClade_subset_leaves {t : Genealogy Copy} {A : Finset Copy}
    (h : A ∈ internalClades t) : A ⊆ t.leaves := by
  induction t with
  | leaf x => simp [internalClades] at h
  | graft l r ihl ihr =>
      simp only [internalClades,Finset.mem_insert,Finset.mem_union] at h
      rcases h with h | h | h
      · simpa only [Genealogy.leaves,h]
      · exact Finset.Subset.trans (ihl h) Finset.subset_union_left
      · exact Finset.Subset.trans (ihr h) Finset.subset_union_right

def spineClades (S : Finset Copy) : List Copy → Finset (Finset Copy)
  | [] => ∅
  | a::as => insert (insert a S) (spineClades (insert a S) as)

lemma spineClade_contains_start (S : Finset Copy) (as : List Copy)
    {A : Finset Copy} (h : A ∈ spineClades S as) : S ⊆ A := by
  induction as generalizing S with
  | nil => simp [spineClades] at h
  | cons a as ih =>
      simp only [spineClades,Finset.mem_insert] at h
      rcases h with rfl | h
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.trans (Finset.subset_insert _ _) (ih _ h)

/-- Exact internal clades of the prescribed spine added to an already carried
pref tree. This retains every old clade instead of replacing that tree by a
fresh leaf on the original carrier. -/
lemma fold_internalClades (t : Genealogy Copy) (as : List Copy) :
    internalClades (as.foldl (fun u a => .graft u (.leaf a)) t) =
      internalClades t ∪ spineClades t.leaves as := by
  induction as generalizing t with
  | nil => simp [spineClades]
  | cons a as ih =>
      rw [List.foldl_cons,ih]
      ext A
      simp only [internalClades,Genealogy.leaves,spineClades,
        Finset.union_singleton,Finset.union_empty,Finset.mem_union,Finset.mem_insert]
      tauto

lemma first_label_in_spineClade (S : Finset Copy) (a : Copy) (as : List Copy)
    {A : Finset Copy} (h : A ∈ spineClades S (a::as)) : a ∈ A := by
  simp only [spineClades,Finset.mem_insert] at h
  rcases h with rfl | h
  · exact Finset.mem_insert_self _ _
  · exact spineClade_contains_start (insert a S) as h (Finset.mem_insert_self _ _)

/-- Exactly the next prescribed singleton can join the carried pref without
creating a clade absent from the target. The wrong B-A2 case is excluded here. -/
lemma next_attachment_iff (S : Finset Copy) (a next : Copy) (rest : List Copy)
    (hnext : next ∉ S) :
    insert a S ∈ spineClades S (next::rest) ↔ a = next := by
  constructor
  · intro h
    have hn := first_label_in_spineClade S next rest h
    have he : next = a := (Finset.mem_insert.mp hn).resolve_right hnext
    exact he.symm
  · rintro rfl
    exact Finset.mem_insert_self _ _

lemma two_singletons_not_spine (S : Finset Copy) (as : List Copy)
    (b a c : Copy) (hb : b ∈ S) (hba : b ≠ a) (hbc : b ≠ c) :
    ({a,c} : Finset Copy) ∉ spineClades S as := by
  intro h
  have hm := spineClade_contains_start S as h hb
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  exact hm.elim hba hbc

/-- Complete target-clade test for the pref/singleton merger. -/
lemma next_attachment_target_iff (t : Genealogy Copy) (a next : Copy)
    (rest : List Copy) (ha : a ∉ t.leaves) (hn : next ∉ t.leaves) :
    insert a t.leaves ∈ internalClades
      ((next::rest).foldl (fun u z => .graft u (.leaf z)) t) ↔ a = next := by
  rw [fold_internalClades,Finset.mem_union]
  have hnot : insert a t.leaves ∉ internalClades t := by
    intro h
    exact ha (internalClade_subset_leaves h (Finset.mem_insert_self _ _))
  simp only [hnot,false_or]
  exact next_attachment_iff t.leaves a next rest hn

/-- Every pair of remaining singleton labels is incompatible with the target.
The B-containing pref and disjoint singleton leaves are explicit, actual
forest invariants to be supplied at the source use-site. -/
lemma singleton_pair_not_target (t : Genealogy Copy) (as : List Copy)
    (b a c : Copy) (hb : b ∈ t.leaves) (ha : a ∉ t.leaves)
    (hba : b ≠ a) (hbc : b ≠ c) :
    ({a,c} : Finset Copy) ∉ internalClades
      (as.foldl (fun u z => .graft u (.leaf z)) t) := by
  rw [fold_internalClades,Finset.mem_union]
  rintro (h | h)
  · exact ha (internalClade_subset_leaves h (Finset.mem_insert_self _ _))
  · exact two_singletons_not_spine t.leaves as b a c hb hba hbc h

/-- A singleton's live representative is its original label. This uses the
actual forest's leaf fibres, rather than introducing abstract root names. -/
lemma singleton_ancestor_eq (s : State V E Copy) (hs : Valid s) (a : Copy)
    (ha : s.genealogy (s.ancestor a) = .leaf a) : s.ancestor a = a := by
  have hl := hs.ancestor_live a
  have hm := (hs.leaf_fiber (s.ancestor a) hl (s.ancestor a)).mpr
    (hs.representative (s.ancestor a) hl)
  simpa only [ha, Genealogy.leaves, Finset.mem_singleton] using hm

/-- One carried pref and the remaining labelled singletons, covering the
actual original-copy carrier. This is an invariant to establish at each
successful merger, not a hypothesis about the desired event probability. -/
structure CombFrontier (s : State V E Copy) (t : Genealogy Copy)
    (p : Copy) (rest : List Copy) : Prop where
  prefix_live : p ∈ s.live
  prefix_tree : UnorderedEquiv (s.genealogy p) t
  singleton : ∀ a ∈ rest, s.genealogy (s.ancestor a) = .leaf a
  cover : ∀ x, x ∈ t.leaves ∨ x ∈ rest
  disjoint : ∀ a ∈ rest, a ∉ t.leaves
  nodup : rest.Nodup

lemma frontier_singleton_live (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p : Copy) (rest : List Copy)
    (h : CombFrontier s t p rest) {a : Copy} (ha : a ∈ rest) : a ∈ s.live := by
  have he := singleton_ancestor_eq s hs a (h.singleton a ha)
  simpa only [he] using hs.ancestor_live a

lemma frontier_prefix_not_remaining (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p : Copy) (rest : List Copy)
    (h : CombFrontier s t p rest) : p ∉ rest := by
  intro hp
  apply h.disjoint p hp
  rw [← unordered_leaves h.prefix_tree]
  exact (hs.leaf_fiber p h.prefix_live p).mpr (hs.representative p h.prefix_live)

lemma frontier_live_exact (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p : Copy) (rest : List Copy)
    (h : CombFrontier s t p rest) : s.live = insert p rest.toFinset := by
  ext x
  constructor
  · intro hx
    rcases h.cover x with ht | hr
    · have ht' : x ∈ (s.genealogy p).leaves := by
        rw [unordered_leaves h.prefix_tree]
        exact ht
      have he := (hs.leaf_fiber p h.prefix_live x).mp ht'
      have hxp : x = p := (hs.representative x hx).symm.trans he
      exact Finset.mem_insert.mpr (Or.inl hxp)
    · exact Finset.mem_insert.mpr (Or.inr (List.mem_toFinset.mpr hr))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hr
    · exact h.prefix_live
    · exact frontier_singleton_live s hs t p rest h (List.mem_toFinset.mp hr)

lemma frontier_live_card (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p : Copy) (rest : List Copy)
    (h : CombFrontier s t p rest) : s.live.card = rest.length + 1 := by
  rw [frontier_live_exact s hs t p rest h]
  rw [Finset.card_insert_of_notMem]
  · rw [List.toFinset_card_of_nodup h.nodup]
  · simpa only [List.mem_toFinset] using frontier_prefix_not_remaining s hs t p rest h

lemma frontier_singleton_tree (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p : Copy) (rest : List Copy)
    (h : CombFrontier s t p rest) {a : Copy} (ha : a ∈ rest) :
    s.genealogy a = .leaf a := by
  have he := singleton_ancestor_eq s hs a (h.singleton a ha)
  simpa only [he] using h.singleton a ha

/-- First successful ordered orientation: the existing pref representative
survives. This is the original source merger, with its actual live labels. -/
lemma frontier_merge_prefix_survives (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p a : Copy) (rest : List Copy)
    (h : CombFrontier s t p (a :: rest)) :
    CombFrontier (merge s p a) (.graft t (.leaf a)) p rest := by
  have hpnot := frontier_prefix_not_remaining s hs t p (a :: rest) h
  have hpa : p ≠ a := by intro he; apply hpnot; simp [he]
  have hanot : a ∉ rest := (List.nodup_cons.mp h.nodup).1
  have hatree := frontier_singleton_tree s hs t p (a :: rest) h (by simp : a ∈ a :: rest)
  refine ⟨?_, ?_, ?_, ?_, ?_, (List.nodup_cons.mp h.nodup).2⟩
  · exact Finset.mem_erase.mpr ⟨hpa, h.prefix_live⟩
  · simpa only [merge, if_pos rfl, hatree] using
      (UnorderedEquiv.graft h.prefix_tree (UnorderedEquiv.refl (.leaf a)))
  · intro c hc
    have hcfull : c ∈ a :: rest := List.mem_cons_of_mem a hc
    have hca : c ≠ a := by intro he; subst c; exact hanot hc
    have hcp : c ≠ p := by intro he; subst c; exact hpnot hcfull
    have hac := singleton_ancestor_eq s hs c (h.singleton c hcfull)
    have hctree := frontier_singleton_tree s hs t p (a :: rest) h hcfull
    simpa only [merge, hac, if_neg hca, if_neg hcp] using hctree
  · intro x
    rcases h.cover x with hx | hx
    · exact Or.inl (Finset.mem_union.mpr (Or.inl hx))
    · rcases List.mem_cons.mp hx with rfl | hr
      · exact Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self a)))
      · exact Or.inr hr
  · intro c hc
    have hcfull : c ∈ a :: rest := List.mem_cons_of_mem a hc
    have hca : c ≠ a := by intro he; subst c; exact hanot hc
    simpa only [Genealogy.leaves, Finset.mem_union, Finset.mem_singleton,
      not_or] using And.intro (h.disjoint c hcfull) hca

/-- Second successful ordered orientation: the next singleton becomes the
survivor. Only quotient equivalence of the pref is asserted; the Code and
recorded child orientation need not equal those of the first orientation. -/
lemma frontier_merge_singleton_survives (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p a : Copy) (rest : List Copy)
    (h : CombFrontier s t p (a :: rest)) :
    CombFrontier (merge s a p) (.graft t (.leaf a)) a rest := by
  have hpnot := frontier_prefix_not_remaining s hs t p (a :: rest) h
  have hpa : p ≠ a := by intro he; apply hpnot; simp [he]
  have hanot : a ∉ rest := (List.nodup_cons.mp h.nodup).1
  have halive := frontier_singleton_live s hs t p (a :: rest) h (by simp : a ∈ a :: rest)
  have hatree := frontier_singleton_tree s hs t p (a :: rest) h (by simp : a ∈ a :: rest)
  refine ⟨?_, ?_, ?_, ?_, ?_, (List.nodup_cons.mp h.nodup).2⟩
  · exact Finset.mem_erase.mpr ⟨Ne.symm hpa, halive⟩
  · have hg := UnorderedEquiv.graft (UnorderedEquiv.refl (.leaf a)) h.prefix_tree
    have he := UnorderedEquiv.trans hg (UnorderedEquiv.swap (.leaf a) t)
    simpa only [merge, if_pos rfl, hatree] using he
  · intro c hc
    have hcfull : c ∈ a :: rest := List.mem_cons_of_mem a hc
    have hca : c ≠ a := by intro he; subst c; exact hanot hc
    have hcp : c ≠ p := by intro he; subst c; exact hpnot hcfull
    have hac := singleton_ancestor_eq s hs c (h.singleton c hcfull)
    have hctree := frontier_singleton_tree s hs t p (a :: rest) h hcfull
    simpa only [merge, hac, if_neg hcp, if_neg hca] using hctree
  · intro x
    rcases h.cover x with hx | hx
    · exact Or.inl (Finset.mem_union.mpr (Or.inl hx))
    · rcases List.mem_cons.mp hx with rfl | hr
      · exact Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self a)))
      · exact Or.inr hr
  · intro c hc
    have hcfull : c ∈ a :: rest := List.mem_cons_of_mem a hc
    have hca : c ≠ a := by intro he; subst c; exact hanot hc
    simpa only [Genealogy.leaves, Finset.mem_union, Finset.mem_singleton,
      not_or] using And.intro (h.disjoint c hcfull) hca

lemma frontier_live_cases (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p : Copy) (rest : List Copy)
    (h : CombFrontier s t p rest) {x : Copy} (hx : x ∈ s.live) :
    x = p ∨ x ∈ rest := by
  rw [frontier_live_exact s hs t p rest h] at hx
  simpa only [Finset.mem_insert, List.mem_toFinset] using hx

lemma actual_merge_creates_clade (s : State V E Copy) (x y : Copy) :
    (s.genealogy x).leaves ∪ (s.genealogy y).leaves ∈
      internalClades ((merge s x y).genealogy x) := by
  simp only [merge, if_pos rfl, internalClades, Finset.mem_insert_self]

/-- Every actual merger other than the two ordered orientations of the next
prescribed pair creates a clade incompatible with the exact target. This also
rejects the wrong B-spine attachment; no B-free-only shortcut is used. -/
lemma frontier_wrong_merge_clade (s : State V E Copy) (hs : Valid s)
    (t : Genealogy Copy) (p a b : Copy) (rest : List Copy)
    (h : CombFrontier s t p (a :: rest)) (hb : b ∈ t.leaves)
    (x y : Copy) (hx : x ∈ s.live) (hy : y ∈ s.live) (hxy : x ≠ y)
    (hwrong : ¬ ((x = p ∧ y = a) ∨ (x = a ∧ y = p))) :
    ∃ A, A ∈ internalClades ((merge s x y).genealogy x) ∧
      A ∉ internalClades ((a :: rest).foldl (fun u z => .graft u (.leaf z)) t) := by
  refine ⟨(s.genealogy x).leaves ∪ (s.genealogy y).leaves,
    actual_merge_creates_clade s x y, ?_⟩
  have haout := h.disjoint a (by simp : a ∈ a :: rest)
  by_cases hxp : x = p
  · subst x
    have hyp : y ≠ p := Ne.symm hxy
    have hym : y ∈ a :: rest :=
      (frontier_live_cases s hs t p (a :: rest) h hy).resolve_left hyp
    have hytree := frontier_singleton_tree s hs t p (a :: rest) h hym
    have hyout := h.disjoint y hym
    have hya : y ≠ a := by
      intro he
      exact hwrong (Or.inl ⟨rfl,he⟩)
    rw [unordered_leaves h.prefix_tree, hytree, Genealogy.leaves]
    rw [Finset.union_singleton]
    exact fun hc => hya ((next_attachment_target_iff t y a rest hyout haout).mp hc)
  · have hxm : x ∈ a :: rest :=
      (frontier_live_cases s hs t p (a :: rest) h hx).resolve_left hxp
    have hxtree := frontier_singleton_tree s hs t p (a :: rest) h hxm
    by_cases hyp : y = p
    · subst y
      have hxout := h.disjoint x hxm
      have hxa : x ≠ a := by
        intro he
        exact hwrong (Or.inr ⟨he,rfl⟩)
      rw [hxtree, Genealogy.leaves, unordered_leaves h.prefix_tree]
      rw [Finset.singleton_union]
      exact fun hc => hxa ((next_attachment_target_iff t x a rest hxout haout).mp hc)
    · have hym : y ∈ a :: rest :=
        (frontier_live_cases s hs t p (a :: rest) h hy).resolve_left hyp
      have hytree := frontier_singleton_tree s hs t p (a :: rest) h hym
      have hxout := h.disjoint x hxm
      have hyout := h.disjoint y hym
      have hbx : b ≠ x := by intro he; apply hxout; simpa only [← he] using hb
      have hby : b ≠ y := by intro he; apply hyout; simpa only [← he] using hb
      simpa only [hxtree,hytree,Genealogy.leaves,Finset.singleton_union] using
        singleton_pair_not_target t (a :: rest) b x y hb hxout hbx hby

section ActualCompletion
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
variable {X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [Fintype X] [Fintype Copy]

def codeBad (N : RootedBinary V E X) {sample : Copy → X}
    (b x : Copy) (s : Code N sample) : Prop :=
  hasBad b ((state s).genealogy ((state s).ancestor x))

lemma actual_destination_bad (N : RootedBinary V E X) {sample : Copy → X}
    (b x : Copy) (s : Code N sample) (p : Choice N s)
    (h : codeBad N b x s) :
    codeBad N b x (stepDestination N s (some p)) := by
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  let t := merge (state s) p.2.val.1 p.2.val.2
  have ht := merge_source_valid N sample (state s) s.property hm
  change hasBad b ((decodeSnapshot N.root (encodeSnapshot t ht.forest)).genealogy
    (t.ancestor x))
  rw [decode_encode_live_genealogy N.root t ht.forest (ht.forest.ancestor_live x)]
  exact actual_merge_preserves_bad b (state s) p.2.val.1 p.2.val.2 x h

lemma actual_jump_supported_bad (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (b x : Copy) (s d : Code N sample)
    (h : codeBad N b x s) (hd : d ∈ (sourceJumpStep N r s).support) :
    codeBad N b x d := by
  rcases source_jump_support_cases N r s hd with hhold | ⟨p,hp⟩
  · simpa only [hhold.1] using h
  · subst d
    exact actual_destination_bad N b x s p h

/-- Every supported actual completion preserves the carried obstruction;
this is induction on the inherited kernel, not on a replacement path model. -/
lemma actual_completion_supported_bad (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (b x : Copy)
    (fuel : Nat) (s d : Code N sample) (h : codeBad N b x s)
    (hd : d ∈ (ancestralCompletion N r fuel s).support) : codeBad N b x d := by
  induction fuel generalizing s with
  | zero =>
      have he : d = s := by simpa only [ancestralCompletion,PMF.mem_support_pure_iff] using hd
      simpa only [he] using h
  | succ fuel ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih z (actual_jump_supported_bad N r b x s z h hz) hdz

/-- Actual one-tree support joins the originally obstructed copy's ancestor
with B's ancestor. The event is still the specified labelled comb, not the
union of all B-spine shapes. -/
theorem actual_completion_excludes_specified (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (b x : Copy) (as : List Copy)
    (s d : Code N sample) (hroot : AncestralRoot N s)
    (h : codeBad N b x s) (hd : d ∈ (completionKernel N r s).support) :
    ¬ specifiedEvent b as
      (toUnranked ((state d).genealogy ((state d).ancestor b))) := by
  have hc := ancestral_completion_terminal_support N r (Fintype.card Copy)
    s hroot (Finset.card_le_univ s.val.live) hd
  have hb := actual_completion_supported_bad N r b x (Fintype.card Copy) s d h hd
  have he : (state d).ancestor x = (state d).ancestor b :=
    (Finset.card_le_one.mp hc.2) _ (d.property.forest.ancestor_live x)
      _ (d.property.forest.ancestor_live b)
  apply bad_excludes_specified b as
  simpa only [codeBad,he] using hb
/-- A concrete internal clade follows the original copy through the actual
merger, independent of whether it omits B. This also catches wrong B-Aj joins. -/
lemma actual_merge_preserves_clade (A : Finset Copy) (s : State V E Copy)
    (a c x : Copy) (hA : A ∈ internalClades (s.genealogy (s.ancestor x))) :
    A ∈ internalClades ((merge s a c).genealogy ((merge s a c).ancestor x)) := by
  by_cases hx : s.ancestor x = c
  · simp only [merge,hx,if_pos,ite_true,internalClades]
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (by simpa only [hx] using hA))
  · by_cases ha : s.ancestor x = a
    · simp only [merge,if_neg hx,if_pos ha,internalClades]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by simpa only [ha] using hA))
    · simpa only [merge,if_neg hx,if_neg ha] using hA

def codeClade (N : RootedBinary V E X) {sample : Copy → X}
    (A : Finset Copy) (x : Copy) (s : Code N sample) : Prop :=
  A ∈ internalClades ((state s).genealogy ((state s).ancestor x))

lemma actual_destination_clade (N : RootedBinary V E X) {sample : Copy → X}
    (A : Finset Copy) (x : Copy) (s : Code N sample) (p : Choice N s)
    (h : codeClade N A x s) : codeClade N A x (stepDestination N s (some p)) := by
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  let t := merge (state s) p.2.val.1 p.2.val.2
  have ht := merge_source_valid N sample (state s) s.property hm
  change A ∈ internalClades ((decodeSnapshot N.root (encodeSnapshot t ht.forest)).genealogy
    (t.ancestor x))
  rw [decode_encode_live_genealogy N.root t ht.forest (ht.forest.ancestor_live x)]
  exact actual_merge_preserves_clade A (state s) p.2.val.1 p.2.val.2 x h

lemma actual_jump_supported_clade (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (A : Finset Copy) (x : Copy) (s d : Code N sample)
    (h : codeClade N A x s) (hd : d ∈ (sourceJumpStep N r s).support) :
    codeClade N A x d := by
  rcases source_jump_support_cases N r s hd with hhold | ⟨p,hp⟩
  · simpa only [hhold.1] using h
  · subst d
    exact actual_destination_clade N A x s p h

lemma actual_completion_supported_clade (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (A : Finset Copy) (x : Copy)
    (fuel : Nat) (s d : Code N sample) (h : codeClade N A x s)
    (hd : d ∈ (ancestralCompletion N r fuel s).support) : codeClade N A x d := by
  induction fuel generalizing s with
  | zero =>
      have he : d = s := by simpa only [ancestralCompletion,PMF.mem_support_pure_iff] using hd
      simpa only [he] using h
  | succ fuel ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih z (actual_jump_supported_clade N r A x s z h hz) hdz

/-- Any clade absent from the specified labelled target rules out that target
on every actual completion endpoint. In particular the wrong B-A2 first join
is rejected even though its new clade contains B. -/
theorem actual_completion_excludes_wrong_clade (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (b x : Copy) (as : List Copy)
    (s d : Code N sample) (hroot : AncestralRoot N s) (A : Finset Copy)
    (hA : codeClade N A x s) (hwrong : A ∉ internalClades (comb b as))
    (hd : d ∈ (completionKernel N r s).support) :
    ¬ specifiedEvent b as
      (toUnranked ((state d).genealogy ((state d).ancestor b))) := by
  intro hevent
  have hc := ancestral_completion_terminal_support N r (Fintype.card Copy)
    s hroot (Finset.card_le_univ s.val.live) hd
  have hkeep := actual_completion_supported_clade N r A x (Fintype.card Copy) s d hA hd
  have he : (state d).ancestor x = (state d).ancestor b :=
    (Finset.card_le_one.mp hc.2) _ (d.property.forest.ancestor_live x)
      _ (d.property.forest.ancestor_live b)
  have htree : UnorderedEquiv
      ((state d).genealogy ((state d).ancestor b)) (comb b as) :=
    (toUnranked_eq_iff _ _).mp hevent
  apply hwrong
  rw [← internalClades_unordered htree]
  simpa only [codeClade,he] using hkeep

/-- Target-tree version of the support exclusion, needed while the induction
carries an arbitrary already-correct pref tree. -/
theorem actual_completion_excludes_wrong_tree (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (b x : Copy)
    (target : Genealogy Copy) (s d : Code N sample)
    (hroot : AncestralRoot N s) (A : Finset Copy)
    (hA : codeClade N A x s) (hwrong : A ∉ internalClades target)
    (hd : d ∈ (completionKernel N r s).support) :
    toUnranked ((state d).genealogy ((state d).ancestor b)) ≠ toUnranked target := by
  intro hevent
  have hc := ancestral_completion_terminal_support N r (Fintype.card Copy)
    s hroot (Finset.card_le_univ s.val.live) hd
  have hkeep := actual_completion_supported_clade N r A x (Fintype.card Copy) s d hA hd
  have he : (state d).ancestor x = (state d).ancestor b :=
    (Finset.card_le_one.mp hc.2) _ (d.property.forest.ancestor_live x)
      _ (d.property.forest.ancestor_live b)
  have htree := (toUnranked_eq_iff _ _).mp hevent
  apply hwrong
  rw [← internalClades_unordered htree]
  simpa only [codeClade,he] using hkeep

/-- A wrong actual ordered Choice creates the incompatible clade in its
admitted finite snapshot. The representative is live before decoding. -/
lemma actual_wrong_choice_clade (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : Genealogy Copy) (pref next b : Copy)
    (rest : List Copy) (h : CombFrontier (state s) t pref (next :: rest))
    (hb : b ∈ t.leaves) (p : Choice N s)
    (hwrong : ¬ ((p.2.val.1 = pref ∧ p.2.val.2 = next) ∨
      (p.2.val.1 = next ∧ p.2.val.2 = pref))) :
    ∃ A, codeClade N A p.2.val.1 (stepDestination N s (some p)) ∧
      A ∉ internalClades ((next :: rest).foldl (fun u z => .graft u (.leaf z)) t) := by
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  obtain ⟨A,hA,hnot⟩ := frontier_wrong_merge_clade (state s) s.property.forest
    t pref next b rest h hb p.2.val.1 p.2.val.2
    hm.first_live hm.second_live hm.different hwrong
  refine ⟨A,?_,hnot⟩
  let u := merge (state s) p.2.val.1 p.2.val.2
  have hu := merge_source_valid N sample (state s) s.property hm
  have hanc : u.ancestor p.2.val.1 = p.2.val.1 := by
    simp only [u,merge,s.property.forest.representative p.2.val.1 hm.first_live,
      if_neg hm.different]
  change A ∈ internalClades ((decodeSnapshot N.root (encodeSnapshot u hu.forest)).genealogy
    (u.ancestor p.2.val.1))
  rw [decode_encode_live_genealogy N.root u hu.forest
    (hu.forest.ancestor_live p.2.val.1),hanc]
  exact hA

/-- Every completion supported after a wrong actual ordered Choice misses the
specified fold target. Root preservation is supplied by the inherited source
merger theorem, not assumed for the successor. -/
theorem actual_wrong_choice_completion_excluded (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s d : Code N sample)
    (t : Genealogy Copy) (pref next b : Copy) (rest : List Copy)
    (hroot : AncestralRoot N s)
    (h : CombFrontier (state s) t pref (next :: rest)) (hb : b ∈ t.leaves)
    (p : Choice N s)
    (hwrong : ¬ ((p.2.val.1 = pref ∧ p.2.val.2 = next) ∨
      (p.2.val.1 = next ∧ p.2.val.2 = pref)))
    (hd : d ∈ (completionKernel N r (stepDestination N s (some p))).support) :
    toUnranked ((state d).genealogy ((state d).ancestor b)) ≠
      toUnranked ((next :: rest).foldl (fun u z => .graft u (.leaf z)) t) := by
  obtain ⟨A,hA,hnot⟩ := actual_wrong_choice_clade N s t pref next b rest h hb p hwrong
  exact actual_completion_excludes_wrong_tree N r b p.2.val.1 _ _ d
    (ancestral_merger_preserved N s hroot p) A hA hnot hd

/-- Snapshot admission preserves the concrete frontier because every accessed
genealogy is live. Dead-genealogy defaults are never used. -/
lemma admitted_frontier (N : RootedBinary V E X) (sample : Copy → X)
    (u : State V E Copy) (hu : SourceValid N sample u)
    (t : Genealogy Copy) (pref : Copy) (rest : List Copy)
    (h : CombFrontier u t pref rest) :
    CombFrontier (state (admittedCode N sample u hu)) t pref rest := by
  refine ⟨h.prefix_live,?_,?_,h.cover,h.disjoint,h.nodup⟩
  · change UnorderedEquiv
      ((decodeSnapshot N.root (encodeSnapshot u hu.forest)).genealogy pref) t
    rw [decode_encode_live_genealogy N.root u hu.forest h.prefix_live]
    exact h.prefix_tree
  · intro a ha
    change (decodeSnapshot N.root (encodeSnapshot u hu.forest)).genealogy
      (u.ancestor a) = .leaf a
    rw [decode_encode_live_genealogy N.root u hu.forest (hu.forest.ancestor_live a)]
    exact h.singleton a ha

/-- Both successful actual Choices produce the next frontier in the finite
Code. The new representative is the first ordered component, so it can differ
between orientations even though the carried topology agrees. -/
lemma actual_correct_choice_frontier (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : Genealogy Copy) (pref next : Copy)
    (rest : List Copy) (h : CombFrontier (state s) t pref (next :: rest))
    (p : Choice N s)
    (hgood : (p.2.val.1 = pref ∧ p.2.val.2 = next) ∨
      (p.2.val.1 = next ∧ p.2.val.2 = pref)) :
    CombFrontier (state (stepDestination N s (some p)))
      (.graft t (.leaf next)) p.2.val.1 rest := by
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  let u := merge (state s) p.2.val.1 p.2.val.2
  have hu := merge_source_valid N sample (state s) s.property hm
  have hf : CombFrontier u (.graft t (.leaf next)) p.2.val.1 rest := by
    rcases hgood with ⟨hfirst,hsecond⟩ | ⟨hfirst,hsecond⟩
    · simpa only [u,hfirst,hsecond] using
        frontier_merge_prefix_survives (state s) s.property.forest t pref next rest h
    · simpa only [u,hfirst,hsecond] using
        frontier_merge_singleton_survives (state s) s.property.forest t pref next rest h
  exact admitted_frontier N sample u hu (.graft t (.leaf next)) p.2.val.1 rest hf

end ActualCompletion
end DotG34.SpecifiedCombEvent
