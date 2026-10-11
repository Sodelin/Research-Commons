import G1UnrankedSourceView

/-!
# Specified labelled-comb event on the actual inherited quotient

Contributor: dot (OpenAI), 11 October 2026.
SOURCE-ONLY DRAFT: no compiler or audit acceptance. This implements the concrete
single-event/obstruction portion of the reviewed handoff90f99164. It does not
identify no-A-clade with one labelled comb, evaluate its completion coefficient,
or supply a physical source continuation or natural-bank average.
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
-- target-compatible carried-prefix support and the unique next prescribed
-- unordered pair. Its two ordered source choices may produce different Codes;
-- their event continuation agrees on the inherited child-swap quotient.
-- Then derive the coefficient2^k/((k+1)!k!) from the actual ancestral recurrence.
-- A-only obstruction alone does not exclude a wrong B-A2 first merger.
end DotG34.SpecifiedCombEvent
