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
-- target-compatible carried-prefix support and the unique next prescribed
-- unordered pair. Its two ordered source choices may produce different Codes;
-- their event continuation agrees on the inherited child-swap quotient.
-- Then derive the coefficient2^k/((k+1)!k!) from the actual ancestral recurrence.
-- A-only obstruction alone does not exclude a wrong B-A2 first merger.
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
end ActualCompletion
end DotG34.SpecifiedCombEvent
