import HardFamilyFullTarget
import Mathlib.Data.Fintype.Card

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

The actual exceptional separator indices: uniqueness for EVERY elementary
action, their exact binomial/exponential count, and literal distinguishing
queries. This does not substitute a one-hot target for the original class.
-/

namespace RestrictedCausal.HardFamily

open CanonicalSelection PartialQueries ProbabilitySource
open scoped BigOperators

theorem Index.ext_before {u : Nat} (q r : Index u)
    («first» : q.first = r.first) (second : q.second = r.second)
    (bits : ∀ x, q.before x = r.before x) : q = r := by
  have pair : q.1 = r.1 := Subtype.ext (Prod.ext «first» second)
  rcases q with ⟨p, f⟩
  rcases r with ⟨p', g⟩
  change p = p' at pair
  subst p'
  have same : f = g := by
    funext x
    have atX := bits x.val
    simpa only [Index.before, Index.first, Index.second, dif_pos x.property] using atX
  subst g
  rfl

theorem tests_index_unique {k u : Nat} (q r : Index u)
    (action : ElementaryAction (Labels k u) Available)
    (qTest : TestsIndex q action) (rTest : TestsIndex r action) : q = r := by
  cases action with
  | invariance t x b => exact qTest.elim
  | ci x y b =>
      have samePair : q.first = r.first ∧ q.second = r.second := by
        rcases qTest.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases rTest.1 with forward | backward
          · exact ⟨Sum.inr.inj forward.1, Sum.inr.inj forward.2⟩
          · have ab := q.1.property
            have ba := r.1.property
            have a := Sum.inr.inj backward.1
            have b := Sum.inr.inj backward.2
            change q.first < q.second at ab
            change r.first < r.second at ba
            rw [← a, ← b] at ba
            exact (lt_asymm ab ba).elim
        · rcases rTest.1 with backward | forward
          · have ab := q.1.property
            have ba := r.1.property
            have a := Sum.inr.inj backward.2
            have b := Sum.inr.inj backward.1
            change q.first < q.second at ab
            change r.first < r.second at ba
            rw [← a, ← b] at ba
            exact (lt_asymm ab ba).elim
          · exact ⟨Sum.inr.inj forward.2, Sum.inr.inj forward.1⟩
      apply Index.ext_before q r samePair.1 samePair.2
      intro z
      apply (bool_eq_iff_truth_iff _ _).mpr
      exact (qTest.2 (.inr z)).symm.trans (rTest.2 (.inr z))

def indexBits {k u : Nat} (q : Index u) : Labels k u → Bool
  | .inl _ => true
  | .inr x => q.before x

theorem indexBits_condition {k u : Nat} (q : Index u) (x : Labels k u) :
    BoolCondition (indexBits q) x ↔ exceptionalCondition q x := by
  cases x <;> simp only [BoolCondition, indexBits, exceptionalCondition, Bool.true_eq_true]

def indexQuery {k u : Nat} (q : Index u) : ElementaryAction (Labels k u) Available :=
  .ci (.inr q.first) (.inr q.second) (indexBits q)

theorem indexQuery_tests {k u : Nat} (q : Index u) : TestsIndex q (indexQuery (k := k) q) :=
  ⟨Or.inl ⟨rfl, rfl⟩, indexBits_condition q⟩

theorem indexQuery_legal {k u : Nat} (q : Index u) : LegalAction Available (indexQuery (k := k) q) :=
  tests_index_legal q _ (indexQuery_tests q)

theorem indexQuery_tests_iff {k u : Nat} (q r : Index u) :
    TestsIndex r (indexQuery (k := k) q) ↔ r = q := by
  constructor
  · intro tested
    exact tests_index_unique r q _ tested (indexQuery_tests q)
  · rintro rfl
    exact indexQuery_tests q

theorem indexQuery_base_false {k u : Nat} (q : Index u) :
    PhysicalSource.physicalResponse Available (physicalSource (k := k) none) (indexQuery q) = false :=
  (physical_tested_index_answers q _ (indexQuery_tests q)).2

theorem indexQuery_response_iff {k u : Nat} (source : Option (Index u)) (q : Index u) :
    PhysicalSource.physicalResponse Available (physicalSource (k := k) source) (indexQuery q) = true ↔
      source = some q := by
  cases source with
  | none => simp only [indexQuery_base_false, Bool.false_eq_true, reduceCtorEq]
  | some r =>
      by_cases same : r = q
      · subst r
        simp only [(physical_tested_index_answers q _ (indexQuery_tests (k := k) q)).1,
          Bool.true_eq_true]
      · have notTested := fun h => same ((indexQuery_tests_iff q r).mp h)
        rw [physical_responses_agree_off_index r _ notTested, indexQuery_base_false]
        simp only [Bool.false_eq_true, Option.some.injEq, same]

theorem outside_pair_card {u : Nat} (p : OrderedPair (Fin u)) :
    Fintype.card {x : Fin u // x ≠ p.val.1 ∧ x ≠ p.val.2} = u - 2 := by
  have distinct : p.val.1 ≠ p.val.2 := ne_of_lt p.property
  calc
    Fintype.card {x : Fin u // x ≠ p.val.1 ∧ x ≠ p.val.2} =
        (Finset.univ \ {p.val.1, p.val.2}).card := by
      apply Fintype.card_of_subtype
      intro x
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
    _ = u - 2 := by
      rw [Finset.card_univ_sdiff]
      simp only [Fintype.card_fin, Finset.card_pair distinct]

theorem index_card (u : Nat) : Fintype.card (Index u) = u.choose 2 * 2 ^ (u - 2) := by
  calc
    Fintype.card (Index u) =
        ∑ p : OrderedPair (Fin u), 2 ^ Fintype.card {x : Fin u // x ≠ p.val.1 ∧ x ≠ p.val.2} := by
      simp only [Index, Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool]
    _ = ∑ _p : OrderedPair (Fin u), 2 ^ (u - 2) := by simp only [outside_pair_card]
    _ = u.choose 2 * 2 ^ (u - 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_orderedPair, Fintype.card_fin]

end RestrictedCausal.HardFamily
