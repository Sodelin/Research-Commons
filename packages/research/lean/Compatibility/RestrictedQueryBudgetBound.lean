import RestrictedInteractivePlan
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The original C8 query bound, including the full-coverage endpoint and the
empty observed set. Counts are elementary coordinates, not observations,
statistical samples, intervention regimes, or total enumeration runtime.
-/

namespace RestrictedCausal.PartialQueries

open CanonicalSelection
open scoped BigOperators

universe u

theorem one_le_two_power (n : Nat) : 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem two_power_mono {m n : Nat} (le : m ≤ n) : 2 ^ m ≤ 2 ^ n := by
  induction n generalizing m with
  | zero =>
      have equal : m = 0 := by omega
      subst m
      exact Nat.le_refl _
  | succ n ih =>
      cases m with
      | zero => exact one_le_two_power _
      | succ m =>
          have less : m ≤ n := by omega
          simpa only [pow_succ] using Nat.mul_le_mul_right 2 (ih less)

theorem twice_choose_two (n : Nat) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      cases n with
      | zero => simp
      | succ m =>
          simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one] at ih ⊢
          nlinarith

theorem observed_index_card_bound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    Fintype.card (ObservedIndex T) ≤
      (Fintype.card X).choose 2 * 2 ^ Fintype.card {x : X // ¬ T x} := by
  have subset (p : ObservedPair X) :
      Fintype.card (UntargetedOutsidePair T p.val.1 p.val.2) ≤
        Fintype.card {x : X // ¬ T x} :=
    Fintype.card_subtype_mono _ _ (fun _ member => member.1)
  calc
    Fintype.card (ObservedIndex T) =
        ∑ p : ObservedPair X, 2 ^ Fintype.card (UntargetedOutsidePair T p.val.1 p.val.2) := by
      simp only [ObservedIndex, Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool]
    _ ≤ ∑ _p : ObservedPair X, 2 ^ Fintype.card {x : X // ¬ T x} :=
      Finset.sum_le_sum (fun p _ => two_power_mono (subset p))
    _ = (Fintype.card X).choose 2 * 2 ^ Fintype.card {x : X // ¬ T x} := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      rw [show Fintype.card (ObservedPair X) = (Fintype.card X).choose 2 from card_orderedPair X]

theorem conditional_index_card_bound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    Fintype.card (ConditionalIndex T) ≤
      Fintype.card (MarginalIndex T) * 2 ^ Fintype.card {x : X // ¬ T x} := by
  have subset (q : MarginalIndex T) :
      Fintype.card (UntargetedOutsideEndpoint T q.val.2) ≤
        Fintype.card {x : X // ¬ T x} :=
    Fintype.card_subtype_mono _ _ (fun _ member => member.1)
  calc
    Fintype.card (ConditionalIndex T) =
        ∑ q : MarginalIndex T, 2 ^ Fintype.card (UntargetedOutsideEndpoint T q.val.2) := by
      simp only [ConditionalIndex, Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool]
    _ ≤ ∑ _q : MarginalIndex T, 2 ^ Fintype.card {x : X // ¬ T x} :=
      Finset.sum_le_sum (fun q _ => two_power_mono (subset q))
    _ = Fintype.card (MarginalIndex T) * 2 ^ Fintype.card {x : X // ¬ T x} := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

/-- Valid for every n, including n=0 and n=1, with natural subtraction. -/
theorem coordinate_budget_bound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    2 * coordinateBudget T ≤
      5 * Fintype.card X * (Fintype.card X - 1) * 2 ^ Fintype.card {x : X // ¬ T x} := by
  let n := Fintype.card X
  let u := Fintype.card {x : X // ¬ T x}
  let M := Fintype.card (MarginalIndex T)
  let O := n.choose 2
  have observed := observed_index_card_bound T
  have conditional := conditional_index_card_bound T
  have total : coordinateBudget T ≤ M + O * 2 ^ u + M * 2 ^ u := by
    unfold coordinateBudget
    dsimp [M, O, n, u]
    omega
  have marginal : M ≤ n * (n - 1) := by
    dsimp [M, n]
    rw [marginal_index_card]
    exact Nat.mul_le_mul_right _ (Fintype.card_subtype_le T)
  have scaled := Nat.mul_le_mul_right (2 ^ u) marginal
  have baseScaled := Nat.mul_le_mul_left (n * (n - 1)) (one_le_two_power u)
  have pairs : 2 * O = n * (n - 1) := twice_choose_two n
  have pairsScaled := congrArg (fun z => z * 2 ^ u) pairs
  change 2 * coordinateBudget T ≤ 5 * n * (n - 1) * 2 ^ u
  nlinarith

/-- Full intervention coverage recovers exactly 5 choose(n,2) elementary
queries in this particular policy, including both degenerate endpoints.
This is not a new claim about HPL's prior full-coverage quadratic theorem. -/
theorem coordinate_budget_full_coverage {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (allTargets : ∀ x, T x) :
    coordinateBudget T = 5 * (Fintype.card X).choose 2 := by
  have targets : Fintype.card {x : X // T x} = Fintype.card X :=
    Fintype.card_congr
      { toFun := Subtype.val
        invFun := fun x => ⟨x, allTargets x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have pairEmpty (p : ObservedPair X) :
      Fintype.card (UntargetedOutsidePair T p.val.1 p.val.2) = 0 := by
    letI : IsEmpty (UntargetedOutsidePair T p.val.1 p.val.2) :=
      ⟨fun z => z.property.1 (allTargets z.val)⟩
    exact Fintype.card_eq_zero
  have endpointEmpty (q : MarginalIndex T) :
      Fintype.card (UntargetedOutsideEndpoint T q.val.2) = 0 := by
    letI : IsEmpty (UntargetedOutsideEndpoint T q.val.2) :=
      ⟨fun z => z.property.1 (allTargets z.val)⟩
    exact Fintype.card_eq_zero
  rw [coordinate_budget_exact]
  simp only [pairEmpty, endpointEmpty, pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.mul_one, targets]
  rw [show Fintype.card (ObservedPair X) = (Fintype.card X).choose 2 from card_orderedPair X,
    marginal_index_card, targets]
  have pairs := twice_choose_two (Fintype.card X)
  nlinarith

end RestrictedCausal.PartialQueries
