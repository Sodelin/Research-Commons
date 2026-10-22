/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual physical switching between the original small/large source caps.
Three real reversing transfers use a distinct initially empty scratch
port. Both caps are DATA, not natural numbers in finite control. This
does not construct those caps or implement the complete source parser.
-/
import PolytomyFramedRowsParser

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def reverseMoveEval (source target : K) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update (Function.update s.stk source []) target
    ((s.stk source).reverse ++ s.stk target)⟩

theorem frameCallerStore_self (source target : K) (s : CountdownStore K F) :
    frameCallerStore source target s.stk s.state.1 s.state.2 (s.stk source) (s.stk target) = s := by
  apply countdownStore_ext
  · rcases s.state with ⟨f, flag⟩; rfl
  · exact updates_at_own_values s.stk source target

theorem reverseMove_executes (source target : K) (hne : source ≠ target)
    (s : CountdownStore K F) :
    (frameReverseRoutine (F := F × Bool) source target).Executes s
      (reverseMoveEval source target s) ((s.stk source).length + 1) := by
  have h := frameReverse_executes source target hne s.stk s.state.1 s.state.2
    (s.stk source) (s.stk target)
  rw [frameCallerStore_self] at h
  exact h

def capExchangeRoutine (active cached temp : K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (frameReverseRoutine active temp)
    (RoutineComposition.seq (frameReverseRoutine cached active) (frameReverseRoutine temp cached))

def capExchangeEval (active cached temp : K) (s : CountdownStore K F) : CountdownStore K F :=
  reverseMoveEval temp cached (reverseMoveEval cached active (reverseMoveEval active temp s))

/-- General words have an asymmetric exchange: the cached word is
    reversed once, while the active word is reversed twice. Unary caps
    are reversal invariant; no false arbitrary-word swap claim is made. -/
def capExchangeResult (active cached temp : K) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update (Function.update (Function.update s.stk
    active (s.stk cached).reverse) cached (s.stk active)) temp []⟩

theorem capExchange_effect (a b t : K) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (s : CountdownStore K F) (ht : s.stk t = []) :
    capExchangeEval a b t s = capExchangeResult a b t s := by
  apply countdownStore_ext
  · rfl
  · funext k
    by_cases hkT : k = t
    · subst k
      simp [capExchangeEval, capExchangeResult, reverseMoveEval, ht,
        hab, hat, hbt, Ne.symm hab, Ne.symm hat, Ne.symm hbt]
    · by_cases hkB : k = b
      · subst k
        simp [capExchangeEval, capExchangeResult, reverseMoveEval, ht,
          hab, hat, hbt, Ne.symm hab, Ne.symm hat, Ne.symm hbt]
      · by_cases hkA : k = a
        · subst k
          simp [capExchangeEval, capExchangeResult, reverseMoveEval, ht,
            hab, hat, hbt, Ne.symm hab, Ne.symm hat, Ne.symm hbt]
        · simp [capExchangeEval, capExchangeResult, reverseMoveEval, hkA, hkB, hkT]

theorem capExchange_executes (a b t : K) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (s : CountdownStore K F) (ht : s.stk t = []) :
    (capExchangeRoutine a b t).Executes s (capExchangeEval a b t s)
      (2 * (s.stk a).length + (s.stk b).length + 3) := by
  let u := reverseMoveEval a t s
  let v := reverseMoveEval b a u
  have hb : u.stk b = s.stk b := by
    simp [u, reverseMoveEval, Ne.symm hab, hbt]
  have ht' : v.stk t = (s.stk a).reverse := by
    simp [v, u, reverseMoveEval, ht, Ne.symm hat, Ne.symm hbt]
  have h1 := reverseMove_executes a t hat s
  have h2 := reverseMove_executes b a (Ne.symm hab) u
  have h3 := reverseMove_executes t b (Ne.symm hbt) v
  rw [hb] at h2
  rw [ht', List.length_reverse] at h3
  have h23 := RoutineComposition.seq_executes (frameReverseRoutine b a) (frameReverseRoutine t b) h2 h3
  have h123 := RoutineComposition.seq_executes (frameReverseRoutine a t)
    (RoutineComposition.seq (frameReverseRoutine b a) (frameReverseRoutine t b)) h1 h23
  convert h123 using 1 <;> simp only [capExchangeRoutine, capExchangeEval, u, v,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem capExchange_unary_values (a b t : K) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (s : CountdownStore K F) (C D : ℕ) (ha : s.stk a = List.replicate C true)
    (hb : s.stk b = List.replicate D true) (ht : s.stk t = []) :
    (capExchangeEval a b t s).stk a = List.replicate D true ∧
      (capExchangeEval a b t s).stk b = List.replicate C true ∧
      (capExchangeEval a b t s).stk t = [] ∧
      (capExchangeEval a b t s).state = s.state := by
  rw [capExchange_effect a b t hab hat hbt s ht]
  simp [capExchangeResult, ha, hb, hab, hat, hbt, Ne.symm hab]

theorem capExchange_outside (a b t k : K) (hka : k ≠ a) (hkb : k ≠ b) (hkt : k ≠ t)
    (s : CountdownStore K F) :
    (capExchangeEval a b t s).stk k = s.stk k := by
  simp [capExchangeEval, reverseMoveEval, hka, hkb, hkt]

theorem capExchange_unary_executes (a b t : K) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (s : CountdownStore K F) (C D : ℕ) (ha : s.stk a = List.replicate C true)
    (hb : s.stk b = List.replicate D true) (ht : s.stk t = []) :
    (capExchangeRoutine a b t).Executes s (capExchangeEval a b t s) (2 * C + D + 3) ∧
      (capExchangeEval a b t s).stk a = List.replicate D true ∧
      (capExchangeEval a b t s).stk b = List.replicate C true ∧
      (capExchangeEval a b t s).stk t = [] ∧
      (capExchangeEval a b t s).state = s.state := by
  refine ⟨?_, capExchange_unary_values a b t hab hat hbt s C D ha hb ht⟩
  simpa only [ha, hb, List.length_replicate] using capExchange_executes a b t hab hat hbt s ht

/-- Both switching operations have a polynomial DATA-length cost at the
    original caps; this does not supply cap creation or header assembly. -/
theorem original_cap_exchange_total_bound (L : ℕ) :
    (2 * (L + 1) + (L + 1) ^ 2 + 3) +
      (2 * (L + 1) ^ 2 + (L + 1) + 3) =
      3 * (L + 1) ^ 2 + 3 * (L + 1) + 6 := by omega

/- Three distinct ports and an empty scratch port are essential. The code
preserves the entire public control, including a false success flag, and
every outside stack. It can therefore restore the small cap after a failed
large-cap header without reviving parsing. Physical creation of L+1 and
(L+1)^2 from input, exact header/rows composition, full suffix rejection,
final record reversal/tagging/all-path cleanup and whole constructor/
checker/hardness/kernel obligations remain open. No runtime or model change.
-/

end PolytomyReductionModel
