/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual unary cap squaring: preserve C, make a physical C-counter, repeat
an actual restoring C-copy into an accumulator C times. Nat arithmetic
appears only in the specification, never in finite machine control.
-/
import PolytomyInputLengthCap

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem capReplicate_append (n m : ℕ) :
    List.replicate n true ++ List.replicate m true = List.replicate (n + m) true := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, Nat.succ_add] using congrArg (List.cons true) ih

def copyCapToExtraRoutine (b : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (capCopyRoutine (F := F × Bool))
    (frameReverseRoutine (.inl .work) (.inr b))

def copyCapToExtraEval (b : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  ⟨s.state, Function.update s.stk (.inr b) (List.replicate C true ++ s.stk (.inr b))⟩

theorem copyCapToExtra_executes (b : K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s) :
    (copyCapToExtraRoutine b).Executes s (copyCapToExtraEval b C s) (3 * C + 3) := by
  let u := numericStore (fun k => s.stk (.inr k)) s.state.1 s.state.2
    (s.stk (.inl .source)) [] (List.replicate C true) (List.replicate C true) []
  have h1 := capCopy_executes C (fun k => s.stk (.inr k)) s.state.1 s.state.2
    (s.stk (.inl .source)) [] []
  rw [← numericLoop_reconstruct C L s hs] at h1
  have h2 := reverseMove_executes (.inl .work : NumericStack K) (.inr b) (by simp) u
  have hu : reverseMoveEval (.inl .work) (.inr b) u = copyCapToExtraEval b C s := by
    apply countdownStore_ext
    · rfl
    · funext k
      rcases hs with ⟨hp, hw, ho, hc, hL⟩
      cases k with
      | inl p => cases p <;> simp [u, reverseMoveEval, copyCapToExtraEval, numericStore, numericStacks, hp, hw, ho, hc]
      | inr k => by_cases hk : k = b <;> simp [u, reverseMoveEval, copyCapToExtraEval, numericStore, numericStacks, hk]
  rw [hu] at h2
  have hall := RoutineComposition.seq_executes (capCopyRoutine (F := F × Bool))
    (frameReverseRoutine (.inl .work) (.inr b)) h1 h2
  convert hall using 1 <;> simp [copyCapToExtraRoutine, u, numericStore, numericStacks, Nat.mul_succ, Nat.succ_mul, Nat.add_assoc] <;> omega

theorem copyCapToExtra_invariant (b : K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s) :
    NumericLoopInv C L (copyCapToExtraEval b C s) := by
  simpa [NumericLoopInv, copyCapToExtraEval] using hs

def capSquareContract (b d : K) (hbd : b ≠ d) (C L : ℕ) :
    CountdownContract (.inr d : NumericStack K) (copyCapToExtraRoutine b)
      (copyCapToExtraEval b C) (NumericLoopInv C L) (3 * C + 3) where
  peek_closed s hs := by
    simpa only [NumericLoopInv, countdownPeek, countdownPeekOp, Op.apply] using hs
  pop_closed s hs hg := by
    simpa [NumericLoopInv, countdownPop, countdownPopOp, Op.apply] using hs
  body_closed s hs := copyCapToExtra_invariant b C L s hs
  reset_closed s hs := by
    simpa only [NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
  counter_preserved s hs := by simp [copyCapToExtraEval, Ne.symm hbd]
  body_executes s hs := ⟨3 * C + 3, le_refl _, copyCapToExtra_executes b C L s hs⟩

def capSquareState (b d : K) (base : K → List Bool) (frame : F) (guard : Bool)
    (C n : ℕ) (bits acc : List Bool) : CountdownStore (NumericStack K) F :=
  numericStore (Function.update (Function.update base b acc) d (List.replicate n true))
    (frame, guard) true bits [] (List.replicate C true) [] []

theorem capSquareLoop_effect (b d : K) (hbd : b ≠ d) (base : K → List Bool)
    (frame : F) (C : ℕ) (bits : List Bool) (n : ℕ) : ∀ acc guard,
    countdownLoopEval (.inr d) (copyCapToExtraEval b C) n
      (countdownPeek (.inr d) (capSquareState b d base frame guard C n bits acc)) =
    capSquareState b d base frame false C 0 bits (List.replicate (n * C) true ++ acc) := by
  induction n with
  | zero =>
      intro acc guard
      apply countdownStore_ext
      · simp [countdownLoopEval, countdownPeek, countdownPeekOp, Op.apply, capSquareState, numericStore, numericStacks]
      · simp [countdownLoopEval, countdownPeek, countdownPeekOp, Op.apply, capSquareState, numericStore]
  | succ n ih =>
      intro acc guard
      let s := capSquareState b d base frame guard C (n + 1) bits acc
      have hg : countdownGuard (countdownPeek (.inr d) s).state = true := by
        simp [s, countdownGuard, countdownPeek, countdownPeekOp, Op.apply,
          capSquareState, numericStore, numericStacks, List.replicate_succ]
      have hstep : countdownPeek (.inr d)
          (copyCapToExtraEval b C (countdownPop (.inr d) (countdownPeek (.inr d) s))) =
          countdownPeek (.inr d) (capSquareState b d base frame true C n bits (List.replicate C true ++ acc)) := by
        apply countdownStore_ext
        · simp [s, countdownPeek, countdownPeekOp, countdownPop, countdownPopOp, Op.apply,
            copyCapToExtraEval, capSquareState, numericStore, numericStacks, hbd, Ne.symm hbd, List.replicate_succ]
        · funext k
          cases k with
          | inl p => cases p <;> simp [s, countdownPeek, countdownPeekOp, countdownPop, countdownPopOp,
              Op.apply, copyCapToExtraEval, capSquareState, numericStore, numericStacks]
          | inr k =>
              by_cases hkd : k = d
              · subst k; simp [s, countdownPeek, countdownPeekOp, countdownPop, countdownPopOp,
                  Op.apply, copyCapToExtraEval, capSquareState, numericStore, numericStacks, hbd, Ne.symm hbd, List.replicate_succ]
              · by_cases hkb : k = b
                · subst k; simp [s, countdownPeek, countdownPeekOp, countdownPop, countdownPopOp,
                    Op.apply, copyCapToExtraEval, capSquareState, numericStore, numericStacks, hbd, Ne.symm hbd]
                · simp [s, countdownPeek, countdownPeekOp, countdownPop, countdownPopOp,
                    Op.apply, copyCapToExtraEval, capSquareState, numericStore, numericStacks, hkd, hkb]
      change countdownLoopEval (.inr d) (copyCapToExtraEval b C) (n + 1) (countdownPeek (.inr d) s) = _
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      rw [hstep, ih]
      have hwords : List.replicate (n * C) true ++ (List.replicate C true ++ acc) =
          List.replicate ((n + 1) * C) true ++ acc := by
        rw [← List.append_assoc, capReplicate_append]
        have ha : n * C + C = (n + 1) * C := by ring
        rw [ha]
      rw [hwords]

def capSquareRoutine (b d : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (copyCapToExtraRoutine d)
    (countdownRoutine (.inr d) (copyCapToExtraRoutine b))

theorem capSquare_executes (b d : K) (hbd : b ≠ d) (C L : ℕ)
    (bits : List Bool) (hL : bits.length ≤ L) (base : K → List Bool)
    (hb : base b = []) (hd : base d = []) (frame : F) (guard : Bool) :
    ∃ n ≤ 3 * C ^ 2 + 9 * C + 6,
      (capSquareRoutine b d).Executes
        (numericStore base (frame, guard) true bits [] (List.replicate C true) [] [])
        (numericStore (Function.update base b (List.replicate (C ^ 2) true))
          (frame, false) true bits [] (List.replicate C true) [] []) n := by
  let s := numericStore base (frame, guard) true bits [] (List.replicate C true) [] []
  let u := copyCapToExtraEval d C s
  have hi : NumericLoopInv C L s := by simpa [s, NumericLoopInv, numericStore, numericStacks] using hL
  have h1 := copyCapToExtra_executes d C L s hi
  have hiu := copyCapToExtra_invariant d C L s hi
  obtain ⟨n, hn, h2, _, _, _⟩ := countdownRoutine_executes (.inr d) (copyCapToExtraRoutine b)
    (copyCapToExtraEval b C) (NumericLoopInv C L) (3 * C + 3) (capSquareContract b d hbd C L) u hiu
  have hu : u = capSquareState b d base frame guard C C bits [] := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> simp [u, s, copyCapToExtraEval, capSquareState, numericStore, numericStacks]
      | inr k => by_cases hkd : k = d <;> by_cases hkb : k = b <;>
          simp_all [u, s, copyCapToExtraEval, capSquareState, numericStore, numericStacks]
  have huLen : (u.stk (.inr d)).length = C := by simp [u, s, copyCapToExtraEval, numericStore, numericStacks, hd]
  have hout : countdownEval (.inr d) (copyCapToExtraEval b C) u =
      numericStore (Function.update base b (List.replicate (C ^ 2) true))
        (frame, false) true bits [] (List.replicate C true) [] [] := by
    unfold countdownEval
    rw [huLen, hu, capSquareLoop_effect b d hbd]
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> simp [countdownReset, countdownResetOp, Op.apply, capSquareState, numericStore, numericStacks]
      | inr k => by_cases hkd : k = d <;>
          simp_all [countdownReset, countdownResetOp, Op.apply, capSquareState, numericStore, numericStacks, pow_two, Ne.symm hbd]
  rw [hout] at h2
  have hall := RoutineComposition.seq_executes (copyCapToExtraRoutine d)
    (countdownRoutine (.inr d) (copyCapToExtraRoutine b)) h1 h2
  refine ⟨(3 * C + 3) + n, ?_, hall⟩
  rw [huLen] at hn
  nlinarith

/- Both extra counter d and accumulator b start empty and are distinct.
Success=true is required by the existing failure-guarded countdown; the
whole cap-preparation entry must set it explicitly. Output preserves C,
source, other stacks and F, leaves d empty, puts C^2 in b and resets only
the cached guard. Full cap-preparation/prefix and complete-input finish,
cleanup, downstream constructor/checker/hardness/kernel still follow.
-/

end PolytomyReductionModel
