/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual destructive-second-operand unary product for the ORIGINAL
downstream constructor arithmetic (m*N, alphabet and costs). This
generalizes the already supplied square loop; it is not the constructor.
-/
import PolytomyNormalizerReductionInterface

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def unaryProductRoutine (b d : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  countdownRoutine (.inr d) (copyCapToExtraRoutine b)

theorem unaryProduct_executes (b d : K) (hbd : b ≠ d) (C D L : ℕ)
    (bits : List Bool) (hL : bits.length ≤ L) (base : K → List Bool)
    (hb : base b = []) (hd : base d = List.replicate D true) (frame : F) (guard : Bool) :
    ∃ n ≤ D * (3 * C + 6) + 3,
      (unaryProductRoutine b d).Executes
        (numericStore base (frame, guard) true bits [] (List.replicate C true) [] [])
        (numericStore (Function.update (Function.update base d []) b (List.replicate (C * D) true))
          (frame, false) true bits [] (List.replicate C true) [] []) n := by
  let s := numericStore base (frame, guard) true bits [] (List.replicate C true) [] []
  have hi : NumericLoopInv C L s := by simpa [s, NumericLoopInv, numericStore, numericStacks] using hL
  obtain ⟨n, hn, he, _, _, _⟩ := countdownRoutine_executes (.inr d) (copyCapToExtraRoutine b)
    (copyCapToExtraEval b C) (NumericLoopInv C L) (3 * C + 3) (capSquareContract b d hbd C L) s hi
  have hstate : s = capSquareState b d base frame guard C D bits [] := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> rfl
      | inr k => by_cases hkd : k = d <;> by_cases hkb : k = b <;>
          simp_all [s, capSquareState, numericStore, numericStacks]
  have hlen : (s.stk (.inr d)).length = D := by simp [s, numericStore, numericStacks, hd]
  have hout : countdownEval (.inr d) (copyCapToExtraEval b C) s =
      numericStore (Function.update (Function.update base d []) b (List.replicate (C * D) true))
        (frame, false) true bits [] (List.replicate C true) [] [] := by
    unfold countdownEval
    rw [hlen, hstate, capSquareLoop_effect b d hbd]
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> simp [countdownReset, countdownResetOp, Op.apply, capSquareState, numericStore, numericStacks]
      | inr k => by_cases hkd : k = d <;> by_cases hkb : k = b <;>
          simp_all [countdownReset, countdownResetOp, Op.apply, capSquareState, numericStore, numericStacks, Nat.mul_comm, Ne.symm hbd]
  rw [hout] at he
  rw [hlen] at hn
  exact ⟨n, by omega, he⟩

/- C and D are PHYSICAL unary operands. The active C operand/source and
all extra stacks except b,d survive; d is consumed and b starts empty.
Success=true is required by the existing guarded countdown. Preserving
an original D scalar requires an explicit copy at the caller, not a
theorem-only promise. Downstream parser/validator/control/copy/serializer
and full constructor/checker/hardness/kernel obligations remain open.
-/

end PolytomyReductionModel
