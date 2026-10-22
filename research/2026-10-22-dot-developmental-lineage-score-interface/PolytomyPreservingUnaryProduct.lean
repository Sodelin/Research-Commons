/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual operand-preserving multiplication caller: copy the cached operand
through physical cap switching, restore both operands, then consume only
the fresh counter copy. No input scalar is assumed to survive destruction.
-/
import PolytomyUnarySubtractCaller

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def copySavedCapRoutine (m t d : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (numericCapSwap m t)
    (RoutineComposition.seq (copyCapToExtraRoutine d) (numericCapSwap m t))

def copySavedCapEval (m t d : K) (D : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  numericCapSwapEval m t (copyCapToExtraEval d D (numericCapSwapEval m t s))

theorem copySavedCap_effect (m t d : K) (hmt : m ≠ t) (hdm : d ≠ m) (hdt : d ≠ t)
    (C D : ℕ) (s : CountdownStore (NumericStack K) F)
    (hc : s.stk (.inl .cap) = List.replicate C true)
    (hm : s.stk (.inr m) = List.replicate D true) (ht : s.stk (.inr t) = []) :
    copySavedCapEval m t d D s = copyCapToExtraEval d D s := by
  apply countdownStore_ext
  · rfl
  · funext k
    cases k with
    | inl p => cases p <;>
        simp [copySavedCapEval, numericCapSwapEval, capExchangeEval, reverseMoveEval,
          copyCapToExtraEval, hc, hm, ht, hmt, hdm, hdt, Ne.symm hmt, Ne.symm hdm, Ne.symm hdt]
    | inr k =>
        by_cases hkm : k = m
        · subst k
          simp [copySavedCapEval, numericCapSwapEval, capExchangeEval, reverseMoveEval,
            copyCapToExtraEval, hc, hm, ht, hmt, hdm, hdt, Ne.symm hmt, Ne.symm hdm, Ne.symm hdt]
        · by_cases hkt : k = t
          · subst k
            simp [copySavedCapEval, numericCapSwapEval, capExchangeEval, reverseMoveEval,
              copyCapToExtraEval, hc, hm, ht, hmt, hdm, hdt, Ne.symm hmt, Ne.symm hdm, Ne.symm hdt]
          · by_cases hkd : k = d
            · subst k
              simp [copySavedCapEval, numericCapSwapEval, capExchangeEval, reverseMoveEval,
                copyCapToExtraEval, hc, hm, ht, hmt, hdm, hdt, Ne.symm hmt, Ne.symm hdm, Ne.symm hdt]
            · simp [copySavedCapEval, numericCapSwapEval, capExchangeEval, reverseMoveEval,
                copyCapToExtraEval, hkm, hkt, hkd]

theorem copySavedCap_executes (m t d : K) (hmt : m ≠ t) (hdm : d ≠ m) (hdt : d ≠ t)
    (C D L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s)
    (hm : s.stk (.inr m) = List.replicate D true) (ht : s.stk (.inr t) = []) :
    (copySavedCapRoutine m t d).Executes s (copyCapToExtraEval d D s) (3 * C + 6 * D + 9) := by
  let u := numericCapSwapEval m t s
  obtain ⟨h1, hi1, hm1, ht1⟩ := numericCapSwap_executes m t hmt C D L s hs hm ht
  have h2 := copyCapToExtra_executes d D L u hi1
  let v := copyCapToExtraEval d D u
  have hi2 := copyCapToExtra_invariant d D L u hi1
  have hm2 : v.stk (.inr m) = List.replicate C true := by
    simpa [v, copyCapToExtraEval, Ne.symm hdm] using hm1
  have ht2 : v.stk (.inr t) = [] := by
    simpa [v, copyCapToExtraEval, Ne.symm hdt] using ht1
  obtain ⟨h3, _, _, _⟩ := numericCapSwap_executes m t hmt D C L v hi2 hm2 ht2
  have h23 := RoutineComposition.seq_executes (copyCapToExtraRoutine d) (numericCapSwap m t) h2 h3
  have hall := RoutineComposition.seq_executes (numericCapSwap m t)
    (RoutineComposition.seq (copyCapToExtraRoutine d) (numericCapSwap m t)) h1 h23
  have heff := copySavedCap_effect m t d hmt hdm hdt C D s hs.2.2.2.1 hm ht
  change copySavedCapEval m t d D s = copyCapToExtraEval d D s at heff
  change (copySavedCapRoutine m t d).Executes s (copySavedCapEval m t d D s)
    ((2 * C + D + 3) + ((3 * D + 3) + (2 * D + C + 3))) at hall
  rw [heff] at hall
  convert hall using 1 <;> omega

def preservingUnaryProductRoutine (m t b d : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (copySavedCapRoutine m t d) (unaryProductRoutine b d)

theorem preservingUnaryProduct_executes (m t b d : K)
    (hmt : m ≠ t) (hbm : b ≠ m) (hbt : b ≠ t) (hbd : b ≠ d)
    (hdm : d ≠ m) (hdt : d ≠ t) (C D L : ℕ)
    (bits : List Bool) (hL : bits.length ≤ L) (base : K → List Bool)
    (hm : base m = List.replicate D true) (ht : base t = []) (hb : base b = []) (hd : base d = [])
    (frame : F) (guard : Bool) :
    ∃ n ≤ 3 * C * D + 3 * C + 12 * D + 12,
      (preservingUnaryProductRoutine m t b d).Executes
        (numericStore base (frame, guard) true bits [] (List.replicate C true) [] [])
        (numericStore (Function.update base b (List.replicate (C * D) true))
          (frame, false) true bits [] (List.replicate C true) [] []) n := by
  let s := numericStore base (frame, guard) true bits [] (List.replicate C true) [] []
  let newBase := Function.update base d (List.replicate D true)
  have hi : NumericLoopInv C L s := by simpa [s, NumericLoopInv, numericStore, numericStacks] using hL
  have h1 := copySavedCap_executes m t d hmt hdm hdt C D L s hi hm ht
  have hclone : copyCapToExtraEval d D s =
      numericStore newBase (frame, guard) true bits [] (List.replicate C true) [] [] := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> rfl
      | inr k => by_cases hkd : k = d <;> simp [s, newBase, copyCapToExtraEval, numericStore, numericStacks, hkd, hd]
  rw [hclone] at h1
  have hb' : newBase b = [] := by simp [newBase, hbd, hb]
  have hd' : newBase d = List.replicate D true := by simp [newBase]
  obtain ⟨n, hn, h2⟩ := unaryProduct_executes b d hbd C D L bits hL newBase hb' hd' frame guard
  have hrestore : Function.update (Function.update newBase d []) b (List.replicate (C * D) true) =
      Function.update base b (List.replicate (C * D) true) := by
    funext k
    by_cases hkb : k = b
    · simp [hkb]
    · by_cases hkd : k = d <;> simp [newBase, hkb, hkd, hd]
  rw [hrestore] at h2
  have hall := RoutineComposition.seq_executes (copySavedCapRoutine m t d) (unaryProductRoutine b d) h1 h2
  refine ⟨(3 * C + 6 * D + 9) + n, ?_, hall⟩
  nlinarith

/- Both original operands survive: active cap C and cached m=D. The
distinct fresh product b receives C*D, d returns empty, t returns empty,
numeric work remains empty and unrelated caller data/F survives. The
cached guard resets false; success remains true. This is an actual
caller composition, not an oracle for multiplication or a complete
constructor. Validation, row membership, canonical output, independent
checker, closed hardness and all kernel checks remain to be completed.
-/

end PolytomyReductionModel
