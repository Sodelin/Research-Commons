/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Store-shaped interface to the ACTUAL operand-preserving multiplier.
It does not posit a new arithmetic machine or put operands in control.
-/
import PolytomyActualEveryOriginalBlock
import PolytomyPreservingUnaryProduct

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem numericStore_snapshot (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : NumericLoopInv C L s) (hf : s.state.2 = true) :
    numericStore (fun k => s.stk (.inr k)) s.state.1 true (s.stk (.inl .source)) []
      (List.replicate C true) [] [] = s := by
  apply countdownStore_ext
  · cases h : s.state with
    | mk a b => simp_all
  · funext k
    cases k with
    | inr k => rfl
    | inl p => cases p <;> simp [numericStore, numericStacks, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1]

def preservingProductStoreEval (b : K) (C D : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  ⟨((s.state.1.1, false), true), Function.update s.stk (.inr b) (List.replicate (C * D) true)⟩

theorem preservingUnaryProduct_store (m t b d : K)
    (hmt : m ≠ t) (hbm : b ≠ m) (hbt : b ≠ t) (hbd : b ≠ d)
    (hdm : d ≠ m) (hdt : d ≠ t) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s) (hf : s.state.2 = true)
    (hm : s.stk (.inr m) = List.replicate D true) (ht : s.stk (.inr t) = [])
    (hb : s.stk (.inr b) = []) (hd : s.stk (.inr d) = []) :
    ∃ n ≤ 3 * C * D + 3 * C + 12 * D + 12,
      (preservingUnaryProductRoutine m t b d).Executes s (preservingProductStoreEval b C D s) n := by
  obtain ⟨n, hn, he⟩ := preservingUnaryProduct_executes m t b d hmt hbm hbt hbd hdm hdt
    C D L (s.stk (.inl .source)) hs.2.2.2.2 (fun k => s.stk (.inr k)) hm ht hb hd
    s.state.1.1 s.state.1.2
  rw [numericStore_snapshot C L s hs hf] at he
  have hout : numericStore (Function.update (fun k => s.stk (.inr k)) b (List.replicate (C * D) true))
      (s.state.1.1, false) true (s.stk (.inl .source)) [] (List.replicate C true) [] [] =
      preservingProductStoreEval b C D s := by
    apply countdownStore_ext
    · rfl
    · funext k
      cases k with
      | inr k => simp [numericStore, numericStacks, preservingProductStoreEval]
      | inl p => cases p <;>
          simp [numericStore, numericStacks, preservingProductStoreEval,
            hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1]
  rw [hout] at he
  exact ⟨n, hn, he⟩

/- Entry operands C,D are tied to the physical cap/cached words.
The output is an exact concrete store update, with operand/source/other
data preserved and cached guard reset. Full source terms are unelaborated.
-/

end PolytomyReductionModel
