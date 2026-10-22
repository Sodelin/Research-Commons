/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual complete bounded coverage loop, with a supplied physical unary
query count. The body copies the remaining count and queries it, giving
N-1,...,0 without an unbounded control register. Initial count creation
from the parsed original N and the range/count-validation join remain.
-/
import PolytomyDescendingMembershipQuery

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def CoverageInv (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool) : Prop :=
  UnaryScanReady 0 L s ∧ IsUnaryWord (s.stk (.inr .queries)) ∧ (s.stk (.inr .queries)).length ≤ L

def descendingMembershipEval (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  descendingQueryEval (s.stk (.inr .queries)).length s

theorem coveragePeek_closed (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : CoverageInv L s) : CoverageInv L (countdownPeek (.inr .queries) s) :=
  ⟨⟨hs.1.numeric, hs.1.source_empty, hs.1.empty, hs.1.original_bound⟩, hs.2⟩

theorem coveragePop_closed (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : CoverageInv L s) : CoverageInv L (countdownPop (.inr .queries) s) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simpa [NumericLoopInv, countdownPop, countdownPopOp, Op.apply] using hs.1.numeric
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.1.source_empty
  · intro k hk
    have hkq : k ≠ UnaryScanPort.queries := by cases k <;> simp_all [scanWorkExtras]
    simpa [countdownPop, countdownPopOp, Op.apply, hkq] using hs.1.empty k hk
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.1.original_bound
  · rw [countdownPop_counter, hs.2.1]
    simp [IsUnaryWord]
  · rw [countdownPop_counter]
    have ht : (s.stk (.inr .queries)).tail.length ≤ (s.stk (.inr .queries)).length := by
      cases s.stk (.inr .queries) <;> simp
    exact ht.trans hs.2.2

def coverageContract (L : ℕ) : CountdownContract (.inr .queries) descendingQueryRoutine
    descendingMembershipEval (CoverageInv L) (descendingQueryStepBound L) where
  peek_closed := coveragePeek_closed L
  pop_closed s hs _ := coveragePop_closed L s hs
  body_closed s hs := by
    have hready := descendingQuery_ready (s.stk (.inr .queries)).length L s hs.1 hs.2.1
    have hpres := (descendingQuery_preserves (s.stk (.inr .queries)).length L s hs.1 hs.2.1).2
    refine ⟨hready, ?_, ?_⟩
    · simpa only [descendingMembershipEval, hpres] using hs.2.1
    · simpa only [descendingMembershipEval, hpres] using hs.2.2
  reset_closed s hs := ⟨⟨hs.1.numeric, hs.1.source_empty, hs.1.empty, hs.1.original_bound⟩, hs.2⟩
  counter_preserved s hs := (descendingQuery_preserves (s.stk (.inr .queries)).length L s hs.1 hs.2.1).2
  body_executes s hs := descendingQuery_executes (s.stk (.inr .queries)).length L hs.2.2 s hs.1 hs.2.1

def coverageRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  countdownRoutine (.inr .queries) descendingQueryRoutine

def coverageEval (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  countdownEval (.inr .queries) descendingMembershipEval s

theorem coverage_executes (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : CoverageInv L s) :
    ∃ n ≤ (s.stk (.inr .queries)).length * (descendingQueryStepBound L + 3) + 3,
      coverageRoutine.Executes s (coverageEval s) n ∧ CoverageInv L (coverageEval s) ∧
      (coverageEval s).state.1.2 = false ∧
      ((coverageEval s).state.2 = true → (coverageEval s).stk (.inr .queries) = []) := by
  exact countdownRoutine_executes (.inr .queries) descendingQueryRoutine descendingMembershipEval
    (CoverageInv L) (descendingQueryStepBound L) (coverageContract L) s hs

def descendingCoverage (bits : List Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => normalizedMember n bits && descendingCoverage bits n

theorem coverageLoop_verdict (L n : ℕ) :
    ∀ s : CountdownStore (NumericStack UnaryScanPort) Bool, CoverageInv L s →
      (s.stk (.inr .queries)).length = n →
      (countdownLoopEval (.inr .queries) descendingMembershipEval n
        (countdownPeek (.inr .queries) s)).state.2 =
        s.state.2 && descendingCoverage (s.stk (.inr .original)) n := by
  induction n with
  | zero => intro s hs hlen; simp [countdownLoopEval, countdownPeek, countdownPeekOp, Op.apply, descendingCoverage]
  | succ n ih =>
      intro s hs hlen
      cases hf : s.state.2 with
      | false =>
          rw [countdownLoop_failed (.inr .queries) descendingMembershipEval (n + 1)
            (countdownPeek (.inr .queries) s) hf]
          simp [countdownPeek, countdownPeekOp, Op.apply, hf]
      | true =>
          have hhead : (s.stk (.inr .queries)).head?.isSome = true := by
            cases hw : s.stk (.inr .queries) with
            | nil => simp [hw] at hlen
            | cons b xs => rfl
          have hg : countdownGuard (countdownPeek (.inr .queries) s).state = true := by
            simp [countdownGuard, countdownPeek, countdownPeekOp, Op.apply, hf, hhead]
          let p := countdownPop (.inr .queries) (countdownPeek (.inr .queries) s)
          have hp : CoverageInv L p := coveragePop_closed L _ (coveragePeek_closed L s hs)
          have hpn : (p.stk (.inr .queries)).length = n := by
            change ((countdownPop (.inr .queries) (countdownPeek (.inr .queries) s)).stk (.inr .queries)).length = n
            rw [countdownPop_counter]
            change (s.stk (.inr .queries)).tail.length = n
            cases hw : s.stk (.inr .queries) with
            | nil => simp [hw] at hlen
            | cons b xs => simp only [hw, List.length_cons] at hlen; simp only [List.tail_cons]; omega
          have hpword : p.stk (.inr .queries) = List.replicate n true := by simpa only [hpn] using hp.2.1
          let u := descendingMembershipEval p
          have hu : CoverageInv L u := (coverageContract L).body_closed p hp
          have hquery : u.stk (.inr .queries) = p.stk (.inr .queries) := (coverageContract L).counter_preserved p hp
          have hrecord : u.stk (.inr .original) = s.stk (.inr .original) := by
            have h := (descendingQuery_preserves n L p hp.1 hpword).1
            simpa [u, descendingMembershipEval, hpn, p, countdownPop, countdownPopOp,
              countdownPeek, countdownPeekOp, Op.apply] using h
          have hbody : u.state.2 = normalizedMember n (s.stk (.inr .original)) := by
            have h := descendingQuery_verdict n L p hp.1 hpword
            simpa [u, descendingMembershipEval, hpn, p, countdownPop, countdownPopOp,
              countdownPeek, countdownPeekOp, Op.apply] using h
          have hi := ih u hu (by rw [hquery]; exact hpn)
          rw [countdownLoopEval, hg]
          simp only [↓reduceIte]
          change (countdownLoopEval (.inr .queries) descendingMembershipEval n (countdownPeek (.inr .queries) u)).state.2 = _
          simpa only [hbody, hrecord, descendingCoverage, hf, Bool.true_and] using hi

theorem coverage_verdict (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : CoverageInv L s) :
    (coverageEval s).state.2 = s.state.2 &&
      descendingCoverage (s.stk (.inr .original)) (s.stk (.inr .queries)).length :=
  coverageLoop_verdict L (s.stk (.inr .queries)).length s hs rfl

theorem coverage_record_preserved (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : CoverageInv L s) : (coverageEval s).stk (.inr .original) = s.stk (.inr .original) := by
  exact countdownLoop_preserves_on (.inr .queries) descendingQueryRoutine descendingMembershipEval
    (CoverageInv L) (descendingQueryStepBound L) (coverageContract L) (fun t => t.stk (.inr .original))
    (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply])
    (fun t ht => (descendingQuery_preserves (t.stk (.inr .queries)).length L t ht.1 ht.2.1).1)
    (s.stk (.inr .queries)).length (countdownPeek (.inr .queries) s) (coveragePeek_closed L s hs)

/- Early failure leaves only a bounded query-counter suffix; every actual
body has already cleared all its own scan tapes. N=0 gives the vacuous
conjunction, so whole-record syntax/range/count must be checked separately
and preserved in the incoming success flag. This loop alone is not the
original validity predicate. Count creation and the first validation pass
remain necessary before a whole-machine or whole-constructor claim.
-/

end PolytomyReductionModel
