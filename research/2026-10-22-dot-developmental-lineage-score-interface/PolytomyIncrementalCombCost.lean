/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual incremental ORIGINAL fixed-comb cost update for each accepted
canonical leaf. A physical remaining=S-k tape is popped once; its new
unary value is added to the cost only when a previous leaf already exists.
This is used before incrementing the physical accepted-leaf count.
-/
import PolytomyCanonicalLeafWriter

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def combSeenOp (count : K) : Op K Bool (CountdownState F) :=
  .peek count (fun s h => ((s.1.1, h.isSome), s.2))

def combCostStepRoutine (remaining count temp cost : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (countdownPopOp remaining))
    (RoutineComposition.seq (Atom.routine (combSeenOp count))
      (RoutineControl.branch (fun s => s.1.2) (wordDuplicateRoutine remaining temp cost) (Atom.routine cleanupNoop)))

def combCostStepBefore (remaining count : K) (s : CountdownStore K F) :=
  (combSeenOp count).apply (countdownPop remaining s)

def combCostStepEval (remaining count cost : K) (s : CountdownStore K F) :=
  let u := combCostStepBefore remaining count s
  if u.state.1.2 then wordDuplicateEval remaining cost u else u

theorem combCostStep_executes (remaining count temp cost : K)
    (hrt : remaining ≠ temp) (hrc : remaining ≠ cost) (htc : temp ≠ cost)
    (s : CountdownStore K F) (ht : s.stk temp = []) :
    ∃ n ≤ 3 * (s.stk remaining).length + 6,
      (combCostStepRoutine remaining count temp cost).Executes s (combCostStepEval remaining count cost s) n := by
  let u := countdownPop remaining s
  let v := combCostStepBefore remaining count s
  have h1 := Atom.executes (countdownPopOp remaining) s
  have h2 := Atom.executes (combSeenOp count) u
  have htemp : v.stk temp = [] := by
    simp [v, combCostStepBefore, combSeenOp, countdownPop, countdownPopOp, Op.apply, Ne.symm hrt, ht]
  have htail : (v.stk remaining).length ≤ (s.stk remaining).length := by
    change ((countdownPop remaining s).stk remaining).length ≤ _
    rw [countdownPop_counter]
    cases s.stk remaining <;> simp
  cases hf : v.state.1.2 with
  | false =>
      have hbranch := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
        (wordDuplicateRoutine remaining temp cost) (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop v)
      have h23 := RoutineComposition.seq_executes (Atom.routine (combSeenOp count))
        (RoutineControl.branch (fun st => st.1.2) (wordDuplicateRoutine remaining temp cost) (Atom.routine cleanupNoop)) h2 hbranch
      have hall := RoutineComposition.seq_executes (Atom.routine (countdownPopOp remaining))
        (RoutineComposition.seq (Atom.routine (combSeenOp count))
          (RoutineControl.branch (fun st => st.1.2) (wordDuplicateRoutine remaining temp cost) (Atom.routine cleanupNoop))) h1 h23
      exact ⟨4, by omega, by simpa [combCostStepRoutine, combCostStepEval, hf, v, cleanupNoop, Op.apply] using hall⟩
  | true =>
      have hcopy := wordDuplicate_executes remaining temp cost hrt hrc htc v htemp
      have hbranch := RoutineControl.branch_true (fun st : CountdownState F => st.1.2)
        (wordDuplicateRoutine remaining temp cost) (Atom.routine cleanupNoop) hf hcopy
      have h23 := RoutineComposition.seq_executes (Atom.routine (combSeenOp count))
        (RoutineControl.branch (fun st => st.1.2) (wordDuplicateRoutine remaining temp cost) (Atom.routine cleanupNoop)) h2 hbranch
      have hall := RoutineComposition.seq_executes (Atom.routine (countdownPopOp remaining))
        (RoutineComposition.seq (Atom.routine (combSeenOp count))
          (RoutineControl.branch (fun st => st.1.2) (wordDuplicateRoutine remaining temp cost) (Atom.routine cleanupNoop))) h1 h23
      exact ⟨1 + (1 + ((3 * (v.stk remaining).length + 3) + 1)), by omega,
        by simpa only [combCostStepRoutine, combCostStepEval, hf, ↓reduceIte] using hall⟩

theorem combCostStep_remaining (remaining count cost : K) (hrc : remaining ≠ cost)
    (s : CountdownStore K F) : (combCostStepEval remaining count cost s).stk remaining = (s.stk remaining).tail := by
  unfold combCostStepEval
  split <;> simp [wordDuplicateEval, combCostStepBefore, combSeenOp, countdownPop, countdownPopOp, Op.apply, hrc]

theorem combCostStep_cost (remaining count cost : K) (hrc : remaining ≠ cost) (hcount : count ≠ remaining)
    (s : CountdownStore K F) :
    (combCostStepEval remaining count cost s).stk cost =
      if (s.stk count).head?.isSome then (s.stk remaining).tail ++ s.stk cost else s.stk cost := by
  simp [combCostStepEval, combCostStepBefore, combSeenOp, countdownPop, countdownPopOp,
    Op.apply, wordDuplicateEval, hcount, Ne.symm hrc]

theorem combCostStep_extra (remaining count cost k : K) (hkr : k ≠ remaining) (hkc : k ≠ cost)
    (s : CountdownStore K F) : (combCostStepEval remaining count cost s).stk k = s.stk k := by
  unfold combCostStepEval
  split <;> simp [wordDuplicateEval, combCostStepBefore, combSeenOp, countdownPop, countdownPopOp, Op.apply, hkr, hkc]

theorem combCostStep_frame (remaining count cost : K) (s : CountdownStore K F) :
    (combCostStepEval remaining count cost s).state.1.1 = s.state.1.1 ∧
      (combCostStepEval remaining count cost s).state.2 = s.state.2 := by
  unfold combCostStepEval
  split <;> simp [wordDuplicateEval, combCostStepBefore, combSeenOp, countdownPop, countdownPopOp, Op.apply]

theorem combTailCost_snoc (S c n : ℕ) :
    combTailCost S c (n + 1) = combTailCost S c n + (S - (c + n + 1)) := by
  induction n generalizing c with
  | zero => simp [combTailCost]
  | succ n ih =>
      rw [combTailCost, ih, combTailCost]
      have he : c + 1 + n + 1 = c + (n + 1) + 1 := by omega
      rw [he]
      omega

/- Starting remaining=true^S, count=[], the first accepted leaf charges
nothing and leaves remaining=S-1. The next charges S-2, and so on; after
q accepted leaves the total is combTailCost S 1 (q-1). The displayed snoc
identity supplies the cost induction. The accepted-leaf writer/count
increment and descending membership controller must still be composed;
the whole canonical constructor and all kernel checks remain open.
-/

end PolytomyReductionModel
