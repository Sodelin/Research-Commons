/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual ORIGINAL unary block-count frame m+1: copy physical global m,
push true, push the delimiter on output, faithfully prepend the count,
then clear the count work. The original type/budget word is untouched.
-/
import PolytomyPhysicalBinaryPrefix

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def blockCountPrefix1 (s : CanonicalGlobalStore) :=
  wordDuplicateEval (.inr .rowCount) (globalFilterPort .count) s

def blockCountPrefix2 (s : CanonicalGlobalStore) :=
  (prependBitOp (globalFilterPort .count) true).apply (blockCountPrefix1 s)

def blockCountPrefix3 (s : CanonicalGlobalStore) :=
  (prependBitOp (globalFilterPort .output) false).apply (blockCountPrefix2 s)

def blockCountPrefix4 (s : CanonicalGlobalStore) :=
  wordDuplicateEval (globalFilterPort .count) (globalFilterPort .output) (blockCountPrefix3 s)

def blockCountPrefixEval (s : CanonicalGlobalStore) :=
  clearStackEval (globalFilterPort .count) (blockCountPrefix4 s)

def blockCountPrefixRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (wordDuplicateRoutine (.inr .rowCount) (globalFilterPort .temp) (globalFilterPort .count))
    (RoutineComposition.seq (Atom.routine (prependBitOp (globalFilterPort .count) true))
      (RoutineComposition.seq (Atom.routine (prependBitOp (globalFilterPort .output) false))
        (RoutineComposition.seq (wordDuplicateRoutine (globalFilterPort .count) (globalFilterPort .temp) (globalFilterPort .output))
          (clearStackRoutine (globalFilterPort .count)))))

theorem blockCountPrefix_executes (m : ℕ) (s : CanonicalGlobalStore)
    (hm : s.stk (.inr .rowCount) = List.replicate m true)
    (hc : s.stk (globalFilterPort .count) = []) (ht : s.stk (globalFilterPort .temp) = []) :
    blockCountPrefixRoutine.Executes s (blockCountPrefixEval s) (7 * m + 13) := by
  have h1 := wordDuplicate_executes (.inr CanonicalGlobalPort.rowCount : CanonicalGlobalStack)
    (globalFilterPort .temp) (globalFilterPort .count) (by decide) (by decide) (by decide) s ht
  rw [hm, List.length_replicate] at h1
  have h2 := Atom.executes (prependBitOp (globalFilterPort .count) true) (blockCountPrefix1 s)
  have h3 := Atom.executes (prependBitOp (globalFilterPort .output) false) (blockCountPrefix2 s)
  have ht3 : (blockCountPrefix3 s).stk (globalFilterPort .temp) = [] := by
    simpa [blockCountPrefix3, blockCountPrefix2, blockCountPrefix1, prependBitOp, Op.apply,
      wordDuplicateEval, globalFilterPort] using ht
  have hc3 : (blockCountPrefix3 s).stk (globalFilterPort .count) = List.replicate (m + 1) true := by
    simp [blockCountPrefix3, blockCountPrefix2, blockCountPrefix1, prependBitOp, Op.apply,
      wordDuplicateEval, globalFilterPort, hm, hc, List.replicate_succ]
  have h4 := wordDuplicate_executes (globalFilterPort .count) (globalFilterPort .temp)
    (globalFilterPort .output) (by decide) (by decide) (by decide) (blockCountPrefix3 s) ht3
  rw [hc3, List.length_replicate] at h4
  have hc4 : (blockCountPrefix4 s).stk (globalFilterPort .count) = List.replicate (m + 1) true := by
    simpa [blockCountPrefix4, wordDuplicateEval, globalFilterPort] using hc3
  have h5 := clearStack_executes (globalFilterPort .count) (blockCountPrefix4 s)
  rw [hc4, List.length_replicate] at h5
  have hall := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))
  convert hall using 1 <;> omega

theorem blockCountPrefix_output (m : ℕ) (s : CanonicalGlobalStore)
    (hm : s.stk (.inr .rowCount) = List.replicate m true) (hc : s.stk (globalFilterPort .count) = []) :
    (blockCountPrefixEval s).stk (globalFilterPort .output) = unaryFrame (m + 1) ++ s.stk (globalFilterPort .output) := by
  simp [blockCountPrefixEval, blockCountPrefix4, blockCountPrefix3, blockCountPrefix2,
    blockCountPrefix1, clearStackEval, wordDuplicateEval, prependBitOp, Op.apply, globalFilterPort,
    hm, hc, unaryFrame, List.replicate_succ, List.append_assoc]

theorem blockCountPrefix_count (s : CanonicalGlobalStore) :
    (blockCountPrefixEval s).stk (globalFilterPort .count) = [] := by simp [blockCountPrefixEval, clearStackEval]

theorem blockCountPrefix_state (s : CanonicalGlobalStore) : (blockCountPrefixEval s).state = s.state := rfl

theorem blockCountPrefix_extra (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (hc : k ≠ globalFilterPort .count) (ho : k ≠ globalFilterPort .output) :
    (blockCountPrefixEval s).stk k = s.stk k := by
  simp [blockCountPrefixEval, blockCountPrefix4, blockCountPrefix3, blockCountPrefix2,
    blockCountPrefix1, clearStackEval, wordDuplicateEval, prependBitOp, Op.apply, hc, ho]

/- Physical count preparation and cleanup are included in the exact
7m+13 transition count. This emits the original unaryFrame(m+1), not a
binary replacement. Budget/type and global metadata survive untouched.
-/

end PolytomyReductionModel
