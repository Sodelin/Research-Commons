/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual copy of a preserved global unary scalar, concrete binary encoding,
faithful output prefix and cleanup. Reserved global scalar is preserved.
-/
import PolytomyPhysicalBlockCountPrefix

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def copiedBinaryHeaderPrepared (source : CanonicalGlobalPort) (s : CanonicalGlobalStore) :=
  wordDuplicateEval (.inr source) (globalFilterPort .typeIndex) s

def copiedBinaryHeaderEval (source : CanonicalGlobalPort) (s : CanonicalGlobalStore) :=
  binaryPrefixEval (globalFilterPort .typeIndex) (globalFilterPort .output) (copiedBinaryHeaderPrepared source s)

def copiedBinaryHeaderRoutine (source : CanonicalGlobalPort) :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (wordDuplicateRoutine (.inr source) (globalFilterPort .temp) (globalFilterPort .typeIndex))
    (binaryPrefixRoutine (globalFilterPort .typeIndex) (globalFilterPort .temp) (globalFilterPort .output))

theorem copiedBinaryHeader_executes (source : CanonicalGlobalPort) (n : ℕ) (s : CanonicalGlobalStore)
    (hn : s.stk (.inr source) = List.replicate n true)
    (hv : s.stk (globalFilterPort .typeIndex) = []) (ht : s.stk (globalFilterPort .temp) = []) :
    ∃ t ≤ 2 * n ^ 2 + 21 * n + 21,
      (copiedBinaryHeaderRoutine source).Executes s (copiedBinaryHeaderEval source s) t := by
  have he := wordDuplicate_executes (.inr source : CanonicalGlobalStack) (globalFilterPort .temp)
    (globalFilterPort .typeIndex) (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by decide) s ht
  rw [hn, List.length_replicate] at he
  have hv' : (copiedBinaryHeaderPrepared source s).stk (globalFilterPort .typeIndex) = List.replicate n true := by
    simp [copiedBinaryHeaderPrepared, wordDuplicateEval, globalFilterPort, hn, hv]
  have ht' : (copiedBinaryHeaderPrepared source s).stk (globalFilterPort .temp) = [] := by
    simpa [copiedBinaryHeaderPrepared, wordDuplicateEval, globalFilterPort] using ht
  obtain ⟨a, ha, hea⟩ := binaryPrefix_executes (globalFilterPort .typeIndex) (globalFilterPort .temp)
    (globalFilterPort .output) (by decide) (by decide) (by decide) n (copiedBinaryHeaderPrepared source s) hv' ht'
  exact ⟨(3 * n + 3) + a, by omega, RoutineComposition.seq_executes _ _ he hea⟩

theorem copiedBinaryHeader_output (source : CanonicalGlobalPort) (n : ℕ) (s : CanonicalGlobalStore)
    (hn : s.stk (.inr source) = List.replicate n true) (hv : s.stk (globalFilterPort .typeIndex) = []) :
    (copiedBinaryHeaderEval source s).stk (globalFilterPort .output) = binaryNatFrame n ++ s.stk (globalFilterPort .output) := by
  have hv' : (copiedBinaryHeaderPrepared source s).stk (globalFilterPort .typeIndex) = List.replicate n true := by
    simp [copiedBinaryHeaderPrepared, wordDuplicateEval, globalFilterPort, hn, hv]
  rw [binaryPrefix_output _ _ (by decide) n _ hv']
  simp [copiedBinaryHeaderPrepared, wordDuplicateEval, globalFilterPort]

theorem copiedBinaryHeader_type (source : CanonicalGlobalPort) (s : CanonicalGlobalStore) :
    (copiedBinaryHeaderEval source s).stk (globalFilterPort .typeIndex) = [] := binaryPrefix_source _ _ _

theorem copiedBinaryHeader_state (source : CanonicalGlobalPort) (s : CanonicalGlobalStore) :
    (copiedBinaryHeaderEval source s).state = s.state := rfl

theorem copiedBinaryHeader_extra (source : CanonicalGlobalPort) (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (hv : k ≠ globalFilterPort .typeIndex) (ho : k ≠ globalFilterPort .output) :
    (copiedBinaryHeaderEval source s).stk k = s.stk k := by
  rw [binaryPrefix_extra _ _ _ hv ho]
  simp [copiedBinaryHeaderPrepared, wordDuplicateEval, hv]

/- These are actual source copies, not permission to read an arbitrary
mathematical natural in control. The same fixed routine parameter is a
finite global-port selector; N and m headers use their original tapes.
-/

end PolytomyReductionModel
