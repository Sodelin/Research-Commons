/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actually encode a unary source counter with the ORIGINAL binary frame,
faithfully prepend that frame, then really clear the source. Foreign
caller words/control and the initially empty restoring temporary survive.
-/
import PolytomyPhysicalCanonicalBudget

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def binaryPrefixRoutine (value temp output : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (binaryCounterCallerRoutine value)
    (RoutineComposition.seq (wordDuplicateRoutine value temp output) (clearStackRoutine value))

def binaryPrefixEval (value output : K) (s : CountdownStore K F) :=
  clearStackEval value (wordDuplicateEval value output (binaryCounterCallerEval value s))

theorem binaryPrefix_executes (value temp output : K) (hvt : value ≠ temp) (hvo : value ≠ output)
    (hto : temp ≠ output) (n : ℕ) (s : CountdownStore K F)
    (hv : s.stk value = List.replicate n true) (ht : s.stk temp = []) :
    ∃ t ≤ 2 * n ^ 2 + 18 * n + 18,
      (binaryPrefixRoutine value temp output).Executes s (binaryPrefixEval value output s) t := by
  obtain ⟨a, ha, he⟩ := binaryCounterCaller_executes value s
  rw [hv, List.length_replicate] at ha
  have ht' : (binaryCounterCallerEval value s).stk temp = [] := by
    rw [binaryCounterCaller_extra value temp (Ne.symm hvt)]; exact ht
  have hv' : (binaryCounterCallerEval value s).stk value = binaryNatFrame n := by
    rw [binaryCounterCaller_value, hv, List.length_replicate]
  have hcopy := wordDuplicate_executes value temp output hvt hvo hto (binaryCounterCallerEval value s) ht'
  rw [hv'] at hcopy
  have hsource : (wordDuplicateEval value output (binaryCounterCallerEval value s)).stk value = binaryNatFrame n := by
    simpa [wordDuplicateEval, hvo] using hv'
  have hclear := clearStack_executes value (wordDuplicateEval value output (binaryCounterCallerEval value s))
  rw [hsource] at hclear
  have hall := RoutineComposition.seq_executes _ _ he (RoutineComposition.seq_executes _ _ hcopy hclear)
  have hlength : (binaryNatFrame n).length ≤ 2 * n + 1 := by
    have hb := binaryBits_length_le n
    simp only [binaryNatFrame, unaryFrame, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  exact ⟨a + ((3 * (binaryNatFrame n).length + 3) + ((binaryNatFrame n).length + 1)), by omega, hall⟩

theorem binaryPrefix_output (value output : K) (hvo : value ≠ output) (n : ℕ)
    (s : CountdownStore K F) (hv : s.stk value = List.replicate n true) :
    (binaryPrefixEval value output s).stk output = binaryNatFrame n ++ s.stk output := by
  simp [binaryPrefixEval, clearStackEval, wordDuplicateEval, binaryCounterCallerEval,
    binaryCounterCallerStore, hvo, Ne.symm hvo, hv]

theorem binaryPrefix_source (value output : K) (s : CountdownStore K F) :
    (binaryPrefixEval value output s).stk value = [] := by simp [binaryPrefixEval, clearStackEval]

theorem binaryPrefix_state (value output : K) (s : CountdownStore K F) :
    (binaryPrefixEval value output s).state = s.state := rfl

theorem binaryPrefix_extra (value output k : K) (hkv : k ≠ value) (hko : k ≠ output)
    (s : CountdownStore K F) : (binaryPrefixEval value output s).stk k = s.stk k := by
  simp [binaryPrefixEval, clearStackEval, wordDuplicateEval, binaryCounterCallerEval,
    binaryCounterCallerStore, hkv, hko]

/- The emitted word is the ORIGINAL binaryNatFrame n, not a unary-only
replacement or a free serialization oracle. Copy and clearing costs are
included. Caller data/control survive through the genuine embedding.
Full original header ordering/cases/standalone/verifier/hardness/kernel
obligations remain, with no execution or compilation claimed.
-/

end PolytomyReductionModel
