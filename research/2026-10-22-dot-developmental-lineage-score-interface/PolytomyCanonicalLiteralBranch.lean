/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Concrete fixed-word output and exhaustive cleanup for the ORIGINAL
yes/no targets. Every literal bit is an actual push; no parameter-driven
serializer or truth oracle is hidden in a one-port Program.call.
-/
import PolytomyGlobalOriginalValidation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def literalPrefixEval (k : K) (bits : List Bool) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update s.stk k (bits ++ s.stk k)⟩

def literalPrefixRoutine (k : K) : List Bool → Routine (fun _ : K => Bool) (CountdownState F)
  | [] => Atom.routine (.load id)
  | b :: bs => RoutineComposition.seq (literalPrefixRoutine k bs) (Atom.routine (prependBitOp k b))

theorem literalPrefix_executes (k : K) (bits : List Bool) (s : CountdownStore K F) :
    (literalPrefixRoutine k bits).Executes s (literalPrefixEval k bits s) (bits.length + 1) := by
  induction bits with
  | nil =>
      have heq : literalPrefixEval k [] s = s := by
        apply countdownStore_ext
        · rfl
        · funext j; by_cases h : j = k <;> simp [literalPrefixEval, h]
      rw [heq]
      exact Atom.executes (.load id) s
  | cons b bs ih =>
      have hpush := Atom.executes (prependBitOp k b) (literalPrefixEval k bs s)
      have hout : (prependBitOp k b).apply (literalPrefixEval k bs s) = literalPrefixEval k (b :: bs) s := by
        apply countdownStore_ext
        · rfl
        · funext j
          by_cases h : j = k
          · subst j; simp [prependBitOp, Op.apply, literalPrefixEval]
          · simp [prependBitOp, Op.apply, literalPrefixEval, h]
      rw [hout] at hpush
      simpa only [List.length_cons, Nat.add_assoc] using
        RoutineComposition.seq_executes _ _ ih hpush

def canonicalLiteralPrepared (bits : List Bool) (s : CanonicalGlobalStore) :=
  literalPrefixEval (globalFilterPort .output) bits (clearStackEval (globalFilterPort .output) s)

def canonicalLiteralRoutine (bits : List Bool) :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (clearStackRoutine (globalFilterPort .output))
    (RoutineComposition.seq (literalPrefixRoutine (globalFilterPort .output) bits) canonicalCleanupRoutine)

theorem canonicalLiteral_output (bits : List Bool) (s : CanonicalGlobalStore) :
    (canonicalLiteralPrepared bits s).stk (globalFilterPort .output) = bits := by
  simp [canonicalLiteralPrepared, literalPrefixEval, clearStackEval]

theorem canonicalLiteral_extra (bits : List Bool) (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (hk : k ≠ globalFilterPort .output) :
    (canonicalLiteralPrepared bits s).stk k = s.stk k := by
  simp [canonicalLiteralPrepared, literalPrefixEval, clearStackEval, hk]

theorem canonicalLiteral_mass (bits : List Bool) (s : CanonicalGlobalStore) :
    cleanupMass canonicalCleanupOwned (canonicalLiteralPrepared bits s) = cleanupMass canonicalCleanupOwned s := by
  simp [cleanupMass, canonicalCleanupOwned, canonicalLiteralPrepared, literalPrefixEval,
    clearStackEval, globalFilterPort, globalScanPort]

theorem canonicalLiteral_executes (bits : List Bool) (s : CanonicalGlobalStore) :
    ∃ n ≤ (s.stk (globalFilterPort .output)).length + bits.length + cleanupMass canonicalCleanupOwned s + 36,
      (canonicalLiteralRoutine bits).Executes s (canonicalCleanStore bits) n := by
  have hclear := clearStack_executes (globalFilterPort .output) s
  have hwrite := literalPrefix_executes (globalFilterPort .output) bits (clearStackEval (globalFilterPort .output) s)
  obtain ⟨n, hn, he⟩ := canonicalCleanup_executes (canonicalLiteralPrepared bits s)
  rw [canonicalLiteral_output] at he
  rw [canonicalLiteral_mass] at hn
  exact ⟨((s.stk (globalFilterPort .output)).length + 1) + ((bits.length + 1) + n), by omega,
    RoutineComposition.seq_executes _ _ hclear (RoutineComposition.seq_executes _ _ hwrite he)⟩

def originalFixedYesBits : List Bool := scanEncodeTarget scanFixedYesTarget
def originalFixedNoBits : List Bool := scanEncodeTarget scanFixedNoTarget
def originalLiteralSize := originalFixedYesBits.length + originalFixedNoBits.length

def originalYesRoutine := canonicalLiteralRoutine originalFixedYesBits
def originalNoRoutine := canonicalLiteralRoutine originalFixedNoBits

/- Only these TWO fixed words are used by the original dispatch. Their
lengths are fixed program constants, not unbounded data or advice. The
routine works from arbitrary public work contents; its stated bound
charges the ACTUAL mass removed and the previous output length. Later
dispatch/invalid-path proofs must supply those mass bounds explicitly.
-/

end PolytomyReductionModel
