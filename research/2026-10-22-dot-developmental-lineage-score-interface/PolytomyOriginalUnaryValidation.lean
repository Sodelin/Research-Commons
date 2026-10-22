/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual complete original INTERNAL unary validator routine: first original
syntax/count/range pass creates a physical N counter, then actual complete
coverage replays and unconditional cleanup. Original record is preserved
for the still-open canonical constructor. This is not that constructor.
-/
import PolytomyFirstValidationCleanup

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalUnaryValidationRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  RoutineComposition.seq firstValidationRoutine coverageCleanRoutine

def originalUnaryValidationEval (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  coverageCleanEval (firstValidationEval s)

def originalUnaryValidity (bits : List Bool) : Bool :=
  match readNormalizedSource bits with
  | none => false
  | some R => unaryRangeValid R

def originalUnaryValidationBound (L : ℕ) :=
  17 * L ^ 4 + 44 * L ^ 3 + 63 * L ^ 2 + 90 * L + 55

theorem originalUnaryValidation_verdict (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) :
    (originalUnaryValidationEval s).state.2 = originalUnaryValidity (s.stk (.inr .original)) := by
  obtain ⟨hi, horig, hquery⟩ := firstValidation_ready L s hs hq
  have hflag := firstValidation_verdict L s hs hq
  change (coverageEval (firstValidationEval s)).state.2 = _
  rw [coverage_verdict L _ hi, horig, hflag]
  cases hp : readNormalizedSource (s.stk (.inr .original)) with
  | none => simp [countRangeSpec, originalUnaryValidity, hp]
  | some R =>
      have hN := (validationPrepared_values L s hs R hp).1
      rw [hquery, List.length_replicate, hN, descendingCoverage_range]
      simp only [countRangeSpec, originalUnaryValidity, hp, normalizedMember, unaryRangeValid]

theorem originalUnaryValidity_eq_original (bits : List Bool) :
    originalUnaryValidity bits = match readNormalizedSource bits with
      | none => false
      | some R => scanSourceValid R := by
  cases hp : readNormalizedSource bits with
  | none => simp [originalUnaryValidity, hp]
  | some R => simp [originalUnaryValidity, hp, unaryRangeValid_eq_original]

theorem originalUnaryValidation_executes (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) :
    ∃ n ≤ originalUnaryValidationBound L,
      originalUnaryValidationRoutine.Executes s (originalUnaryValidationEval s) n ∧
      UnaryScanReady 0 L (originalUnaryValidationEval s) ∧
      (originalUnaryValidationEval s).stk (.inr .queries) = [] ∧
      (originalUnaryValidationEval s).stk (.inr .original) = s.stk (.inr .original) ∧
      (originalUnaryValidationEval s).state.2 = originalUnaryValidity (s.stk (.inr .original)) := by
  obtain ⟨n, hn, hfirst⟩ := firstValidation_executes L s hs hq
  obtain ⟨hi, horig, hquery⟩ := firstValidation_ready L s hs hq
  obtain ⟨m, hm, hcover, hready, hclear, hpres, hflag⟩ := coverageClean_executes L (firstValidationEval s) hi
  have hmul := Nat.mul_le_mul_right (descendingQueryStepBound L + 3) hi.2.2
  refine ⟨n + m, ?_, RoutineComposition.seq_executes firstValidationRoutine coverageCleanRoutine hfirst hcover,
    hready, hclear, hpres.trans horig, originalUnaryValidation_verdict L s hs hq⟩
  unfold firstValidationBound descendingQueryStepBound originalUnaryValidationBound at *
  nlinarith

/- The routine now realizes the SAME original normalized-record guard on
ALL input words with fresh scan work, preserving the entire original word
and returning clean scan/query tapes. Empty N, repeated IDs, malformed
headers/rows, count mismatch, out-of-range IDs and trailing suffixes are
included. N=0 cannot bypass the first syntax/count/range pass.

Remaining full claim: original canonical constructor/branches/arithmetic/
target serializer and standalone total downstream machine; independent
target/certificate verifier; compatible closed encoded hardness; all
authorized elaboration, compatibility and transitive axiom audits. This
component is neither a compiled validator certificate nor a whole formal
NP-completeness theorem, and changes no biological/general-DAG scope.
-/

end PolytomyReductionModel
