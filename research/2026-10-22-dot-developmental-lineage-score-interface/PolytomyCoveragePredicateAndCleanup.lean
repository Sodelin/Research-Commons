/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact bounded coverage predicate for the actual descending loop, plus
unconditional cleanup of an early-failed outer query suffix. The original
first validation pass and physical N-count initialization remain separate.
-/
import PolytomyDescendingCoverageLoop

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem descendingCoverage_true (bits : List Bool) (n : ℕ) :
    descendingCoverage bits n = true ↔ ∀ i < n, normalizedMember i bits = true := by
  induction n with
  | zero => simp [descendingCoverage]
  | succ n ih =>
      rw [descendingCoverage, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hn, hbelow⟩ i hi
        by_cases heq : i = n
        · simpa [heq] using hn
        · exact hbelow i (by omega)
      · intro h
        exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem descendingCoverage_range (bits : List Bool) (n : ℕ) :
    descendingCoverage bits n = (List.range n).all (fun i => normalizedMember i bits) := by
  have he : descendingCoverage bits n = true ↔
      (List.range n).all (fun i => normalizedMember i bits) = true := by
    simpa only [List.all_eq_true, List.mem_range] using descendingCoverage_true bits n
  cases h1 : descendingCoverage bits n <;>
    cases h2 : (List.range n).all (fun i => normalizedMember i bits) <;> simp_all

theorem coverage_original_membership (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : CoverageInv L s)
    (R : RawMSSCRecord) (hp : readNormalizedSource (s.stk (.inr .original)) = some R)
    (hN : (s.stk (.inr .queries)).length = R.N) :
    (coverageEval s).state.2 = s.state.2 &&
      (List.range R.N).all (fun i => decide (i ∈ R.rows.flatten)) := by
  rw [coverage_verdict L s hs, hN, descendingCoverage_range]
  simp only [normalizedMember, hp]

def coverageCleanRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  RoutineComposition.seq coverageRoutine (clearStackRoutine (.inr .queries))

def coverageCleanEval (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  clearStackEval (.inr .queries) (coverageEval s)

theorem coverageClean_executes (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : CoverageInv L s) :
    ∃ n ≤ (s.stk (.inr .queries)).length * (descendingQueryStepBound L + 3) + L + 4,
      coverageCleanRoutine.Executes s (coverageCleanEval s) n ∧
      UnaryScanReady 0 L (coverageCleanEval s) ∧
      (coverageCleanEval s).stk (.inr .queries) = [] ∧
      (coverageCleanEval s).stk (.inr .original) = s.stk (.inr .original) ∧
      (coverageCleanEval s).state.2 = s.state.2 &&
        descendingCoverage (s.stk (.inr .original)) (s.stk (.inr .queries)).length := by
  obtain ⟨n, hn, he, hi, hg, hz⟩ := coverage_executes L s hs
  have hclear := clearStack_executes (.inr .queries : NumericStack UnaryScanPort) (coverageEval s)
  have hall := RoutineComposition.seq_executes coverageRoutine (clearStackRoutine (.inr .queries)) he hclear
  refine ⟨n + ((coverageEval s).stk (.inr .queries)).length + 1, by have hlen := hi.2.2; omega, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hall
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [coverageCleanEval, clearStackEval, NumericLoopInv] using hi.1.numeric
    · simpa [coverageCleanEval, clearStackEval] using hi.1.source_empty
    · intro k hk
      have hkq : k ≠ UnaryScanPort.queries := by cases k <;> simp_all [scanWorkExtras]
      simpa [coverageCleanEval, clearStackEval, hkq] using hi.1.empty k hk
    · simpa [coverageCleanEval, clearStackEval] using hi.1.original_bound
  · simp [coverageCleanEval, clearStackEval]
  · simpa [coverageCleanEval, clearStackEval] using coverage_record_preserved L s hs
  · exact coverage_verdict L s hs

/- All scan tapes and the physical query counter are now clean even on
an early failed coverage check. The original record remains physically
available for the original canonical constructor. Exact incoming-count=N
and successful initial range/count/syntax validation are still needed to
join the original unaryRangeValid predicate, not postulated here.
-/

end PolytomyReductionModel
