/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The ORIGINAL complete decision tree, including N=0, m<=1, K<N,
mN<=K and the unchanged canonical branch. Every test is a saved Boolean
produced by the physical classifier. At most four actual branch steps.
-/
import PolytomyOriginalDispatchClassifier

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

def dispatchFound (s : CountdownState SelectedRowFrame) := s.1.1.found
def dispatchChosen (s : CountdownState SelectedRowFrame) := s.1.1.chosen
def dispatchActive (s : CountdownState SelectedRowFrame) := s.1.1.active
def dispatchSuccess (s : CountdownState SelectedRowFrame) := s.2

def originalBudgetDecisionRoutine := RoutineControl.branch dispatchActive originalYesRoutine originalNoRoutine
def originalProductDecisionRoutine := RoutineControl.branch dispatchSuccess originalYesRoutine cleanOriginalCanonicalRoutine
def originalLargeDecisionRoutine := RoutineControl.branch dispatchActive originalProductDecisionRoutine originalNoRoutine
def originalNonemptyDecisionRoutine := RoutineControl.branch dispatchChosen originalBudgetDecisionRoutine originalLargeDecisionRoutine
def originalDispatchChooseRoutine := RoutineControl.branch dispatchFound originalYesRoutine originalNonemptyDecisionRoutine

def originalDispatchChooseBound (L : ℕ) :=
  cleanOriginalCanonicalPolynomial.eval L + originalLiteralSize + L + 40

theorem originalDispatchChoose_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : OriginalConstructorEntry L s)
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R)
    (hzero : dispatchFound s.state = decide (R.N = 0))
    (hsmall : dispatchChosen s.state = decide (R.rows.length ≤ 1))
    (hbudget : dispatchActive s.state = decide (R.N ≤ R.K))
    (hproduct : dispatchSuccess s.state = decide (R.N * R.rows.length ≤ R.K)) :
    ∃ n ≤ originalDispatchChooseBound L,
      originalDispatchChooseRoutine.Executes s (canonicalCleanStore (rawRowMSSCBits R)) n := by
  obtain ⟨yn, hy, hey⟩ := originalEntryLiteral_executes originalFixedYesBits L s hs
  obtain ⟨nn, hn, hen⟩ := originalEntryLiteral_executes originalFixedNoBits L s hs
  obtain ⟨cn, hc, hec⟩ := cleanOriginalCanonical_executes R hR L s hs.scan hs.query_empty
    hs.globals_empty hs.filters_empty hparse
  have hyes : yn + 4 ≤ originalDispatchChooseBound L := by
    unfold originalDispatchChooseBound originalLiteralSize; omega
  have hno : nn + 4 ≤ originalDispatchChooseBound L := by
    unfold originalDispatchChooseBound originalLiteralSize; omega
  have hcanon : cn + 4 ≤ originalDispatchChooseBound L := by
    unfold originalDispatchChooseBound; omega
  by_cases hN : R.N = 0
  · have hz : dispatchFound s.state = true := by rw [hzero]; simp [hN]
    have he := RoutineControl.branch_true dispatchFound originalYesRoutine originalNonemptyDecisionRoutine hz hey
    have hout : rawRowMSSCBits R = originalFixedYesBits := by simp [rawRowMSSCBits, hN, originalFixedYesBits]
    rw [← hout] at he
    exact ⟨yn + 1, by omega, he⟩
  have hz : dispatchFound s.state = false := by rw [hzero]; simp [hN]
  by_cases hm : R.rows.length ≤ 1
  · have hsm : dispatchChosen s.state = true := by rw [hsmall]; simp [hm]
    by_cases hK : R.N ≤ R.K
    · have hb : dispatchActive s.state = true := by rw [hbudget]; simp [hK]
      have h1 := RoutineControl.branch_true dispatchActive originalYesRoutine originalNoRoutine hb hey
      have h2 := RoutineControl.branch_true dispatchChosen originalBudgetDecisionRoutine originalLargeDecisionRoutine hsm h1
      have h3 := RoutineControl.branch_false dispatchFound originalYesRoutine originalNonemptyDecisionRoutine hz h2
      have hout : rawRowMSSCBits R = originalFixedYesBits := by simp [rawRowMSSCBits, hN, hm, hK, originalFixedYesBits]
      rw [← hout] at h3
      exact ⟨(yn + 1) + 1 + 1, by omega, h3⟩
    · have hb : dispatchActive s.state = false := by rw [hbudget]; simp [hK]
      have h1 := RoutineControl.branch_false dispatchActive originalYesRoutine originalNoRoutine hb hen
      have h2 := RoutineControl.branch_true dispatchChosen originalBudgetDecisionRoutine originalLargeDecisionRoutine hsm h1
      have h3 := RoutineControl.branch_false dispatchFound originalYesRoutine originalNonemptyDecisionRoutine hz h2
      have hout : rawRowMSSCBits R = originalFixedNoBits := by simp [rawRowMSSCBits, hN, hm, hK, originalFixedNoBits]
      rw [← hout] at h3
      exact ⟨(nn + 1) + 1 + 1, by omega, h3⟩
  have hsm : dispatchChosen s.state = false := by rw [hsmall]; simp [hm]
  by_cases hK : R.N ≤ R.K
  · have hb : dispatchActive s.state = true := by rw [hbudget]; simp [hK]
    have hKn : ¬ R.K < R.N := by omega
    by_cases hP : R.N * R.rows.length ≤ R.K
    · have hp : dispatchSuccess s.state = true := by rw [hproduct]; simp [hP]
      have hP' : R.rows.length * R.N ≤ R.K := by simpa only [Nat.mul_comm] using hP
      have h1 := RoutineControl.branch_true dispatchSuccess originalYesRoutine cleanOriginalCanonicalRoutine hp hey
      have h2 := RoutineControl.branch_true dispatchActive originalProductDecisionRoutine originalNoRoutine hb h1
      have h3 := RoutineControl.branch_false dispatchChosen originalBudgetDecisionRoutine originalLargeDecisionRoutine hsm h2
      have h4 := RoutineControl.branch_false dispatchFound originalYesRoutine originalNonemptyDecisionRoutine hz h3
      have hout : rawRowMSSCBits R = originalFixedYesBits := by
        simp [rawRowMSSCBits, hN, hm, hKn, hP', originalFixedYesBits]
      rw [← hout] at h4
      exact ⟨((yn + 1) + 1) + 1 + 1, by omega, h4⟩
    · have hp : dispatchSuccess s.state = false := by rw [hproduct]; simp [hP]
      have hP' : ¬ R.rows.length * R.N ≤ R.K := by simpa only [Nat.mul_comm] using hP
      have h1 := RoutineControl.branch_false dispatchSuccess originalYesRoutine cleanOriginalCanonicalRoutine hp hec
      have h2 := RoutineControl.branch_true dispatchActive originalProductDecisionRoutine originalNoRoutine hb h1
      have h3 := RoutineControl.branch_false dispatchChosen originalBudgetDecisionRoutine originalLargeDecisionRoutine hsm h2
      have h4 := RoutineControl.branch_false dispatchFound originalYesRoutine originalNonemptyDecisionRoutine hz h3
      have hout : rawRowMSSCBits R = rawRowCanonicalBits R := by simp [rawRowMSSCBits, hN, hm, hKn, hP']
      rw [← hout] at h4
      exact ⟨((cn + 1) + 1) + 1 + 1, by omega, h4⟩
  · have hb : dispatchActive s.state = false := by rw [hbudget]; simp [hK]
    have hKn : R.K < R.N := by omega
    have h1 := RoutineControl.branch_false dispatchActive originalProductDecisionRoutine originalNoRoutine hb hen
    have h2 := RoutineControl.branch_false dispatchChosen originalBudgetDecisionRoutine originalLargeDecisionRoutine hsm h1
    have h3 := RoutineControl.branch_false dispatchFound originalYesRoutine originalNonemptyDecisionRoutine hz h2
    have hout : rawRowMSSCBits R = originalFixedNoBits := by simp [rawRowMSSCBits, hN, hm, hKn, originalFixedNoBits]
    rw [← hout] at h3
    exact ⟨(nn + 1) + 1 + 1, by omega, h3⟩

def originalValidRecordRoutine := RoutineComposition.seq originalDispatchClassifierRoutine originalDispatchChooseRoutine

def originalValidRecordPolynomial : Polynomial ℕ :=
  cleanOriginalCanonicalPolynomial + 8 * Polynomial.X ^ 2 + 54 * Polynomial.X + Polynomial.C (originalLiteralSize + 132)

theorem originalValidRecordPolynomial_eval (L : ℕ) :
    originalValidRecordPolynomial.eval L = originalDispatchClassifierBound L + originalDispatchChooseBound L := by
  simp [originalValidRecordPolynomial, originalDispatchClassifierBound, originalDispatchChooseBound]
  <;> ring

theorem originalValidRecord_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : OriginalConstructorEntry L s)
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ originalValidRecordPolynomial.eval L,
      originalValidRecordRoutine.Executes s (canonicalCleanStore (rawRowMSSCBits R)) n := by
  obtain ⟨a, ha, hea, hfresh, hp⟩ := originalDispatchClassifier_executes R hR L s hs hparse
  have hparsed : readNormalizedSource ((originalDispatchClassified R s).stk (globalScanPort (.inr .original))) = some R := by
    rw [hp]; exact hparse
  obtain ⟨b, hb, heb⟩ := originalDispatchChoose_executes R hR L (originalDispatchClassified R s) hfresh hparsed
    (by rw [originalDispatchClassified_state]; rfl) (by rw [originalDispatchClassified_state]; rfl)
    (by rw [originalDispatchClassified_state]; rfl) (by rw [originalDispatchClassified_state]; rfl)
  exact ⟨a + b, by rw [originalValidRecordPolynomial_eval]; omega,
    RoutineComposition.seq_executes _ _ hea heb⟩

/- This complete original VALID-record theorem is now source-specified.
No invalid source is admitted by it. The all-word validator/false branch
must still be composed, then packaged as a standalone finite TM2 and
composed with the original normalizer. No compilation/novelty is claimed.
-/

end PolytomyReductionModel
