/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Complete actual ORIGINAL header sequence: budget C0+K-N, unary block
count, then binary budget/m/N prefixes in reverse execution order.
Every physical operand, copy, encoder call and cleanup is included.
-/
import PolytomyCopiedBinaryHeader

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalTargetBudget (R : RawMSSCRecord) := rawRowFixedCost R + R.K - R.N

def originalHeaderPrefix (R : RawMSSCRecord) : List Bool :=
  binaryNatFrame R.N ++ binaryNatFrame R.rows.length ++ binaryNatFrame (originalTargetBudget R) ++
    unaryFrame (R.rows.length + 1)

def canonicalHeaderBudget (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  canonicalBudgetEval (rawRowFixedCost R) R.K R.N s

def canonicalHeaderCount (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  blockCountPrefixEval (canonicalHeaderBudget R s)

def canonicalHeaderTarget (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  binaryPrefixEval (globalFilterPort .typeIndex) (globalFilterPort .output) (canonicalHeaderCount R s)

def canonicalHeaderRows (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  copiedBinaryHeaderEval .rowCount (canonicalHeaderTarget R s)

def canonicalHeadersEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  copiedBinaryHeaderEval .universe (canonicalHeaderRows R s)

def canonicalHeadersRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq canonicalBudgetRoutine
    (RoutineComposition.seq blockCountPrefixRoutine
      (RoutineComposition.seq (binaryPrefixRoutine (globalFilterPort .typeIndex) (globalFilterPort .temp) (globalFilterPort .output))
        (RoutineComposition.seq (copiedBinaryHeaderRoutine .rowCount) (copiedBinaryHeaderRoutine .universe))))

def canonicalHeadersBound (R : RawMSSCRecord) :=
  (3 * rawRowFixedCost R + 3 * R.K + 4 * R.N + 11) +
    (7 * R.rows.length + 13) +
    (2 * originalTargetBudget R ^ 2 + 18 * originalTargetBudget R + 18) +
    (2 * R.rows.length ^ 2 + 21 * R.rows.length + 21) +
    (2 * R.N ^ 2 + 21 * R.N + 21)

theorem canonicalHeaders_executes (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s)
    (hcost : s.stk (globalFilterPort .cost) = List.replicate (rawRowFixedCost R) true) :
    ∃ n ≤ canonicalHeadersBound R,
      canonicalHeadersRoutine.Executes s (canonicalHeadersEval R s) n ∧
      (canonicalHeadersEval R s).stk (globalFilterPort .output) =
        originalHeaderPrefix R ++ s.stk (globalFilterPort .output) := by
  let b := canonicalHeaderBudget R s
  let c := canonicalHeaderCount R s
  let t := canonicalHeaderTarget R s
  let r := canonicalHeaderRows R s
  have h0 := canonicalBudget_executes (rawRowFixedCost R) R.K R.N s hcost hs.budget hs.universe
    hs.type_empty hs.remaining_empty hs.temp_empty
  have bg : ∀ k : CanonicalGlobalPort, b.stk (.inr k) = s.stk (.inr k) := by
    intro k
    exact canonicalBudget_extra _ _ _ s _ (by simp [globalFilterPort]) (by simp [globalFilterPort])
  have hbc : b.stk (globalFilterPort .count) = [] := by
    rw [canonicalBudget_extra _ _ _ _ _ (by decide) (by decide)]; exact hs.count_empty
  have hbt : b.stk (globalFilterPort .temp) = [] := by
    rw [canonicalBudget_extra _ _ _ _ _ (by decide) (by decide)]; exact hs.temp_empty
  have hbm : b.stk (.inr .rowCount) = List.replicate R.rows.length true := by rw [bg]; exact hs.rows
  have h1 := blockCountPrefix_executes R.rows.length b hbm hbc hbt
  have cg : ∀ k : CanonicalGlobalPort, c.stk (.inr k) = s.stk (.inr k) := by
    intro k; rw [blockCountPrefix_extra _ _ (by simp [globalFilterPort]) (by simp [globalFilterPort])]; exact bg k
  have hct : c.stk (globalFilterPort .temp) = [] := by
    rw [blockCountPrefix_extra _ _ (by decide) (by decide)]; exact hbt
  have hcv : c.stk (globalFilterPort .typeIndex) = List.replicate (originalTargetBudget R) true := by
    rw [blockCountPrefix_extra _ _ (by decide) (by decide)]
    exact canonicalBudget_value _ _ _ s
  obtain ⟨a, ha, h2⟩ := binaryPrefix_executes (globalFilterPort .typeIndex) (globalFilterPort .temp)
    (globalFilterPort .output) (by decide) (by decide) (by decide) (originalTargetBudget R) c hcv hct
  have tg : ∀ k : CanonicalGlobalPort, t.stk (.inr k) = s.stk (.inr k) := by
    intro k; rw [binaryPrefix_extra _ _ _ (by simp [globalFilterPort]) (by simp [globalFilterPort])]; exact cg k
  have htt : t.stk (globalFilterPort .temp) = [] := by
    rw [binaryPrefix_extra _ _ _ (by decide) (by decide)]; exact hct
  have htv : t.stk (globalFilterPort .typeIndex) = [] := binaryPrefix_source _ _ _
  have htm : t.stk (.inr .rowCount) = List.replicate R.rows.length true := by rw [tg]; exact hs.rows
  obtain ⟨d, hd, h3⟩ := copiedBinaryHeader_executes .rowCount R.rows.length t htm htv htt
  have rg : ∀ k : CanonicalGlobalPort, r.stk (.inr k) = s.stk (.inr k) := by
    intro k; rw [copiedBinaryHeader_extra _ _ _ (by simp [globalFilterPort]) (by simp [globalFilterPort])]; exact tg k
  have hrt : r.stk (globalFilterPort .temp) = [] := by
    rw [copiedBinaryHeader_extra _ _ _ (by decide) (by decide)]; exact htt
  have hrv : r.stk (globalFilterPort .typeIndex) = [] := copiedBinaryHeader_type _ _
  have hrN : r.stk (.inr .universe) = List.replicate R.N true := by rw [rg]; exact hs.universe
  obtain ⟨e, he, h4⟩ := copiedBinaryHeader_executes .universe R.N r hrN hrv hrt
  have hall := RoutineComposition.seq_executes _ _ h0 (RoutineComposition.seq_executes _ _ h1
    (RoutineComposition.seq_executes _ _ h2 (RoutineComposition.seq_executes _ _ h3 h4)))
  refine ⟨(3 * rawRowFixedCost R + 3 * R.K + 4 * R.N + 11) +
    ((7 * R.rows.length + 13) + (a + (d + e))), by unfold canonicalHeadersBound; omega, hall, ?_⟩
  have hout0 : b.stk (globalFilterPort .output) = s.stk (globalFilterPort .output) :=
    canonicalBudget_extra _ _ _ s _ (by decide) (by decide)
  have hout1 := blockCountPrefix_output R.rows.length b hbm hbc
  have hout2 := binaryPrefix_output (globalFilterPort .typeIndex) (globalFilterPort .output)
    (by decide) (originalTargetBudget R) c hcv
  have hout3 := copiedBinaryHeader_output .rowCount R.rows.length t htm htv
  have hout4 := copiedBinaryHeader_output .universe R.N r hrN hrv
  rw [hout4, hout3, hout2, hout1, hout0]
  simp [originalHeaderPrefix, List.append_assoc]

theorem canonicalHeaders_state (R : RawMSSCRecord) (s : CanonicalGlobalStore) :
    (canonicalHeadersEval R s).state = (s.state.1, true) := rfl

theorem canonicalHeaders_extra (R : RawMSSCRecord) (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (hv : k ≠ globalFilterPort .typeIndex) (hr : k ≠ globalFilterPort .remaining)
    (hc : k ≠ globalFilterPort .count) (ho : k ≠ globalFilterPort .output) :
    (canonicalHeadersEval R s).stk k = s.stk k := by
  rw [copiedBinaryHeader_extra _ _ _ hv ho, copiedBinaryHeader_extra _ _ _ hv ho,
    binaryPrefix_extra _ _ _ hv ho, blockCountPrefix_extra _ _ hc ho,
    canonicalBudget_extra _ _ _ _ _ hv hr]

theorem canonicalHeaders_type (R : RawMSSCRecord) (s : CanonicalGlobalStore) :
    (canonicalHeadersEval R s).stk (globalFilterPort .typeIndex) = [] := copiedBinaryHeader_type _ _

theorem canonicalHeaders_count (R : RawMSSCRecord) (s : CanonicalGlobalStore) :
    (canonicalHeadersEval R s).stk (globalFilterPort .count) = [] := by
  rw [copiedBinaryHeader_extra _ _ _ (by decide) (by decide), copiedBinaryHeader_extra _ _ _ (by decide) (by decide),
    binaryPrefix_extra _ _ _ (by decide) (by decide)]
  exact blockCountPrefix_count _

theorem canonicalHeaders_remaining (R : RawMSSCRecord) (s : CanonicalGlobalStore) :
    (canonicalHeadersEval R s).stk (globalFilterPort .remaining) = [] := by
  rw [copiedBinaryHeader_extra _ _ _ (by decide) (by decide), copiedBinaryHeader_extra _ _ _ (by decide) (by decide),
    binaryPrefix_extra _ _ _ (by decide) (by decide), blockCountPrefix_extra _ _ (by decide) (by decide)]
  exact canonicalBudget_remaining _ _ _ _

theorem canonicalHeaders_inv (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) : GlobalCanonicalInv R L (canonicalHeadersEval R s) := by
  have hold : ∀ k : NumericStack UnaryScanPort,
      (canonicalHeadersEval R s).stk (globalScanPort k) = s.stk (globalScanPort k) := by
    intro k; exact canonicalHeaders_extra R s _ (by simp [globalScanPort, globalFilterPort])
      (by simp [globalScanPort, globalFilterPort]) (by simp [globalScanPort, globalFilterPort]) (by simp [globalScanPort, globalFilterPort])
  have hg : ∀ k : CanonicalGlobalPort, (canonicalHeadersEval R s).stk (.inr k) = s.stk (.inr k) := by
    intro k; exact canonicalHeaders_extra R s _ (by simp [globalFilterPort]) (by simp [globalFilterPort])
      (by simp [globalFilterPort]) (by simp [globalFilterPort])
  refine ⟨UnaryScanReady_of_stacks 0 L _ _ hs.scan hold, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    canonicalHeaders_type R s, canonicalHeaders_count R s, canonicalHeaders_remaining R s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hold]; exact hs.query_empty
  · rw [hold]; exact hs.parsed
  · rw [hg]; exact hs.universe
  · rw [hg]; exact hs.rows
  · rw [hg]; exact hs.budget
  · rw [hg]; exact hs.alphabet
  · rw [hg]; exact hs.marker
  · rw [hg]; exact hs.counter_unary
  · rw [hg]; exact hs.counter_bound
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hs.temp_empty
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hs.cost_unary
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hs.row_bound
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hs.threshold_bound
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hs.block_bound
  · rfl

/- Actual execution order is unary count, binary budget, binary m, binary
N, because every emitted frame is prepended. The first original header
is N, NOT alphabet A. Restored block invariant does not erase the real
intermediate budget word or its costs. Total branch dispatch/cleanup/
standalone machine, independent verifier/hardness/kernel checks remain.
-/

end PolytomyReductionModel
