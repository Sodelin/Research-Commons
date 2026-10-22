/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The SAME actual block routine emits every ORIGINAL real OR anchor block,
with exact bytes, original comb cost and work cleanup. Input parameters
are physical tapes, not unbounded finite control or a chosen solution.
-/
import PolytomyOriginalBlockLoopObservations

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

abbrev originalCanonicalBlockRoutine := realCanonicalBlockRoutine

def originalCanonicalBlockEval (R : RawMSSCRecord) (b : Block R.rows.length)
    (s : CanonicalFilterStore) :=
  clearStackEval (.inr .remaining)
    (canonicalCombPrefixEval (.inr .count) (.inr .output) (realTypeLoopEval (originalBlockThreshold R b) s))

def originalCanonicalBlockBound (R : RawMSSCRecord) (b : Block R.rows.length) (L I B : ℕ) :=
  rawRowAlphabet R * (realTypeBodyBound L (rawRowAlphabet R) I (originalBlockThreshold R b) B + 3) +
    rawRowAlphabet R + 6

theorem originalCanonicalBlock_executes (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L I B acc : ℕ) (s : CanonicalFilterStore)
    (hs : OriginalBlockSemanticInv R b L (rawRowAlphabet R) I B s) (hok : s.state.2 = true)
    (hall : s.stk (.inr .typeIndex) = List.replicate (rawRowAlphabet R) true)
    (hremaining : s.stk (.inr .remaining) = List.replicate (rawRowAlphabet R) true)
    (hcount : s.stk (.inr .count) = []) (hcost : s.stk (.inr .cost) = List.replicate acc true) :
    ∃ n ≤ originalCanonicalBlockBound R b L I B,
      originalCanonicalBlockRoutine.Executes s (originalCanonicalBlockEval R b s) n ∧
      (originalCanonicalBlockEval R b s).stk (.inr .output) = rawRowBlockBits R b ++ s.stk (.inr .output) ∧
      (originalCanonicalBlockEval R b s).stk (.inr .cost) =
        List.replicate (acc + combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R b).length - 1)) true ∧
      (originalCanonicalBlockEval R b s).stk (.inr .typeIndex) = [] ∧
      (originalCanonicalBlockEval R b s).stk (.inr .count) = [] ∧
      (originalCanonicalBlockEval R b s).stk (.inr .remaining) = [] ∧
      UnaryScanReady 0 L (selectedCallerBase (originalCanonicalBlockEval R b s)) ∧
      (originalCanonicalBlockEval R b s).stk (.inl (.inr .queries)) = [] ∧
      (originalCanonicalBlockEval R b s).stk (.inl (.inr .original)) = s.stk (.inl (.inr .original)) ∧
      (originalCanonicalBlockEval R b s).state.2 = true := by
  let A := rawRowAlphabet R
  let q := (rawRowCodes R b).length
  let u := realTypeLoopEval (originalBlockThreshold R b) s
  let v := canonicalCombPrefixEval (.inr CanonicalFilterPort.count) (.inr .output) u
  obtain ⟨n, hn, hloop, hi, hflag, hguard, htype⟩ := realTypeLoop_executes L A I (originalBlockThreshold R b) B s hs.operational hok
  have hout := originalBlockLoop_original_leaf_sequence R hR b L A I B s hs hok hall
  have hcomb := originalBlockLoop_original_comb R hR b L A I B acc s hs hok hall hremaining hcount hcost
  change u.stk (.inr .remaining) = List.replicate (A - q) true ∧
    u.stk (.inr .count) = List.replicate q true ∧
    u.stk (.inr .cost) = List.replicate (acc + combTailCost A 1 (q - 1)) true at hcomb
  have hqle : q ≤ A := rawRowCodes_length_le R b
  have hprefix := canonicalCombPrefix_executes (.inr CanonicalFilterPort.count : CanonicalFilterStack) (.inr .output)
    (by decide) u
  rw [hcomb.2.1, List.length_replicate] at hprefix
  have hvremaining : v.stk (.inr .remaining) = List.replicate (A - q) true := by
    rw [canonicalCombPrefix_extra _ _ _ (by decide) (by decide)]
    exact hcomb.1
  have hclear := clearStack_executes (.inr CanonicalFilterPort.remaining : CanonicalFilterStack) v
  rw [hvremaining, List.length_replicate] at hclear
  have htail := RoutineComposition.seq_executes _ _ hprefix hclear
  have hallExec := RoutineComposition.seq_executes _ _ hloop htail
  have hfinalBase : ∀ k : NumericStack UnaryScanPort,
      (selectedCallerBase (originalCanonicalBlockEval R b s)).stk k = (selectedCallerBase u).stk k := by
    intro k
    change (clearStackEval (.inr .remaining) v).stk (.inl k) = u.stk (.inl k)
    simp only [clearStackEval, Function.update_of_ne (by simp : (Sum.inl k : CanonicalFilterStack) ≠ .inr .remaining)]
    exact canonicalCombPrefix_extra _ _ _ (by simp) (by simp) u
  have hrecord := realTypeLoop_original_preserved L A I (originalBlockThreshold R b) B s hs.operational
  refine ⟨n + ((q - 1 + 2) + (A - q + 1)), ?_, hallExec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold originalCanonicalBlockBound
    change n ≤ A * (realTypeBodyBound L A I (originalBlockThreshold R b) B + 3) + 3 at hn
    change _ ≤ A * (realTypeBodyBound L A I (originalBlockThreshold R b) B + 3) + A + 6
    omega
  · change (clearStackEval (.inr .remaining) v).stk (.inr .output) = _
    simp only [clearStackEval, Function.update_of_ne (by decide :
      (Sum.inr CanonicalFilterPort.output : CanonicalFilterStack) ≠ .inr .remaining)]
    rw [canonicalCombPrefix_bytes _ _ (by decide), hcomb.2.1, List.length_replicate]
    change List.replicate (q - 1) false ++ u.stk (.inr .output) = _
    rw [show u.stk (.inr .output) = _ from hout]
    simp only [rawRowBlockBits, q, List.append_assoc]
  · change (clearStackEval (.inr .remaining) v).stk (.inr .cost) = _
    simp only [clearStackEval, Function.update_of_ne (by decide :
      (Sum.inr CanonicalFilterPort.cost : CanonicalFilterStack) ≠ .inr .remaining)]
    rw [canonicalCombPrefix_extra _ _ _ (by decide) (by decide)]
    exact hcomb.2.2
  · change (clearStackEval (.inr .remaining) v).stk (.inr .typeIndex) = []
    simp only [clearStackEval, Function.update_of_ne (by decide :
      (Sum.inr CanonicalFilterPort.typeIndex : CanonicalFilterStack) ≠ .inr .remaining)]
    rw [canonicalCombPrefix_extra _ _ _ (by decide) (by decide)]
    exact htype
  · change (clearStackEval (.inr .remaining) v).stk (.inr .count) = []
    simp only [clearStackEval, Function.update_of_ne (by decide :
      (Sum.inr CanonicalFilterPort.count : CanonicalFilterStack) ≠ .inr .remaining)]
    exact canonicalCombPrefix_count _ _ (by decide) u
  · simp [originalCanonicalBlockEval, clearStackEval]
  · exact UnaryScanReady_of_stacks 0 L _ _ hi.scan hfinalBase
  · change (selectedCallerBase (originalCanonicalBlockEval R b s)).stk (.inr .queries) = []
    rw [hfinalBase]; exact hi.query_empty
  · change (selectedCallerBase (originalCanonicalBlockEval R b s)).stk (.inr .original) = _
    rw [hfinalBase]; exact hrecord
  · exact hflag


/- This includes the ORIGINAL anchor (b=none) and each real block.
The code is identical for every b; only physical caller data differ.
Actual preparation, validator/control integration, complete block order,
boundary branches, budget/binary headers, global cleanup and standalone
constructor remain open. Independent verifier, closed encoded hardness,
dependency/toolchain/axiom/kernel checks also remain. No runtime or
new review/certificate/novelty/full-complexity closure is claimed.
-/

end PolytomyReductionModel
