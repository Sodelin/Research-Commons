/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual COMPLETE original real-block emission from prepared physical
caller data: real descending queries/gates, exact original ordered leaves,
original comb cost, actual q-1 node prefix and remaining-counter cleanup.
Physical setup of those entry data and the full block controller remain.
-/
import PolytomyRealTypeCombFold

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def realCanonicalBlockRoutine : Routine (fun _ : CanonicalFilterStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq realTypeLoopRoutine
    (RoutineComposition.seq (canonicalCombPrefixRoutine (.inr .count) (.inr .output))
      (clearStackRoutine (.inr .remaining)))

def realCanonicalBlockEval (R : RawMSSCRecord) (s : CanonicalFilterStore) :=
  clearStackEval (.inr .remaining)
    (canonicalCombPrefixEval (.inr .count) (.inr .output) (realTypeLoopEval (originalMarkerThreshold R) s))

def realCanonicalBlockBound (R : RawMSSCRecord) (L I B : ℕ) :=
  rawRowAlphabet R * (realTypeBodyBound L (rawRowAlphabet R) I (originalMarkerThreshold R) B + 3) +
    rawRowAlphabet R + 6

theorem realTypeLoop_original_preserved (L S I T B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) :
    (realTypeLoopEval T s).stk (.inl (.inr .original)) = s.stk (.inl (.inr .original)) := by
  let hc := realTypeLoopContract L S I T B
  have hb : ∀ t, RealTypeLoopInv L S I T B t →
      (realTypeBodyEval T t).stk (.inl (.inr .original)) = t.stk (.inl (.inr .original)) := by
    intro t ht
    exact (realCanonicalType_ready canonicalFilterLayout .rowIndex _ L T
      (selectedCallerBase t) ht.scan (selectedCallerExtra t) ht.type_unary).2.2
  exact countdownLoop_preserves_on (.inr .typeIndex) realTypeBodyRoutine (realTypeBodyEval T)
    (RealTypeLoopInv L S I T B) (realTypeBodyBound L S I T B) hc
    (fun t => t.stk (.inl (.inr .original))) (fun _ => rfl)
    (by intro t; simp [countdownPop, countdownPopOp, Op.apply]) hb
    (s.stk (.inr .typeIndex)).length (countdownPeek (.inr .typeIndex) s) (hc.peek_closed s hs)

theorem realCanonicalBlock_executes (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L I B acc : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeSemanticInv R i L (rawRowAlphabet R) I B s) (hok : s.state.2 = true)
    (hall : s.stk (.inr .typeIndex) = List.replicate (rawRowAlphabet R) true)
    (hremaining : s.stk (.inr .remaining) = List.replicate (rawRowAlphabet R) true)
    (hcount : s.stk (.inr .count) = []) (hcost : s.stk (.inr .cost) = List.replicate acc true) :
    ∃ n ≤ realCanonicalBlockBound R L I B,
      realCanonicalBlockRoutine.Executes s (realCanonicalBlockEval R s) n ∧
      (realCanonicalBlockEval R s).stk (.inr .output) = rawRowBlockBits R (some i) ++ s.stk (.inr .output) ∧
      (realCanonicalBlockEval R s).stk (.inr .cost) =
        List.replicate (acc + combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R (some i)).length - 1)) true ∧
      (realCanonicalBlockEval R s).stk (.inr .typeIndex) = [] ∧
      (realCanonicalBlockEval R s).stk (.inr .count) = [] ∧
      (realCanonicalBlockEval R s).stk (.inr .remaining) = [] ∧
      UnaryScanReady 0 L (selectedCallerBase (realCanonicalBlockEval R s)) ∧
      (realCanonicalBlockEval R s).stk (.inl (.inr .queries)) = [] ∧
      (realCanonicalBlockEval R s).stk (.inl (.inr .original)) = s.stk (.inl (.inr .original)) ∧
      (realCanonicalBlockEval R s).state.2 = true := by
  let A := rawRowAlphabet R
  let q := (rawRowCodes R (some i)).length
  let u := realTypeLoopEval (originalMarkerThreshold R) s
  let v := canonicalCombPrefixEval (.inr CanonicalFilterPort.count) (.inr .output) u
  obtain ⟨n, hn, hloop, hi, hflag, hguard, htype⟩ := realTypeLoop_executes L A I (originalMarkerThreshold R) B s hs.operational hok
  have hout := realTypeLoop_original_leaf_sequence R hR i L A I B s hs hok hall
  have hcomb := realTypeLoop_original_comb R hR i L A I B acc s hs hok hall hremaining hcount hcost
  change u.stk (.inr .remaining) = List.replicate (A - q) true ∧
    u.stk (.inr .count) = List.replicate q true ∧
    u.stk (.inr .cost) = List.replicate (acc + combTailCost A 1 (q - 1)) true at hcomb
  have hqle : q ≤ A := rawRowCodes_length_le R (some i)
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
      (selectedCallerBase (realCanonicalBlockEval R s)).stk k = (selectedCallerBase u).stk k := by
    intro k
    change (clearStackEval (.inr .remaining) v).stk (.inl k) = u.stk (.inl k)
    simp only [clearStackEval, Function.update_of_ne (by simp : (Sum.inl k : CanonicalFilterStack) ≠ .inr .remaining)]
    exact canonicalCombPrefix_extra _ _ _ (by simp) (by simp) u
  have hrecord := realTypeLoop_original_preserved L A I (originalMarkerThreshold R) B s hs.operational
  refine ⟨n + ((q - 1 + 2) + (A - q + 1)), ?_, hallExec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold realCanonicalBlockBound
    change n ≤ A * (realTypeBodyBound L A I (originalMarkerThreshold R) B + 3) + 3 at hn
    change _ ≤ A * (realTypeBodyBound L A I (originalMarkerThreshold R) B + 3) + A + 6
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
  · simp [realCanonicalBlockEval, clearStackEval]
  · exact UnaryScanReady_of_stacks 0 L _ _ hi.scan hfinalBase
  · change (selectedCallerBase (realCanonicalBlockEval R s)).stk (.inr .queries) = []
    rw [hfinalBase]; exact hi.query_empty
  · change (selectedCallerBase (realCanonicalBlockEval R s)).stk (.inr .original) = _
    rw [hfinalBase]; exact hrecord
  · exact hflag

/- This is the COMPLETE original REAL-BLOCK emitter from prepared caller
data, with actual transitions, exact original bytes/cost and work cleanup.
The source/validity/row/block/threshold data and initial alphabet counters
are explicit entry premises. Their actual construction, anchor block,
global block order, final budget/binary headers/cleanup and standalone
machine remain open, together with independent verifier, encoded hardness
and every dependency/toolchain/axiom/kernel check. No full closure claim.
-/

end PolytomyReductionModel
