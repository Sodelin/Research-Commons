/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact accepted-count and ORIGINAL combTailCost fold for the actual type
loop. The accumulator is physical unary data. No label-size sum or
abstract optimizer objective is substituted for the original score.
-/
import PolytomyRealTypeOrderedOutput

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def CanonicalCombInv (p : CanonicalLeafLayout K) (A acc q : ℕ) (s : CountdownStore K F) : Prop :=
  s.stk (p.port .remaining) = List.replicate (A - q) true ∧
  s.stk (p.port .count) = List.replicate q true ∧
  s.stk (p.port .cost) = List.replicate (acc + combTailCost A 1 (q - 1)) true

theorem canonicalLeafGate_comb (p : CanonicalLeafLayout K) (A acc q : ℕ) (s : CountdownStore K F)
    (hs : CanonicalCombInv p A acc q s) :
    CanonicalCombInv p A acc (q + if s.state.2 then 1 else 0) (canonicalLeafGateEval p s) := by
  cases hf : s.state.2 with
  | false =>
      simpa [canonicalLeafGateEval, canonicalContinueOp, Op.apply, CanonicalCombInv, hf] using hs
  | true =>
      have h := acceptedCanonicalLeaf_comb_invariant p s A q acc hs.1 hs.2.1 hs.2.2
      have hq : q + 1 - 1 = q := by omega
      simpa [canonicalLeafGateEval, canonicalContinueOp, Op.apply, CanonicalCombInv, hf, hq] using h

abbrev RealTypeCombInv (A acc q : ℕ) (s : CanonicalFilterStore) : Prop :=
  CanonicalCombInv (callerLeafLayout canonicalFilterLayout) A acc q s

theorem realTypeBody_original_comb (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B A acc q : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeSemanticInv R i L S I B s) (hcomb : RealTypeCombInv A acc q s) :
    RealTypeCombInv A acc (q + if rawRowMember R (some i) (s.stk (.inr .typeIndex)).length then 1 else 0)
      (realTypeBodyEval (originalMarkerThreshold R) s) := by
  let C := (s.stk (.inr .typeIndex)).length
  let m := realBlockMembershipBase C (originalMarkerThreshold R) CanonicalFilterPort.typeIndex .rowIndex
    (selectedCallerBase s) (selectedCallerExtra s)
  let u := extraPortsStore m (selectedCallerExtra s)
  have hm : u.state.2 = rawRowMember R (some i) C :=
    realBlockMembership_original .typeIndex .rowIndex C L (originalMarkerThreshold R)
      (selectedCallerBase s) hs.operational.scan (selectedCallerExtra s) hs.operational.type_unary
      R hs.parsed hR i hs.row_index rfl
  have hu : RealTypeCombInv A acc q u := hcomb
  have h := canonicalLeafGate_comb (callerLeafLayout canonicalFilterLayout) A acc q u hu
  rw [hm] at h
  exact h

def originalFilteredCount (R : RawMSSCRecord) (b : Block R.rows.length) (n : ℕ) : ℕ :=
  ((List.range n).filter (rawRowMember R b)).length

theorem originalFilteredCount_succ (R : RawMSSCRecord) (b : Block R.rows.length) (n : ℕ) :
    originalFilteredCount R b (n + 1) = originalFilteredCount R b n + if rawRowMember R b n then 1 else 0 := by
  unfold originalFilteredCount
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : rawRowMember R b n <;> simp [h]

theorem realTypeLoop_comb_fold (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B A acc n : ℕ) :
    ∀ (s : CanonicalFilterStore) (q : ℕ), RealTypeSemanticInv R i L S I B s →
      RealTypeCombInv A acc q s → (s.stk (.inr .typeIndex)).length = n → s.state.2 = true →
      RealTypeCombInv A acc (q + originalFilteredCount R (some i) n)
        (countdownLoopEval (.inr .typeIndex) (realTypeBodyEval (originalMarkerThreshold R)) n
          (countdownPeek (.inr .typeIndex) s)) := by
  induction n with
  | zero =>
      intro s q hs hcomb hlen hok
      simpa [countdownLoopEval, originalFilteredCount, RealTypeCombInv, CanonicalCombInv,
        countdownPeek, countdownPeekOp, Op.apply] using hcomb
  | succ n ih =>
      intro s q hs hcomb hlen hok
      have hhead : (s.stk (.inr .typeIndex)).head?.isSome = true := by
        cases hw : s.stk (.inr .typeIndex) with
        | nil => simp [hw] at hlen
        | cons x xs => rfl
      have hg : countdownGuard (countdownPeek (.inr .typeIndex) s).state = true := by
        simp [countdownGuard, countdownPeek, countdownPeekOp, Op.apply, hhead, hok]
      let p := countdownPop (.inr CanonicalFilterPort.typeIndex) (countdownPeek (.inr .typeIndex) s)
      have hp : RealTypeSemanticInv R i L S I B p := realTypeSemantic_pop R i L S I B _
        (RealTypeSemanticInv_of_stacks R i L S I B s _ hs (fun _ => rfl))
      have hpcomb : RealTypeCombInv A acc q p := by
        simpa [p, RealTypeCombInv, CanonicalCombInv, callerLeafLayout, canonicalFilterLayout,
          countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply] using hcomb
      have hplen : (p.stk (.inr .typeIndex)).length = n := by
        change ((countdownPop (.inr .typeIndex) (countdownPeek (.inr .typeIndex) s)).stk (.inr .typeIndex)).length = n
        rw [countdownPop_counter]
        change (s.stk (.inr .typeIndex)).tail.length = n
        rw [List.length_tail, hlen]; omega
      let t := realTypeBodyEval (originalMarkerThreshold R) p
      have ht := realTypeSemantic_body R i L S I B p hp
      have htcomb := realTypeBody_original_comb R hR i L S I B A acc q p hp hpcomb
      rw [hplen] at htcomb
      have htlen : (t.stk (.inr .typeIndex)).length = n := by rw [realTypeBody_counter]; exact hplen
      have hi := ih t (q + if rawRowMember R (some i) n then 1 else 0) ht htcomb htlen (realTypeBody_success _ _)
      have hq : (q + if rawRowMember R (some i) n then 1 else 0) + originalFilteredCount R (some i) n =
          q + originalFilteredCount R (some i) (n + 1) := by
        rw [originalFilteredCount_succ]
        omega
      rw [hq] at hi
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      exact hi

theorem realTypeLoop_comb (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B A acc q : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeSemanticInv R i L S I B s) (hcomb : RealTypeCombInv A acc q s) (hok : s.state.2 = true) :
    RealTypeCombInv A acc (q + originalFilteredCount R (some i) (s.stk (.inr .typeIndex)).length)
      (realTypeLoopEval (originalMarkerThreshold R) s) :=
  realTypeLoop_comb_fold R hR i L S I B A acc _ s q hs hcomb rfl hok

theorem realTypeLoop_original_comb (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B acc : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeSemanticInv R i L S I B s) (hok : s.state.2 = true)
    (hall : s.stk (.inr .typeIndex) = List.replicate (rawRowAlphabet R) true)
    (hremaining : s.stk (.inr .remaining) = List.replicate (rawRowAlphabet R) true)
    (hcount : s.stk (.inr .count) = []) (hcost : s.stk (.inr .cost) = List.replicate acc true) :
    RealTypeCombInv (rawRowAlphabet R) acc (rawRowCodes R (some i)).length
      (realTypeLoopEval (originalMarkerThreshold R) s) := by
  have hinit : RealTypeCombInv (rawRowAlphabet R) acc 0 s := by
    simp [RealTypeCombInv, CanonicalCombInv, callerLeafLayout, canonicalFilterLayout,
      hremaining, hcount, hcost, combTailCost]
  have h := realTypeLoop_comb R hR i L S I B (rawRowAlphabet R) acc 0 s hs hinit hok
  simpa [hall, originalFilteredCount, rawRowCodes] using h

/- The actual loop now has both original ordered-leaf and original
accepted-count/comb-cost observations. Full-block finishing must still
perform the actual q-1 false prefix, clear remaining work, preserve global
cost, and join physical initialization/anchor/block order/serialization.
All source terms remain unelaborated and no complexity closure is claimed.
-/

end PolytomyReductionModel
