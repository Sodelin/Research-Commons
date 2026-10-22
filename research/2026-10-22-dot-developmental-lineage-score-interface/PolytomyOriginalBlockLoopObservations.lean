/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact ORIGINAL ordered leaves and accepted-count/comb-cost observations
of the SAME actual physical loop, for real blocks AND the anchor. The
anchor's actual out-of-range selected query is proved false, not omitted.
-/
import PolytomyOriginalBlockSemanticInvariant

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem originalBlockLoop_ordered_output (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B : ℕ) (n : ℕ) :
    ∀ s : CanonicalFilterStore, OriginalBlockSemanticInv R b L S I B s →
      (s.stk (.inr .typeIndex)).length = n → s.state.2 = true →
      (countdownLoopEval (.inr .typeIndex) (realTypeBodyEval (originalBlockThreshold R b)) n
        (countdownPeek (.inr .typeIndex) s)).stk (.inr .output) =
        originalFilteredTokens R b n ++ s.stk (.inr .output) := by
  induction n with
  | zero =>
      intro s hs hlen hok
      simp [countdownLoopEval, originalFilteredTokens, countdownPeek, countdownPeekOp, Op.apply]
  | succ n ih =>
      intro s hs hlen hok
      have hhead : (s.stk (.inr .typeIndex)).head?.isSome = true := by
        cases hw : s.stk (.inr .typeIndex) with
        | nil => simp [hw] at hlen
        | cons x xs => rfl
      have hg : countdownGuard (countdownPeek (.inr .typeIndex) s).state = true := by
        simp [countdownGuard, countdownPeek, countdownPeekOp, Op.apply, hhead, hok]
      let p := countdownPop (.inr CanonicalFilterPort.typeIndex) (countdownPeek (.inr .typeIndex) s)
      have hp : OriginalBlockSemanticInv R b L S I B p := originalBlockSemantic_pop R b L S I B _
        (OriginalBlockSemanticInv_of_stacks R b L S I B s _ hs (fun _ => rfl))
      have hplen : (p.stk (.inr .typeIndex)).length = n := by
        change ((countdownPop (.inr .typeIndex) (countdownPeek (.inr .typeIndex) s)).stk (.inr .typeIndex)).length = n
        rw [countdownPop_counter]
        change (s.stk (.inr .typeIndex)).tail.length = n
        rw [List.length_tail, hlen]; omega
      have hpout : p.stk (.inr .output) = s.stk (.inr .output) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply]
      let t := realTypeBodyEval (originalBlockThreshold R b) p
      have ht : OriginalBlockSemanticInv R b L S I B t := originalBlockSemantic_body R b L S I B p hp
      have htlen : (t.stk (.inr .typeIndex)).length = n := by
        rw [realTypeBody_counter]; exact hplen
      have htrue : t.state.2 = true := realTypeBody_success _ _
      have hbody := originalBlockType_original_output R hR b L S I B p hp
      rw [hplen, hpout] at hbody
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      change (countdownLoopEval (.inr .typeIndex) (realTypeBodyEval (originalBlockThreshold R b)) n
        (countdownPeek (.inr .typeIndex) t)).stk (.inr .output) = _
      rw [ih t ht htlen htrue]
      change originalFilteredTokens R b n ++ t.stk (.inr .output) = _
      rw [show t.stk (.inr .output) = _ from hbody, originalFilteredTokens_succ]
      cases hm : rawRowMember R b n <;> simp [hm, List.append_assoc]

theorem originalBlockLoop_output (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B : ℕ) (s : CanonicalFilterStore)
    (hs : OriginalBlockSemanticInv R b L S I B s) (hok : s.state.2 = true) :
    (realTypeLoopEval (originalBlockThreshold R b) s).stk (.inr .output) =
      originalFilteredTokens R b (s.stk (.inr .typeIndex)).length ++ s.stk (.inr .output) :=
  originalBlockLoop_ordered_output R hR b L S I B _ s hs rfl hok

theorem originalBlockLoop_original_leaf_sequence (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B : ℕ) (s : CanonicalFilterStore)
    (hs : OriginalBlockSemanticInv R b L S I B s) (hok : s.state.2 = true)
    (hall : s.stk (.inr .typeIndex) = List.replicate (rawRowAlphabet R) true) :
    (realTypeLoopEval (originalBlockThreshold R b) s).stk (.inr .output) =
      (rawRowCodes R b).flatMap
        (fun n => true :: (unaryFrame (blockCode b) ++ unaryFrame n)) ++ s.stk (.inr .output) := by
  rw [originalBlockLoop_output R hR b L S I B s hs hok, hall, List.length_replicate]
  rfl

theorem originalBlockType_original_comb (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B A acc q : ℕ) (s : CanonicalFilterStore)
    (hs : OriginalBlockSemanticInv R b L S I B s) (hcomb : RealTypeCombInv A acc q s) :
    RealTypeCombInv A acc (q + if rawRowMember R b (s.stk (.inr .typeIndex)).length then 1 else 0)
      (realTypeBodyEval (originalBlockThreshold R b) s) := by
  let C := (s.stk (.inr .typeIndex)).length
  let m := realBlockMembershipBase C (originalBlockThreshold R b) CanonicalFilterPort.typeIndex .rowIndex
    (selectedCallerBase s) (selectedCallerExtra s)
  let u := extraPortsStore m (selectedCallerExtra s)
  have hm : u.state.2 = rawRowMember R b C :=
    realBlockMembership_original_block .typeIndex .rowIndex C L (originalBlockThreshold R b)
      (selectedCallerBase s) hs.operational.scan (selectedCallerExtra s) hs.operational.type_unary
      R hs.parsed hR b hs.row_index rfl
  have hu : RealTypeCombInv A acc q u := hcomb
  have h := canonicalLeafGate_comb (callerLeafLayout canonicalFilterLayout) A acc q u hu
  rw [hm] at h
  exact h

theorem originalBlockLoop_comb_fold (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B A acc n : ℕ) :
    ∀ (s : CanonicalFilterStore) (q : ℕ), OriginalBlockSemanticInv R b L S I B s →
      RealTypeCombInv A acc q s → (s.stk (.inr .typeIndex)).length = n → s.state.2 = true →
      RealTypeCombInv A acc (q + originalFilteredCount R b n)
        (countdownLoopEval (.inr .typeIndex) (realTypeBodyEval (originalBlockThreshold R b)) n
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
      have hp : OriginalBlockSemanticInv R b L S I B p := originalBlockSemantic_pop R b L S I B _
        (OriginalBlockSemanticInv_of_stacks R b L S I B s _ hs (fun _ => rfl))
      have hpcomb : RealTypeCombInv A acc q p := by
        simpa [p, RealTypeCombInv, CanonicalCombInv, callerLeafLayout, canonicalFilterLayout,
          countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply] using hcomb
      have hplen : (p.stk (.inr .typeIndex)).length = n := by
        change ((countdownPop (.inr .typeIndex) (countdownPeek (.inr .typeIndex) s)).stk (.inr .typeIndex)).length = n
        rw [countdownPop_counter]
        change (s.stk (.inr .typeIndex)).tail.length = n
        rw [List.length_tail, hlen]; omega
      let t := realTypeBodyEval (originalBlockThreshold R b) p
      have ht := originalBlockSemantic_body R b L S I B p hp
      have htcomb := originalBlockType_original_comb R hR b L S I B A acc q p hp hpcomb
      rw [hplen] at htcomb
      have htlen : (t.stk (.inr .typeIndex)).length = n := by rw [realTypeBody_counter]; exact hplen
      have hi := ih t (q + if rawRowMember R b n then 1 else 0) ht htcomb htlen (realTypeBody_success _ _)
      have hq : (q + if rawRowMember R b n then 1 else 0) + originalFilteredCount R b n =
          q + originalFilteredCount R b (n + 1) := by
        rw [originalFilteredCount_succ]
        omega
      rw [hq] at hi
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      exact hi

theorem originalBlockLoop_comb (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B A acc q : ℕ) (s : CanonicalFilterStore)
    (hs : OriginalBlockSemanticInv R b L S I B s) (hcomb : RealTypeCombInv A acc q s) (hok : s.state.2 = true) :
    RealTypeCombInv A acc (q + originalFilteredCount R b (s.stk (.inr .typeIndex)).length)
      (realTypeLoopEval (originalBlockThreshold R b) s) :=
  originalBlockLoop_comb_fold R hR b L S I B A acc _ s q hs hcomb rfl hok

theorem originalBlockLoop_original_comb (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B acc : ℕ) (s : CanonicalFilterStore)
    (hs : OriginalBlockSemanticInv R b L S I B s) (hok : s.state.2 = true)
    (hall : s.stk (.inr .typeIndex) = List.replicate (rawRowAlphabet R) true)
    (hremaining : s.stk (.inr .remaining) = List.replicate (rawRowAlphabet R) true)
    (hcount : s.stk (.inr .count) = []) (hcost : s.stk (.inr .cost) = List.replicate acc true) :
    RealTypeCombInv (rawRowAlphabet R) acc (rawRowCodes R b).length
      (realTypeLoopEval (originalBlockThreshold R b) s) := by
  have hinit : RealTypeCombInv (rawRowAlphabet R) acc 0 s := by
    simp [RealTypeCombInv, CanonicalCombInv, callerLeafLayout, canonicalFilterLayout,
      hremaining, hcount, hcost, combTailCost]
  have h := originalBlockLoop_comb R hR b L S I B (rawRowAlphabet R) acc 0 s hs hinit hok
  simpa [hall, originalFilteredCount, rawRowCodes] using h


/- These are observations of the fully instantiated actual routine.
They do not supply its body as an oracle. Entry physical row/threshold/
block/type words remain explicit obligations of the complete caller.
All source, verifier, encoded-hardness, dependency and kernel limits
remain; this is not the complete constructor or a compiled certificate.
-/

end PolytomyReductionModel
