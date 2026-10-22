/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact original ascending filtered leaf sequence from the actual
descending physical type loop. This is an observation of the instantiated
query/threshold/leaf machine, not a substitute abstract filtering program.
-/
import PolytomyRealTypeSemanticInvariant

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalFilteredTokens (R : RawMSSCRecord) (b : Block R.rows.length) (n : ℕ) : List Bool :=
  ((List.range n).filter (rawRowMember R b)).flatMap (originalLeafToken (blockCode b))

theorem originalFilteredTokens_succ (R : RawMSSCRecord) (b : Block R.rows.length) (n : ℕ) :
    originalFilteredTokens R b (n + 1) = originalFilteredTokens R b n ++
      (if rawRowMember R b n then originalLeafToken (blockCode b) n else []) := by
  unfold originalFilteredTokens
  rw [List.range_succ, List.filter_append, List.flatMap_append]
  cases h : rawRowMember R b n <;> simp [h]

theorem realTypeLoop_ordered_output (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B : ℕ) (n : ℕ) :
    ∀ s : CanonicalFilterStore, RealTypeSemanticInv R i L S I B s →
      (s.stk (.inr .typeIndex)).length = n → s.state.2 = true →
      (countdownLoopEval (.inr .typeIndex) (realTypeBodyEval (originalMarkerThreshold R)) n
        (countdownPeek (.inr .typeIndex) s)).stk (.inr .output) =
        originalFilteredTokens R (some i) n ++ s.stk (.inr .output) := by
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
      have hp : RealTypeSemanticInv R i L S I B p := realTypeSemantic_pop R i L S I B _
        (RealTypeSemanticInv_of_stacks R i L S I B s _ hs (fun _ => rfl))
      have hplen : (p.stk (.inr .typeIndex)).length = n := by
        change ((countdownPop (.inr .typeIndex) (countdownPeek (.inr .typeIndex) s)).stk (.inr .typeIndex)).length = n
        rw [countdownPop_counter]
        change (s.stk (.inr .typeIndex)).tail.length = n
        rw [List.length_tail, hlen]; omega
      have hpout : p.stk (.inr .output) = s.stk (.inr .output) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply]
      let t := realTypeBodyEval (originalMarkerThreshold R) p
      have ht : RealTypeSemanticInv R i L S I B t := realTypeSemantic_body R i L S I B p hp
      have htlen : (t.stk (.inr .typeIndex)).length = n := by
        rw [realTypeBody_counter]; exact hplen
      have htrue : t.state.2 = true := realTypeBody_success _ _
      have hbody := realTypeBody_original_output R hR i L S I B p hp
      rw [hplen, hpout] at hbody
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      change (countdownLoopEval (.inr .typeIndex) (realTypeBodyEval (originalMarkerThreshold R)) n
        (countdownPeek (.inr .typeIndex) t)).stk (.inr .output) = _
      rw [ih t ht htlen htrue]
      change originalFilteredTokens R (some i) n ++ t.stk (.inr .output) = _
      rw [show t.stk (.inr .output) = _ from hbody, originalFilteredTokens_succ]
      cases hm : rawRowMember R (some i) n <;> simp [hm, List.append_assoc]

theorem realTypeLoop_output (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeSemanticInv R i L S I B s) (hok : s.state.2 = true) :
    (realTypeLoopEval (originalMarkerThreshold R) s).stk (.inr .output) =
      originalFilteredTokens R (some i) (s.stk (.inr .typeIndex)).length ++ s.stk (.inr .output) :=
  realTypeLoop_ordered_output R hR i L S I B _ s hs rfl hok

theorem realTypeLoop_original_leaf_sequence (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeSemanticInv R i L S I B s) (hok : s.state.2 = true)
    (hall : s.stk (.inr .typeIndex) = List.replicate (rawRowAlphabet R) true) :
    (realTypeLoopEval (originalMarkerThreshold R) s).stk (.inr .output) =
      (rawRowCodes R (some i)).flatMap
        (fun n => true :: (unaryFrame (blockCode (some i)) ++ unaryFrame n)) ++ s.stk (.inr .output) := by
  rw [realTypeLoop_output R hR i L S I B s hs hok, hall, List.length_replicate]
  rfl

/- The output order is ORIGINAL increasing code order, despite the
physical countdown visiting the codes in decreasing order. Every call
was the real copied query/threshold/gate body. Exact accepted count,
original comb-cost fold, q-1 comb prefix, anchor and block ordering,
initial arithmetic, binary serializer and full machine remain to join.
All terms remain unelaborated; no runtime or certificate is claimed.
-/

end PolytomyReductionModel
