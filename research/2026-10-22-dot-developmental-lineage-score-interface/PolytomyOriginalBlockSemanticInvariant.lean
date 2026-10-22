/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Original-valid-source semantic invariant for every actual original block,
including the anchor through its physical out-of-range row selector.
Record, row, threshold and block code are physical data, not witnesses.
-/
import PolytomyOriginalAnchorParameters

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

structure OriginalBlockSemanticInv (R : RawMSSCRecord) (b : Block R.rows.length)
    (L S I B : ℕ) (s : CanonicalFilterStore) : Prop where
  operational : RealTypeLoopInv L S I (originalBlockThreshold R b) B s
  parsed : readNormalizedSource (s.stk (.inl (.inr .original))) = some R
  row_index : (s.stk (.inr .rowIndex)).length = originalBlockRowIndex R b
  block_word : s.stk (.inr .blockCode) = List.replicate (blockCode b) true

theorem OriginalBlockSemanticInv_of_stacks (R : RawMSSCRecord) (b : Block R.rows.length)
    (L S I B : ℕ) (s t : CanonicalFilterStore) (hs : OriginalBlockSemanticInv R b L S I B s)
    (h : ∀ k, t.stk k = s.stk k) : OriginalBlockSemanticInv R b L S I B t := by
  refine ⟨RealTypeLoopInv_of_stacks L S I _ B s t hs.operational h, ?_, ?_, ?_⟩
  · rw [h]; exact hs.parsed
  · rw [h]; exact hs.row_index
  · rw [h]; exact hs.block_word

theorem originalBlockSemantic_pop (R : RawMSSCRecord) (b : Block R.rows.length) (L S I B : ℕ)
    (s : CanonicalFilterStore) (hs : OriginalBlockSemanticInv R b L S I B s) :
    OriginalBlockSemanticInv R b L S I B (countdownPop (.inr .typeIndex) s) := by
  refine ⟨realTypeLoop_pop_invariant L S I _ B s hs.operational, ?_, ?_, ?_⟩
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.parsed
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.row_index
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.block_word

theorem originalBlockSemantic_body (R : RawMSSCRecord) (b : Block R.rows.length) (L S I B : ℕ)
    (s : CanonicalFilterStore) (hs : OriginalBlockSemanticInv R b L S I B s) :
    OriginalBlockSemanticInv R b L S I B (realTypeBodyEval (originalBlockThreshold R b) s) := by
  let C := (s.stk (.inr .typeIndex)).length
  obtain ⟨hready, hquery, horig⟩ := realCanonicalType_ready canonicalFilterLayout .rowIndex C L
    (originalBlockThreshold R b) (selectedCallerBase s) hs.operational.scan (selectedCallerExtra s) hs.operational.type_unary
  have hrow := realCanonicalType_extra canonicalFilterLayout .rowIndex C (originalBlockThreshold R b)
    (selectedCallerBase s) (selectedCallerExtra s) CanonicalFilterPort.rowIndex
    (by decide) (by decide) (by decide) (by decide)
  have hblock := realCanonicalType_extra canonicalFilterLayout .rowIndex C (originalBlockThreshold R b)
    (selectedCallerBase s) (selectedCallerExtra s) CanonicalFilterPort.blockCode
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨realTypeBody_invariant L S I _ B s hs.operational, ?_, ?_, ?_⟩
  · change readNormalizedSource ((realCanonicalTypeResult canonicalFilterLayout .rowIndex C
      (originalBlockThreshold R b) (selectedCallerBase s) (selectedCallerExtra s)).stk (.inl (.inr .original))) = _
    rw [horig]; exact hs.parsed
  · change ((realCanonicalTypeResult canonicalFilterLayout .rowIndex C (originalBlockThreshold R b)
      (selectedCallerBase s) (selectedCallerExtra s)).stk (.inr .rowIndex)).length = _
    rw [hrow]; exact hs.row_index
  · change (realCanonicalTypeResult canonicalFilterLayout .rowIndex C (originalBlockThreshold R b)
      (selectedCallerBase s) (selectedCallerExtra s)).stk (.inr .blockCode) = _
    rw [hblock]; exact hs.block_word

theorem originalBlockType_original_output (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (b : Block R.rows.length) (L S I B : ℕ) (s : CanonicalFilterStore)
    (hs : OriginalBlockSemanticInv R b L S I B s) :
    (realTypeBodyEval (originalBlockThreshold R b) s).stk (.inr .output) =
      if rawRowMember R b (s.stk (.inr .typeIndex)).length then
        originalLeafToken (blockCode b) (s.stk (.inr .typeIndex)).length ++ s.stk (.inr .output)
      else s.stk (.inr .output) := by
  let C := (s.stk (.inr .typeIndex)).length
  let m := realBlockMembershipBase C (originalBlockThreshold R b) CanonicalFilterPort.typeIndex .rowIndex
    (selectedCallerBase s) (selectedCallerExtra s)
  let u := extraPortsStore m (selectedCallerExtra s)
  have hm : u.state.2 = rawRowMember R b C :=
    realBlockMembership_original_block .typeIndex .rowIndex C L (originalBlockThreshold R b)
      (selectedCallerBase s) hs.operational.scan (selectedCallerExtra s) hs.operational.type_unary
      R hs.parsed hR b hs.row_index rfl
  have hb : IsUnaryWord (u.stk (.inr .blockCode)) := by
    change IsUnaryWord (s.stk (.inr .blockCode))
    rw [hs.block_word]
    simp [IsUnaryWord]
  have hv : IsUnaryWord (u.stk (.inr .typeIndex)) := hs.operational.type_unary
  have hbytes := acceptedCanonicalLeaf_bytes (callerLeafLayout canonicalFilterLayout) u hb hv
  have hbytes' : (acceptedCanonicalLeafEval (callerLeafLayout canonicalFilterLayout) u).stk (.inr .output) =
      originalLeafToken (blockCode b) C ++ s.stk (.inr .output) := by
    simpa [callerLeafLayout, canonicalFilterLayout, u, extraPortsStore, selectedCallerExtra,
      hs.block_word, originalLeafToken, C, List.append_assoc] using hbytes
  change (canonicalLeafGateEval (callerLeafLayout canonicalFilterLayout) u).stk (.inr .output) = _
  rw [canonicalLeafGate_data, hm, hbytes']
  rfl

/- Validity is exactly the original RawMSSCValid, not a new statistical
or biological assumption. It is a theorem premise for original predicate
identification, to be supplied by the already original validator branch.
Real OR anchor record/row/block data survive repeated actual bodies; the source is not
replaced by an abstract membership oracle or a chosen optimizer order.
-/

end PolytomyReductionModel
