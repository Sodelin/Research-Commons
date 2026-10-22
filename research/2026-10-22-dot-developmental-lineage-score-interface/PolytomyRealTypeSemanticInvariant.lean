/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Original-valid-source semantic invariant for the actual real-type loop.
It fixes the preserved record, selected row and original block code as
physical data; none of these are supplied as machine-control witnesses.
-/
import PolytomyActualRealTypeLoop

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalMarkerThreshold (R : RawMSSCRecord) := R.N + privateCount R.N R.rows.length

def originalLeafToken (block typeCode : ℕ) : List Bool :=
  true :: (unaryFrame block ++ unaryFrame typeCode)

structure RealTypeSemanticInv (R : RawMSSCRecord) (i : Fin R.rows.length)
    (L S I B : ℕ) (s : CanonicalFilterStore) : Prop where
  operational : RealTypeLoopInv L S I (originalMarkerThreshold R) B s
  parsed : readNormalizedSource (s.stk (.inl (.inr .original))) = some R
  row_index : (s.stk (.inr .rowIndex)).length = i.val
  block_word : s.stk (.inr .blockCode) = List.replicate (blockCode (some i)) true

theorem RealTypeSemanticInv_of_stacks (R : RawMSSCRecord) (i : Fin R.rows.length)
    (L S I B : ℕ) (s t : CanonicalFilterStore) (hs : RealTypeSemanticInv R i L S I B s)
    (h : ∀ k, t.stk k = s.stk k) : RealTypeSemanticInv R i L S I B t := by
  refine ⟨RealTypeLoopInv_of_stacks L S I _ B s t hs.operational h, ?_, ?_, ?_⟩
  · rw [h]; exact hs.parsed
  · rw [h]; exact hs.row_index
  · rw [h]; exact hs.block_word

theorem realTypeSemantic_pop (R : RawMSSCRecord) (i : Fin R.rows.length) (L S I B : ℕ)
    (s : CanonicalFilterStore) (hs : RealTypeSemanticInv R i L S I B s) :
    RealTypeSemanticInv R i L S I B (countdownPop (.inr .typeIndex) s) := by
  refine ⟨realTypeLoop_pop_invariant L S I _ B s hs.operational, ?_, ?_, ?_⟩
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.parsed
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.row_index
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.block_word

theorem realTypeSemantic_body (R : RawMSSCRecord) (i : Fin R.rows.length) (L S I B : ℕ)
    (s : CanonicalFilterStore) (hs : RealTypeSemanticInv R i L S I B s) :
    RealTypeSemanticInv R i L S I B (realTypeBodyEval (originalMarkerThreshold R) s) := by
  let C := (s.stk (.inr .typeIndex)).length
  obtain ⟨hready, hquery, horig⟩ := realCanonicalType_ready canonicalFilterLayout .rowIndex C L
    (originalMarkerThreshold R) (selectedCallerBase s) hs.operational.scan (selectedCallerExtra s) hs.operational.type_unary
  have hrow := realCanonicalType_extra canonicalFilterLayout .rowIndex C (originalMarkerThreshold R)
    (selectedCallerBase s) (selectedCallerExtra s) CanonicalFilterPort.rowIndex
    (by decide) (by decide) (by decide) (by decide)
  have hblock := realCanonicalType_extra canonicalFilterLayout .rowIndex C (originalMarkerThreshold R)
    (selectedCallerBase s) (selectedCallerExtra s) CanonicalFilterPort.blockCode
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨realTypeBody_invariant L S I _ B s hs.operational, ?_, ?_, ?_⟩
  · change readNormalizedSource ((realCanonicalTypeResult canonicalFilterLayout .rowIndex C
      (originalMarkerThreshold R) (selectedCallerBase s) (selectedCallerExtra s)).stk (.inl (.inr .original))) = _
    rw [horig]; exact hs.parsed
  · change ((realCanonicalTypeResult canonicalFilterLayout .rowIndex C (originalMarkerThreshold R)
      (selectedCallerBase s) (selectedCallerExtra s)).stk (.inr .rowIndex)).length = _
    rw [hrow]; exact hs.row_index
  · change (realCanonicalTypeResult canonicalFilterLayout .rowIndex C (originalMarkerThreshold R)
      (selectedCallerBase s) (selectedCallerExtra s)).stk (.inr .blockCode) = _
    rw [hblock]; exact hs.block_word

theorem realTypeBody_original_output (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (L S I B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeSemanticInv R i L S I B s) :
    (realTypeBodyEval (originalMarkerThreshold R) s).stk (.inr .output) =
      if rawRowMember R (some i) (s.stk (.inr .typeIndex)).length then
        originalLeafToken (blockCode (some i)) (s.stk (.inr .typeIndex)).length ++ s.stk (.inr .output)
      else s.stk (.inr .output) := by
  let C := (s.stk (.inr .typeIndex)).length
  let m := realBlockMembershipBase C (originalMarkerThreshold R) CanonicalFilterPort.typeIndex .rowIndex
    (selectedCallerBase s) (selectedCallerExtra s)
  let u := extraPortsStore m (selectedCallerExtra s)
  have hm : u.state.2 = rawRowMember R (some i) C :=
    realBlockMembership_original .typeIndex .rowIndex C L (originalMarkerThreshold R)
      (selectedCallerBase s) hs.operational.scan (selectedCallerExtra s) hs.operational.type_unary
      R hs.parsed hR i hs.row_index rfl
  have hb : IsUnaryWord (u.stk (.inr .blockCode)) := by
    change IsUnaryWord (s.stk (.inr .blockCode))
    rw [hs.block_word]
    simp [IsUnaryWord]
  have hv : IsUnaryWord (u.stk (.inr .typeIndex)) := hs.operational.type_unary
  have hbytes := acceptedCanonicalLeaf_bytes (callerLeafLayout canonicalFilterLayout) u hb hv
  have hbytes' : (acceptedCanonicalLeafEval (callerLeafLayout canonicalFilterLayout) u).stk (.inr .output) =
      originalLeafToken (blockCode (some i)) C ++ s.stk (.inr .output) := by
    simpa [callerLeafLayout, canonicalFilterLayout, u, extraPortsStore, selectedCallerExtra,
      hs.block_word, originalLeafToken, C, List.append_assoc] using hbytes
  change (canonicalLeafGateEval (callerLeafLayout canonicalFilterLayout) u).stk (.inr .output) = _
  rw [canonicalLeafGate_data, hm, hbytes']
  rfl

/- Validity is exactly the original RawMSSCValid, not a new statistical
or biological assumption. It is a theorem premise for original predicate
identification, to be supplied by the already original validator branch.
Record/row/block data survive repeated actual bodies; the source is not
replaced by an abstract membership oracle or a chosen optimizer order.
-/

end PolytomyReductionModel
