/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Use the SAME actual selected-query/threshold/gate program for every
ORIGINAL block. The anchor selects row m, which is provably out of bounds,
so its real selected query returns false; threshold N then gives exactly
the original anchor predicate. No invented row, modified source or oracle.
-/
import PolytomyActualOriginalRealBlock

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalBlockRowIndex (R : RawMSSCRecord) : Block R.rows.length → ℕ
  | none => R.rows.length
  | some i => i.val

def originalBlockThreshold (R : RawMSSCRecord) : Block R.rows.length → ℕ
  | none => R.N
  | some _ => originalMarkerThreshold R

variable {E : Type} [DecidableEq E]

theorem realBlockMembership_original_block (typePort rowPort : E) (C L T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (extra : E → List Bool) (hC : extra typePort = List.replicate C true)
    (R : RawMSSCRecord) (hparse : readNormalizedSource (s.stk (.inr .original)) = some R)
    (hR : RawMSSCValid R) (b : Block R.rows.length)
    (hrow : (extra rowPort).length = originalBlockRowIndex R b)
    (hT : T = originalBlockThreshold R b) :
    (realBlockMembershipBase C T typePort rowPort s extra).state.2 = rawRowMember R b C := by
  cases b with
  | some i =>
      exact realBlockMembership_original typePort rowPort C L T s hs extra hC R hparse hR i hrow hT
  | none =>
      let u := selectedQueryPreparedBase s (extra typePort) (extra rowPort)
      have hu := selectedQueryPrepared_ready C L s hs (extra typePort) (extra rowPort) hC
      have hq := selectedQuery_verdict C L u hu
      have hoob := selectedRowMembership_oob C R.rows R.rows.length (le_refl _)
      have hq' : (realBlockQueryBase C typePort rowPort s extra).state.2 = false := by
        simpa [u, realBlockQueryBase, selectedQueryPreparedBase, selectedQueryMember, hparse,
          hrow, originalBlockRowIndex, hoob] using hq
      change (realBlockQueryBase C typePort rowPort s extra).state.2 || decide (T ≤ C) = _
      rw [hq', hT]
      simp [originalBlockThreshold, rawRowMember]

/- This common implementation deliberately spends polynomial time on
an out-of-range anchor query rather than assuming a free anchor oracle.
The physical row selector m and threshold N still require actual caller
setup; both are data tapes, not machine-control natural parameters.
-/

end PolytomyReductionModel
