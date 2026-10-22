/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual copied-parameter selected-row query plus real shared-marker
threshold test. The ORIGINAL source-validity guard justifies dropping
only the redundant n<N conjunct inside true selected-row membership.
It does not justify replacing a selected row by the flattened record.
-/
import PolytomyCopiedThresholdCompare

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem rawRowMember_valid_selected (R : RawMSSCRecord) (hR : RawMSSCValid R)
    (i : Fin R.rows.length) (C : ℕ) :
    rawRowMember R (some i) C = decide (C ∈ R.rows.get i) ||
      decide (R.N + privateCount R.N R.rows.length ≤ C) := by
  by_cases hm : C ∈ R.rows.get i
  · have hlt : C < R.N := hR.2.1 C
      (List.mem_flatten.mpr ⟨R.rows.get i, List.get_mem R.rows i, hm⟩)
    simp [rawRowMember, hm, hlt]
  · simp [rawRowMember, hm]

variable {K E : Type} [DecidableEq K] [DecidableEq E]

def saveSelectedQueryOp : Op K Bool (CountdownState SelectedRowFrame) :=
  .load (fun s => ((⟨s.2, s.1.1.chosen, s.1.1.active⟩, s.1.2), s.2))

def joinMarkerVerdictOp : Op K Bool (CountdownState SelectedRowFrame) :=
  .load (fun s => (s.1, s.1.1.found || s.2))

def realBlockMembershipRoutine (typePort rowPort thresholdPort temp : E) :
    Routine (fun _ : SelectedQueryCallerStack E => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (copiedSelectedQueryRoutine typePort rowPort temp)
    (RoutineComposition.seq (Atom.routine saveSelectedQueryOp)
      (RoutineComposition.seq (copiedThresholdRoutine typePort thresholdPort temp)
        (Atom.routine joinMarkerVerdictOp)))

def realBlockQueryBase (C : ℕ) (typePort rowPort : E)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool) :=
  selectedQueryEval C (selectedQueryPreparedBase s (extra typePort) (extra rowPort))

def realBlockMembershipBase (C T : ℕ) (typePort rowPort : E)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool) :=
  joinMarkerVerdictOp.apply (thresholdFlagBase C T
    (saveSelectedQueryOp.apply (realBlockQueryBase C typePort rowPort s extra)))

def realBlockMembershipBound (C L I T : ℕ) :=
  selectedQueryBound C L I + 7 * C + 3 * I + 4 * T + 16

theorem realBlockMembership_executes (typePort rowPort thresholdPort temp : E)
    (htt : typePort ≠ temp) (hrt : rowPort ≠ temp) (hTt : thresholdPort ≠ temp) (C L T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) (extra : E → List Bool)
    (ht : extra temp = []) (hC : extra typePort = List.replicate C true)
    (hT : extra thresholdPort = List.replicate T true) :
    ∃ n ≤ realBlockMembershipBound C L (extra rowPort).length T,
      (realBlockMembershipRoutine typePort rowPort thresholdPort temp).Executes
        (extraPortsStore s extra) (extraPortsStore (realBlockMembershipBase C T typePort rowPort s extra) extra) n ∧
      (realBlockMembershipBase C T typePort rowPort s extra).state.2 =
        (selectedQueryMember C (extra rowPort).length (s.stk (.inr .original)) || decide (T ≤ C)) ∧
      UnaryScanReady 0 L (realBlockMembershipBase C T typePort rowPort s extra) ∧
      (realBlockMembershipBase C T typePort rowPort s extra).stk (.inr .queries) = [] ∧
      (realBlockMembershipBase C T typePort rowPort s extra).stk (.inr .original) = s.stk (.inr .original) := by
  let q := realBlockQueryBase C typePort rowPort s extra
  let a := saveSelectedQueryOp.apply q
  obtain ⟨n, hn, he, hflag, hextra⟩ := copiedSelectedQuery_executes typePort rowPort temp htt hrt C L s hs hq extra ht hC
  obtain ⟨hready, hclear, horig⟩ := copiedSelectedQuery_ready typePort rowPort C L s hs extra hC
  have hcap : a.stk (.inl .cap) = [] := by simpa using hready.numeric.2.2.2.1
  have haquery : a.stk (.inr .queries) = [] := hclear
  have hsave : (Atom.routine (saveSelectedQueryOp (K := SelectedQueryCallerStack E))).Executes
      (extraPortsStore q extra) (extraPortsStore a extra) 1 := Atom.executes saveSelectedQueryOp _
  obtain ⟨m, hm, hcompare⟩ := copiedThreshold_executes typePort thresholdPort temp htt hTt C T a
    hcap haquery extra ht hC hT
  have hjoin : (Atom.routine (joinMarkerVerdictOp (K := SelectedQueryCallerStack E))).Executes
      (extraPortsStore (thresholdFlagBase C T a) extra)
      (extraPortsStore (realBlockMembershipBase C T typePort rowPort s extra) extra) 1 :=
    Atom.executes joinMarkerVerdictOp _
  have hlast := RoutineComposition.seq_executes _ _ hcompare hjoin
  have htail := RoutineComposition.seq_executes _ _ hsave hlast
  have hall := RoutineComposition.seq_executes _ _ he htail
  refine ⟨n + (1 + (m + 1)), by unfold realBlockMembershipBound; omega, hall, ?_, ?_, hclear, horig⟩
  · change q.state.2 || decide (T ≤ C) = _
    have hqflag : q.state.2 = selectedQueryMember C (extra rowPort).length (s.stk (.inr .original)) := hflag
    rw [hqflag]
  · exact ⟨hready.numeric, hready.source_empty, hready.empty, hready.original_bound⟩

theorem realBlockMembership_original (typePort rowPort : E) (C L T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (extra : E → List Bool) (hC : extra typePort = List.replicate C true)
    (R : RawMSSCRecord) (hparse : readNormalizedSource (s.stk (.inr .original)) = some R)
    (hR : RawMSSCValid R) (i : Fin R.rows.length) (hrow : (extra rowPort).length = i.val)
    (hT : T = R.N + privateCount R.N R.rows.length) :
    (realBlockMembershipBase C T typePort rowPort s extra).state.2 = rawRowMember R (some i) C := by
  let u := selectedQueryPreparedBase s (extra typePort) (extra rowPort)
  have hu := selectedQueryPrepared_ready C L s hs (extra typePort) (extra rowPort) hC
  have hq := selectedQuery_verdict C L u hu
  have hq' : (realBlockQueryBase C typePort rowPort s extra).state.2 = decide (C ∈ R.rows.get i) := by
    simpa [u, realBlockQueryBase, selectedQueryPreparedBase, selectedQueryMember, hparse, hrow,
      selectedRowMembership_get C R.rows i.val i.isLt] using hq
  change (realBlockQueryBase C typePort rowPort s extra).state.2 || decide (T ≤ C) = _
  rw [hq', hT, rawRowMember_valid_selected R hR i C]

theorem anchorBlockMembership_original (R : RawMSSCRecord) (C : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) :
    (thresholdFlagBase C R.N s).state.2 = rawRowMember R none C := rfl

/- Real-block arithmetic deliberately saves the completed query VERDICT,
not a possibly stale partial found bit. Its total function is queryMember
OR markerThreshold, even on malformed records. Equality to ORIGINAL block
membership is claimed only after the ORIGINAL source validity guard. The
anchor is the same actual copied threshold routine with threshold N.
Physical N/product/threshold creation, valid-source branching, complete
canonical enumeration/accepted-leaf gating, serialization and packaging
remain open, alongside checker/hardness/toolchain/axiom/kernel checks.
-/

end PolytomyReductionModel
