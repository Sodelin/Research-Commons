/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual membership-to-accepted-leaf gate. A false membership is a skipped
type, NOT a parse failure that stops the type countdown. An actual final
atom restores loop success after either branch. Original leaf/cost effects
occur exactly on membership true. The real-block query is composed below.
-/
import PolytomyOriginalBlockMembership

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K E F : Type} [DecidableEq K] [DecidableEq E]

def canonicalContinueOp : Op K Bool (CountdownState F) := .load (fun s => (s.1, true))

def canonicalLeafGateRoutine (p : CanonicalLeafLayout K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq
    (RoutineControl.branch Prod.snd (acceptedCanonicalLeafRoutine p) (Atom.routine cleanupNoop))
    (Atom.routine canonicalContinueOp)

def canonicalLeafGateEval (p : CanonicalLeafLayout K) (s : CountdownStore K F) :=
  canonicalContinueOp.apply (if s.state.2 then acceptedCanonicalLeafEval p s else s)

theorem canonicalLeafGate_executes (p : CanonicalLeafLayout K) (s : CountdownStore K F)
    (ht : s.stk (p.port .temp) = []) :
    ∃ n ≤ 3 * (s.stk (p.port .remaining)).length + 3 * (s.stk (p.port .value)).length +
      3 * (s.stk (p.port .block)).length + 18,
      (canonicalLeafGateRoutine p).Executes s (canonicalLeafGateEval p s) n := by
  cases hf : s.state.2 with
  | false =>
      have hnoop := Atom.executes (cleanupNoop (K := K) (F := F)) s
      have hb := RoutineControl.branch_false Prod.snd (acceptedCanonicalLeafRoutine p)
        (Atom.routine cleanupNoop) hf hnoop
      have h := RoutineComposition.seq_executes _ _ hb (Atom.executes canonicalContinueOp s)
      exact ⟨3, by omega, by simpa [canonicalLeafGateRoutine, canonicalLeafGateEval, hf, cleanupNoop, Op.apply] using h⟩
  | true =>
      obtain ⟨n, hn, he⟩ := acceptedCanonicalLeaf_executes p s ht
      have hb := RoutineControl.branch_true Prod.snd (acceptedCanonicalLeafRoutine p)
        (Atom.routine cleanupNoop) hf he
      have h := RoutineComposition.seq_executes _ _ hb
        (Atom.executes canonicalContinueOp (acceptedCanonicalLeafEval p s))
      exact ⟨(n + 1) + 1, by omega, by simpa [canonicalLeafGateRoutine, canonicalLeafGateEval, hf] using h⟩

theorem canonicalLeafGate_success (p : CanonicalLeafLayout K) (s : CountdownStore K F) :
    (canonicalLeafGateEval p s).state.2 = true := by
  simp [canonicalLeafGateEval, canonicalContinueOp, Op.apply]

theorem canonicalLeafGate_data (p : CanonicalLeafLayout K) (s : CountdownStore K F) (k : K) :
    (canonicalLeafGateEval p s).stk k =
      if s.state.2 then (acceptedCanonicalLeafEval p s).stk k else s.stk k := by
  cases hf : s.state.2 <;> simp [canonicalLeafGateEval, canonicalContinueOp, Op.apply, hf]

theorem canonicalLeafGate_extra (p : CanonicalLeafLayout K) (s : CountdownStore K F) (k : K)
    (hkr : k ≠ p.port .remaining) (hkc : k ≠ p.port .count)
    (hkcost : k ≠ p.port .cost) (hko : k ≠ p.port .output) :
    (canonicalLeafGateEval p s).stk k = s.stk k := by
  rw [canonicalLeafGate_data]
  split
  · exact acceptedCanonicalLeaf_extra p s k hkr hkc hkcost hko
  · rfl

def callerLeafLayout (p : CanonicalLeafLayout E) : CanonicalLeafLayout (SelectedQueryCallerStack E) where
  port a := .inr (p.port a)
  injective := fun _ _ h => p.injective (Sum.inr.inj h)

def realCanonicalTypeRoutine (p : CanonicalLeafLayout E) (rowPort thresholdPort : E) :
    Routine (fun _ : SelectedQueryCallerStack E => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (realBlockMembershipRoutine (p.port .value) rowPort thresholdPort (p.port .temp))
    (canonicalLeafGateRoutine (callerLeafLayout p))

def realCanonicalTypeResult (p : CanonicalLeafLayout E) (rowPort : E) (C T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool) :=
  canonicalLeafGateEval (callerLeafLayout p)
    (extraPortsStore (realBlockMembershipBase C T (p.port .value) rowPort s extra) extra)

theorem realCanonicalType_executes (p : CanonicalLeafLayout E) (rowPort thresholdPort : E)
    (hrt : rowPort ≠ p.port .temp) (hTt : thresholdPort ≠ p.port .temp) (C L T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) (extra : E → List Bool)
    (ht : extra (p.port .temp) = []) (hC : extra (p.port .value) = List.replicate C true)
    (hT : extra thresholdPort = List.replicate T true) :
    ∃ n ≤ realBlockMembershipBound C L (extra rowPort).length T +
      3 * (extra (p.port .remaining)).length + 3 * C + 3 * (extra (p.port .block)).length + 18,
      (realCanonicalTypeRoutine p rowPort thresholdPort).Executes (extraPortsStore s extra)
        (realCanonicalTypeResult p rowPort C T s extra) n ∧
      (realCanonicalTypeResult p rowPort C T s extra).state.2 = true := by
  obtain ⟨n, hn, he, hflag, hready, hclear, hpres⟩ := realBlockMembership_executes
    (p.port .value) rowPort thresholdPort (p.port .temp) (p.ne (by decide)) hrt hTt
    C L T s hs hq extra ht hC hT
  obtain ⟨m, hm, hgate⟩ := canonicalLeafGate_executes (callerLeafLayout p)
    (extraPortsStore (realBlockMembershipBase C T (p.port .value) rowPort s extra) extra) ht
  have hm' : m ≤ 3 * (extra (p.port .remaining)).length + 3 * C + 3 * (extra (p.port .block)).length + 18 := by
    simpa [callerLeafLayout, extraPortsStore, hC] using hm
  exact ⟨n + m, by omega, RoutineComposition.seq_executes _ _ he hgate,
    canonicalLeafGate_success _ _⟩

theorem realCanonicalType_original_gate (p : CanonicalLeafLayout E) (rowPort : E) (C L T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (extra : E → List Bool) (hC : extra (p.port .value) = List.replicate C true)
    (R : RawMSSCRecord) (hparse : readNormalizedSource (s.stk (.inr .original)) = some R)
    (hR : RawMSSCValid R) (i : Fin R.rows.length) (hrow : (extra rowPort).length = i.val)
    (hT : T = R.N + privateCount R.N R.rows.length) (k : SelectedQueryCallerStack E) :
    (realCanonicalTypeResult p rowPort C T s extra).stk k =
      if rawRowMember R (some i) C then
        (acceptedCanonicalLeafEval (callerLeafLayout p)
          (extraPortsStore (realBlockMembershipBase C T (p.port .value) rowPort s extra) extra)).stk k
      else (extraPortsStore (realBlockMembershipBase C T (p.port .value) rowPort s extra) extra).stk k := by
  rw [realCanonicalTypeResult, canonicalLeafGate_data]
  rw [show (extraPortsStore (realBlockMembershipBase C T (p.port .value) rowPort s extra) extra).state.2 =
      rawRowMember R (some i) C from
    realBlockMembership_original (p.port .value) rowPort C L T s hs extra hC R hparse hR i hrow hT]

/- The generic gate's membership premise is instantiated above by the
actual copied-parameter selected query and actual copied threshold test.
An original-validity proof is required only for the semantic equality to
rawRowMember, not supplied as a machine witness. No optimizer is called.
The complete descending type-loop invariant/ordered filter fold, anchor
case, physical threshold setup, block loop/serializer and full finite
machine packaging remain to join; this component is not the whole claim.
-/

end PolytomyReductionModel
