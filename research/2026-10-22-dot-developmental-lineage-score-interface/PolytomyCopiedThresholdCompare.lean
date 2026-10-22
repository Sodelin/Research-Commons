/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual caller-preserving threshold test T<=C. Both operands are copied
from caller tapes into empty scan cap/selector ports, actually subtracted,
then the residual is cleared. All original data and finite frame survive.
-/
import PolytomySelectedQueryParameters

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def thresholdFlagBase (C T : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) :
    CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame :=
  ⟨(s.state.1, decide (T ≤ C)), s.stk⟩

def thresholdCoreRoutine :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (unarySubtractRoutine (.inl .cap) (.inr .queries)) (clearStackRoutine (.inl .cap))

theorem thresholdCore_executes (C T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame)
    (hcap : s.stk (.inl .cap) = []) (hq : s.stk (.inr .queries) = []) :
    thresholdCoreRoutine.Executes
      (selectedQueryPreparedBase s (List.replicate C true) (List.replicate T true))
      (thresholdFlagBase C T s) (T + (C - T) + 2) := by
  let v := frameCallerStore (.inl NumericPort.cap) (.inr UnaryScanPort.queries) s.stk s.state.1
    (decide (T ≤ C)) (List.replicate (C - T) true) []
  have hsub := unarySubtract_executes (.inl NumericPort.cap : NumericStack UnaryScanPort) (.inr .queries)
    (by simp) s.stk s.state.1 s.state.2 C T
  have heq : frameCallerStore (.inl NumericPort.cap) (.inr UnaryScanPort.queries) s.stk s.state.1 s.state.2
      (List.replicate C true) (List.replicate T true) =
      selectedQueryPreparedBase s (List.replicate C true) (List.replicate T true) := by
    cases s with | mk state stk => cases state; rfl
  rw [heq] at hsub
  have hclear := clearStack_executes (.inl NumericPort.cap : NumericStack UnaryScanPort) v
  have hlen : (v.stk (.inl .cap)).length = C - T := by simp [v, frameCallerStore]
  have hresult : clearStackEval (.inl .cap) v = thresholdFlagBase C T s := by
    apply countdownStore_ext
    · rfl
    · funext k
      by_cases hkcap : k = .inl .cap
      · subst k; simp [clearStackEval, thresholdFlagBase, hcap]
      · by_cases hkq : k = .inr .queries
        · subst k; simp [clearStackEval, v, frameCallerStore, thresholdFlagBase, hq]
        · simp [clearStackEval, v, frameCallerStore, thresholdFlagBase, hkcap, hkq]
  rw [hlen, hresult] at hclear
  have h := RoutineComposition.seq_executes _ _ hsub hclear
  simpa only [thresholdCoreRoutine, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

variable {E : Type} [DecidableEq E]

def copiedThresholdRoutine (typePort thresholdPort temp : E) :
    Routine (fun _ : SelectedQueryCallerStack E => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (selectedQueryPrepareRoutine typePort thresholdPort temp)
    (extraPortsRoutine (E := E) thresholdCoreRoutine)

theorem copiedThreshold_executes (typePort thresholdPort temp : E)
    (htt : typePort ≠ temp) (hTt : thresholdPort ≠ temp) (C T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame)
    (hcap : s.stk (.inl .cap) = []) (hq : s.stk (.inr .queries) = [])
    (extra : E → List Bool) (ht : extra temp = [])
    (hC : extra typePort = List.replicate C true) (hT : extra thresholdPort = List.replicate T true) :
    ∃ n ≤ 4 * C + 4 * T + 8,
      (copiedThresholdRoutine typePort thresholdPort temp).Executes (extraPortsStore s extra)
        (extraPortsStore (thresholdFlagBase C T s) extra) n := by
  have hcopy := selectedQueryPrepare_executes typePort thresholdPort temp htt hTt (extraPortsStore s extra) ht
  rw [selectedQueryPrepare_effect typePort thresholdPort s extra hcap hq] at hcopy
  have hcopy' : (selectedQueryPrepareRoutine typePort thresholdPort temp).Executes
      (extraPortsStore s extra)
      (extraPortsStore (selectedQueryPreparedBase s (List.replicate C true) (List.replicate T true)) extra)
      (3 * C + 3 * T + 6) := by
    simpa only [extraPortsStore, hC, hT, List.length_replicate] using hcopy
  have hcore := thresholdCore_executes C T s hcap hq
  have hlift := extraPorts_executes thresholdCoreRoutine
    (selectedQueryPreparedBase s (List.replicate C true) (List.replicate T true))
    (thresholdFlagBase C T s) extra (T + (C - T) + 2) hcore
  have hall := RoutineComposition.seq_executes _ _ hcopy' hlift
  exact ⟨(3 * C + 3 * T + 6) + (T + (C - T) + 2), by omega, hall⟩

/- New-attempt comparison intentionally overwrites the success flag,
including on underflow. The semantic frame and cached guard are preserved
and all data are exactly restored. A caller combining this with another
Boolean result must actually save that result before this call. This is
not a failure-absorbing parser and not an implicit whole-source validator.
-/

end PolytomyReductionModel
