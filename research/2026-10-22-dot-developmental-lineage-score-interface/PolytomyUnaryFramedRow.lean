/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original internal row: unary count read to a physical counter,
then actual unary identifier visits. The exact readFramedList observation
retains the source suffix and accumulated result, including empty rows.
-/
import PolytomyUnaryIdentifierList

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def unaryFramedRowRoutine (p : UnaryVisitPorts K) (c : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (guardedUnaryFieldRoutine (.inl .source) (.inr c))
    (unaryIdentifierListRoutine p c mode bump)

def unaryFramedRowEval (p : UnaryVisitPorts K) (c : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C : ℕ) (s : CountdownStore (NumericStack K) F) :=
  unaryIdentifierListEval p c mode bump C (guardedUnaryFieldEval (.inl .source) (.inr c) s)

def unaryFramedRowBound (C L : ℕ) := L * (7 * C + 10 * L + 25) + 2 * L + 7

theorem unaryFramedRow_executes (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) (hempty : s.stk (.inr c) = []) :
    ∃ n ≤ unaryFramedRowBound C L,
      (unaryFramedRowRoutine p c mode bump).Executes s (unaryFramedRowEval p c mode bump C s) n ∧
      UnaryVisitInv p C L (unaryFramedRowEval p c mode bump C s) ∧
      (unaryFramedRowEval p c mode bump C s).state.1.2 = false ∧
      ((unaryFramedRowEval p c mode bump C s).state.2 = true →
        (unaryFramedRowEval p c mode bump C s).stk (.inr c) = []) := by
  let u := guardedUnaryFieldEval (.inl .source) (.inr c) s
  obtain ⟨n, hn, he⟩ := guardedUnaryField_executes (.inl .source : NumericStack K) (.inr c)
    (by simp) s hempty L hs.1.2.2.2.2
  have hu := unaryField_visit_invariant p c hc C L s hs
  have hlen := (guardedUnaryField_output_bound (.inl .source : NumericStack K) (.inr c) s hempty).trans hs.1.2.2.2.2
  obtain ⟨m, hm, hloop, hi, hg, hz⟩ := unaryIdentifierList_executes p c hc mode bump C L u hu
  have hmul := Nat.mul_le_mul_right (7 * C + 10 * L + 25) hlen
  exact ⟨n + m, by unfold unaryFramedRowBound; omega,
    RoutineComposition.seq_executes _ _ he hloop, hi, hg, hz⟩

theorem unaryFramedRow_observation (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) :
    unaryVisitObservation (unaryFramedRowEval p c mode bump C s) =
      if s.state.2 then (readFramedList readUnaryFrame (s.stk (.inl .source))).map
        (fun q => (q.2, q.1.foldl (unaryVisitStep mode bump C) s.state.1.1)) else none := by
  rw [unaryFramedRowEval, unaryIdentifierList_observation p c hc mode bump C L _
    (unaryField_visit_invariant p c hc C L s hs)]
  cases hf : s.state.2 with
  | false => simp [guardedUnaryFieldEval, hf]
  | true =>
      cases hp : readUnaryFrame (s.stk (.inl .source)) with
      | none => simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore, readFramedList]
      | some q =>
          rcases q with ⟨n, rest⟩
          simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore, readFramedList]

theorem unaryFramedRow_extra (p : UnaryVisitPorts K) (c k : K) (hc : UnaryVisitOutside p c)
    (hkc : k ≠ c) (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) :
    (unaryFramedRowEval p c mode bump C s).stk (.inr k) = s.stk (.inr k) := by
  rw [unaryFramedRowEval, unaryIdentifierList_extra p c k hc hkc mode bump C L _
    (unaryField_visit_invariant p c hc C L s hs)]
  exact guardedUnaryField_extra _ _ _ (by simp) (by simpa using hkc) s

end PolytomyReductionModel
