/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact original unary-frame semantics of the actual identifier visitor.
All accumulator data are finite control; the unbounded query remains on
the physical cap tape. Match and nonmatch are both successful parses.
-/
import PolytomyUnaryIdentifierVisitor

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem unaryVisitFinish_result (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C D : ℕ) (base : K → List Bool)
    (hm : base p.m = List.replicate D true) (hl : base p.l = [])
    (frame : F) (guard flag : Bool) (bits : List Bool) :
    unaryVisitFinishEval p mode bump C
      (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] []) =
      numericStore (Function.update base p.m [])
        (bump frame (unaryVisitTest mode C D), guard) true bits [] (List.replicate C true) [] [] := by
  apply countdownStore_ext
  · simpa [unaryVisitFinishEval, unaryVisitSubtractEval, unaryVisitDecisionOp,
      clearManyEval, clearStackEval, Op.apply, numericStore, numericStacks, hm]
      using congrArg (fun b => ((bump frame b, guard), true)) (unaryVisit_test_residual mode C D)
  · funext k
    cases k with
    | inl q => cases q <;> rfl
    | inr k =>
        by_cases hkm : k = p.m <;> by_cases hkl : k = p.l <;>
          simp_all [unaryVisitFinishEval, unaryVisitSubtractEval, unaryVisitDecisionOp,
            clearManyEval, clearStackEval, Op.apply, numericStore, numericStacks]

def unaryIdentifierResult (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C : ℕ) (base : K → List Bool) (frame : F) (guard flag : Bool) (bits : List Bool) :
    CountdownStore (NumericStack K) F :=
  if flag then
    match readUnaryFrame bits with
    | none => numericStore base (frame, guard) false [] [] (List.replicate C true) [] []
    | some (D, rest) => numericStore base (bump frame (unaryVisitTest mode C D), guard)
        true rest [] (List.replicate C true) [] []
  else numericStore base (frame, guard) false bits [] (List.replicate C true) [] []

theorem unaryIdentifier_result (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C : ℕ) (base : K → List Bool)
    (hm : base p.m = []) (hl : base p.l = [])
    (frame : F) (guard flag : Bool) (bits : List Bool) :
    unaryIdentifierEval p mode bump C
      (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] []) =
      unaryIdentifierResult mode bump C base frame guard flag bits := by
  cases flag with
  | false => simp [unaryIdentifierEval, guardedUnaryFieldEval, unaryIdentifierResult, numericStore]
  | true =>
      cases hp : readUnaryFrame bits with
      | none =>
          apply countdownStore_ext
          · simp [unaryIdentifierEval, guardedUnaryFieldEval, unaryIdentifierResult, hp,
              unaryCallerResult, frameCallerStore, numericStore, numericStacks]
          · funext k
            cases k with
            | inl q => cases q <;> simp [unaryIdentifierEval, guardedUnaryFieldEval,
                unaryIdentifierResult, hp, unaryCallerResult, frameCallerStore, numericStore, numericStacks]
            | inr k => by_cases hk : k = p.m <;>
                simp_all [unaryIdentifierEval, guardedUnaryFieldEval, unaryIdentifierResult,
                  hp, unaryCallerResult, frameCallerStore, numericStore, numericStacks]
      | some q =>
          rcases q with ⟨D, rest⟩
          let readStore := numericStore (Function.update base p.m (List.replicate D true))
            (frame, guard) true rest [] (List.replicate C true) [] []
          have hread : guardedUnaryFieldEval (.inl .source) (.inr p.m)
              (numericStore base (frame, guard) true bits [] (List.replicate C true) [] []) = readStore := by
            apply countdownStore_ext
            · simp [guardedUnaryFieldEval, hp, unaryCallerResult, frameCallerStore, readStore, numericStore, numericStacks]
            · funext k
              cases k with
              | inl q => cases q <;> simp [guardedUnaryFieldEval, hp, unaryCallerResult,
                  frameCallerStore, readStore, numericStore, numericStacks]
              | inr k => by_cases hk : k = p.m <;> simp [guardedUnaryFieldEval, hp,
                  unaryCallerResult, frameCallerStore, readStore, numericStore, numericStacks, hk]
          rw [unaryIdentifierEval, hread]
          simp only [readStore, numericStore, Bool.true_eq_true, ↓reduceIte]
          have hfinish := unaryVisitFinish_result p mode bump C D
            (Function.update base p.m (List.replicate D true)) (by simp)
            (by simpa [p.hlm] using hl) frame guard true rest
          have hrestore : Function.update (Function.update base p.m (List.replicate D true)) p.m [] = base := by
            funext k; by_cases hk : k = p.m <;> simp_all
          rw [hrestore] at hfinish
          simpa [unaryIdentifierResult, hp] using hfinish

theorem unaryIdentifier_invariant (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : UnaryVisitInv p C L s) : UnaryVisitInv p C L (unaryIdentifierEval p mode bump C s) := by
  rw [numericLoop_reconstruct C L s hs.1, unaryIdentifier_result p mode bump C
    (fun k => s.stk (.inr k)) hs.2.1 hs.2.2.2.1]
  cases hf : s.state.2 with
  | false =>
      simpa [unaryIdentifierResult, hf, UnaryVisitInv, NumericLoopInv, numericStore, numericStacks]
        using And.intro hs.1.2.2.2.2 hs.2
  | true =>
      cases hp : readUnaryFrame (s.stk (.inl .source)) with
      | none =>
          simpa [unaryIdentifierResult, hf, hp, UnaryVisitInv, NumericLoopInv, numericStore, numericStacks]
            using And.intro (Nat.zero_le L) hs.2
      | some q =>
          rcases q with ⟨D, rest⟩
          have hc := readUnaryFrame_consumption (s.stk (.inl .source)) D rest hp
          have hb := hs.1.2.2.2.2
          have hrest : rest.length ≤ L := by omega
          simpa [unaryIdentifierResult, hf, hp, UnaryVisitInv, NumericLoopInv, numericStore, numericStacks]
            using And.intro hrest hs.2

theorem unaryIdentifier_extra (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : UnaryVisitInv p C L s) (k : K) :
    (unaryIdentifierEval p mode bump C s).stk (.inr k) = s.stk (.inr k) := by
  rw [numericLoop_reconstruct C L s hs.1, unaryIdentifier_result p mode bump C
    (fun k => s.stk (.inr k)) hs.2.1 hs.2.2.2.1]
  cases hf : s.state.2 <;> cases hp : readUnaryFrame (s.stk (.inl .source)) <;>
    simp [unaryIdentifierResult, hf, hp, numericStore, numericStacks]

def unaryVisitObservation (s : CountdownStore (NumericStack K) F) : Option (List Bool × F) :=
  if s.state.2 then some (s.stk (.inl .source), s.state.1.1) else none

theorem unaryIdentifier_observation (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : UnaryVisitInv p C L s) :
    unaryVisitObservation (unaryIdentifierEval p mode bump C s) =
      if s.state.2 then (readUnaryFrame (s.stk (.inl .source))).map
        (fun q => (q.2, bump s.state.1.1 (unaryVisitTest mode C q.1))) else none := by
  rw [numericLoop_reconstruct C L s hs.1, unaryIdentifier_result p mode bump C
    (fun k => s.stk (.inr k)) hs.2.1 hs.2.2.2.1]
  cases hf : s.state.2 <;> cases hp : readUnaryFrame (s.stk (.inl .source)) <;>
    simp [unaryVisitObservation, unaryIdentifierResult, hf, hp, numericStore, numericStacks]

/- Every extra port, including the physical original record, scalar
headers and reserved counters, is unchanged at visitor boundaries under
the stated clean-scratch invariant. Parsing failure still may consume the
remaining source; that failure is observable and is not a semantic nonmatch.
-/

end PolytomyReductionModel
