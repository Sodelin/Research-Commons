/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual internal-unary identifier visitor. A comparison nonmatch updates
the finite accumulator but restores syntactic success; only malformed
input stops traversal. The query is a physical unary cap, never Nat
stored in finite control. Arbitrary finite accumulator updates are allowed.
-/
import PolytomyGuardedUnaryField
import PolytomyPreservingUnaryCompare

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

structure UnaryVisitPorts (K : Type) where
  m : K
  t : K
  l : K
  r : K
  hmt : m ≠ t
  hlm : l ≠ m
  hlt : l ≠ t
  hlr : l ≠ r
  hrm : r ≠ m
  hrt : r ≠ t

inductive UnaryVisitMode where
  | equal
  | less
  deriving DecidableEq, Fintype

def unaryVisitTest : UnaryVisitMode → ℕ → ℕ → Bool
  | .equal, C, D => decide (D = C)
  | .less, C, D => decide (D < C)

def unaryVisitDecisionOp (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) : Op (NumericStack K) Bool (CountdownState F) :=
  .peek (.inr p.l) (fun s h =>
    ((bump s.1.1 (s.2 && match mode with
      | .equal => h.isNone
      | .less => h.isSome), s.1.2), true))

def unaryVisitFinishRoutine (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (preservingUnarySubtractRoutine p.m p.t p.l p.r)
    (RoutineComposition.seq (Atom.routine (unaryVisitDecisionOp p mode bump))
      (clearManyRoutine [.inr p.m, .inr p.l]))

def unaryIdentifierRoutine (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (guardedUnaryFieldRoutine (.inl .source) (.inr p.m))
    (RoutineControl.branch Prod.snd (unaryVisitFinishRoutine p mode bump) (Atom.routine cleanupNoop))

def unaryVisitSubtractEval (p : UnaryVisitPorts K) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  let D := (s.stk (.inr p.m)).length
  numericStore (Function.update (fun k => s.stk (.inr k)) p.l (List.replicate (C - D) true))
    s.state.1 (decide (D ≤ C)) (s.stk (.inl .source)) [] (List.replicate C true) [] []

def unaryVisitFinishEval (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C : ℕ) (s : CountdownStore (NumericStack K) F) :=
  clearManyEval [.inr p.m, .inr p.l]
    ((unaryVisitDecisionOp p mode bump).apply (unaryVisitSubtractEval p C s))

def unaryIdentifierEval (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C : ℕ) (s : CountdownStore (NumericStack K) F) :=
  let u := guardedUnaryFieldEval (.inl .source) (.inr p.m) s
  if u.state.2 then unaryVisitFinishEval p mode bump C u else u

def UnaryVisitInv (p : UnaryVisitPorts K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) : Prop :=
  NumericLoopInv C L s ∧ s.stk (.inr p.m) = [] ∧ s.stk (.inr p.t) = [] ∧
    s.stk (.inr p.l) = [] ∧ s.stk (.inr p.r) = []

theorem unaryField_numeric_invariant (m : K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s) :
    NumericLoopInv C L (guardedUnaryFieldEval (.inl .source) (.inr m) s) := by
  have hb := guardedUnaryField_source_bound (.inl .source : NumericStack K) (.inr m) (by simp) s
  cases hf : s.state.2 with
  | false => simpa [guardedUnaryFieldEval, hf] using hs
  | true =>
      cases hp : readUnaryFrame (s.stk (.inl .source)) with
      | none =>
          simpa [guardedUnaryFieldEval, hf, hp, NumericLoopInv, unaryCallerResult, frameCallerStore]
            using And.intro hs.1 (And.intro hs.2.1 (And.intro hs.2.2.1 (And.intro hs.2.2.2.1 (Nat.zero_le L))))
      | some q =>
          rcases q with ⟨D, rest⟩
          have hrest := (readUnaryFrame_consumption (s.stk (.inl .source)) D rest hp)
          have hsource := hs.2.2.2.2
          have hlen : rest.length ≤ L := by omega
          simpa [guardedUnaryFieldEval, hf, hp, NumericLoopInv, unaryCallerResult, frameCallerStore]
            using And.intro hs.1 (And.intro hs.2.1 (And.intro hs.2.2.1 (And.intro hs.2.2.2.1 hlen)))

theorem unaryVisit_test_residual (mode : UnaryVisitMode) (C D : ℕ) :
    (decide (D ≤ C) && match mode with
      | .equal => (List.replicate (C - D) true).head?.isNone
      | .less => (List.replicate (C - D) true).head?.isSome) = unaryVisitTest mode C D := by
  cases mode with
  | equal =>
      by_cases hle : D ≤ C
      · by_cases heq : D = C
        · subst D; simp [unaryVisitTest]
        · cases hn : C - D with
          | zero => omega
          | succ n => simp [unaryVisitTest, hle, heq, hn]
      · have hne : D ≠ C := by omega
        simp [unaryVisitTest, hle, hne]
  | less =>
      by_cases hlt : D < C
      · have hle : D ≤ C := by omega
        cases hn : C - D with
        | zero => omega
        | succ n => simp [unaryVisitTest, hle, hlt, hn]
      · by_cases hle : D ≤ C
        · have hz : C - D = 0 := by omega
          simp [unaryVisitTest, hle, hlt, hz]
        · simp [unaryVisitTest, hle, hlt]

theorem unaryVisitFinish_executes (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : NumericLoopInv C L s) (hm : IsUnaryWord (s.stk (.inr p.m)))
    (ht : s.stk (.inr p.t) = []) (hl : s.stk (.inr p.l) = []) (hr : s.stk (.inr p.r) = []) :
    ∃ n ≤ 7 * C + 8 * (s.stk (.inr p.m)).length + 17,
      (unaryVisitFinishRoutine p mode bump).Executes s (unaryVisitFinishEval p mode bump C s) n := by
  let D := (s.stk (.inr p.m)).length
  let u := unaryVisitSubtractEval p C s
  let v := (unaryVisitDecisionOp p mode bump).apply u
  have h1 := preservingUnarySubtract_executes p.m p.t p.l p.r p.hmt p.hlm p.hlt p.hlr p.hrm p.hrt
    C D L (s.stk (.inl .source)) hs.2.2.2.2 (fun k => s.stk (.inr k)) hm ht hl hr
    s.state.1.1 s.state.1.2 s.state.2
  rw [← numericLoop_reconstruct C L s hs] at h1
  change (preservingUnarySubtractRoutine p.m p.t p.l p.r).Executes s u (6 * C + 7 * D + 13) at h1
  have h2 := Atom.executes (unaryVisitDecisionOp p mode bump) u
  obtain ⟨n, hn, h3⟩ := clearMany_executes [.inr p.m, .inr p.l] v
  have hmass : cleanupMass [.inr p.m, .inr p.l] v = D + (C - D) := by
    simp [cleanupMass, v, u, unaryVisitDecisionOp, unaryVisitSubtractEval, Op.apply,
      numericStore, numericStacks, Ne.symm p.hlm, D]
  rw [hmass] at hn
  have h23 := RoutineComposition.seq_executes (Atom.routine (unaryVisitDecisionOp p mode bump))
    (clearManyRoutine [.inr p.m, .inr p.l]) h2 h3
  have hall := RoutineComposition.seq_executes (preservingUnarySubtractRoutine p.m p.t p.l p.r)
    (RoutineComposition.seq (Atom.routine (unaryVisitDecisionOp p mode bump))
      (clearManyRoutine [.inr p.m, .inr p.l])) h1 h23
  exact ⟨(6 * C + 7 * D + 13) + (1 + n), by simp only [List.length_cons, List.length_nil] at hn; omega, hall⟩

theorem unaryIdentifier_executes (p : UnaryVisitPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : UnaryVisitInv p C L s) :
    ∃ n ≤ 7 * C + 10 * L + 22,
      (unaryIdentifierRoutine p mode bump).Executes s (unaryIdentifierEval p mode bump C s) n := by
  let u := guardedUnaryFieldEval (.inl .source) (.inr p.m) s
  obtain ⟨n, hn, hread⟩ := guardedUnaryField_executes (.inl .source : NumericStack K) (.inr p.m)
    (by simp) s hs.2.1 L hs.1.2.2.2.2
  have hi := unaryField_numeric_invariant p.m C L s hs.1
  have hm := guardedUnaryField_output_unary (.inl .source : NumericStack K) (.inr p.m) s hs.2.1
  have hlen := (guardedUnaryField_output_bound (.inl .source : NumericStack K) (.inr p.m) s hs.2.1).trans hs.1.2.2.2.2
  have ht : u.stk (.inr p.t) = [] := by
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using Ne.symm p.hmt)]; exact hs.2.2.1
  have hl : u.stk (.inr p.l) = [] := by
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using p.hlm)]; exact hs.2.2.2.1
  have hr : u.stk (.inr p.r) = [] := by
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using p.hrm)]; exact hs.2.2.2.2
  cases hf : u.state.2 with
  | false =>
      have hbranch := RoutineControl.branch_false Prod.snd (unaryVisitFinishRoutine p mode bump)
        (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop u)
      have hall := RoutineComposition.seq_executes (guardedUnaryFieldRoutine (.inl .source) (.inr p.m))
        (RoutineControl.branch Prod.snd (unaryVisitFinishRoutine p mode bump) (Atom.routine cleanupNoop)) hread hbranch
      refine ⟨n + 2, by omega, ?_⟩
      simpa [unaryIdentifierRoutine, unaryIdentifierEval, hf, u, cleanupNoop, Op.apply] using hall
  | true =>
      obtain ⟨m, hmBound, hfinish⟩ := unaryVisitFinish_executes p mode bump C L u hi hm ht hl hr
      have hbranch := RoutineControl.branch_true Prod.snd (unaryVisitFinishRoutine p mode bump)
        (Atom.routine cleanupNoop) hf hfinish
      have hall := RoutineComposition.seq_executes (guardedUnaryFieldRoutine (.inl .source) (.inr p.m))
        (RoutineControl.branch Prod.snd (unaryVisitFinishRoutine p mode bump) (Atom.routine cleanupNoop)) hread hbranch
      refine ⟨n + (m + 1), by omega, ?_⟩
      simpa only [unaryIdentifierRoutine, unaryIdentifierEval, hf, ↓reduceIte] using hall

/- A compact pure state semantics is proved separately below. Keeping the
actual execution theorem on the composed store expression avoids treating
an extensional high-level parser as an atomic machine instruction. -/

end PolytomyReductionModel
