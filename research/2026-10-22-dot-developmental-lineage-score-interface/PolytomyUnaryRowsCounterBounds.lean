/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

All-path nested counter and saved-count bounds. Successful exhaustion is
not used to bound malformed partial runs. These support later real cleanup
and replay in the original downstream validity controller.
-/
import PolytomyUnaryRowsPredicates

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem countdownLoop_counter_le_on (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F))
    (f : CountdownStore K F → CountdownStore K F) (Inv : CountdownStore K F → Prop)
    (M : ℕ) (hc : CountdownContract counter body f Inv M) (fuel : ℕ) :
    ∀ s, Inv s → ((countdownLoopEval counter f fuel s).stk counter).length ≤ (s.stk counter).length := by
  induction fuel with
  | zero => intro s hs; exact le_refl _
  | succ fuel ih =>
      intro s hs
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          have hp := hc.pop_closed s hs hg
          let u := countdownPeek counter (f (countdownPop counter s))
          have hu : Inv u := hc.peek_closed _ (hc.body_closed _ hp)
          have hcounter : u.stk counter = (s.stk counter).tail := by
            change (f (countdownPop counter s)).stk counter = _
            rw [hc.counter_preserved _ hp, countdownPop_counter]
          have htail : (s.stk counter).tail.length ≤ (s.stk counter).length := by
            cases s.stk counter <;> simp
          have hi := ih u hu
          simp only [countdownLoopEval, hg, ↓reduceIte]
          exact hi.trans (by rw [hcounter]; exact htail)

theorem countdown_counter_le_on (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F))
    (f : CountdownStore K F → CountdownStore K F) (Inv : CountdownStore K F → Prop)
    (M : ℕ) (hc : CountdownContract counter body f Inv M) (s : CountdownStore K F) (hs : Inv s) :
    ((countdownEval counter f s).stk counter).length ≤ (s.stk counter).length :=
  countdownLoop_counter_le_on counter body f Inv M hc (s.stk counter).length
    (countdownPeek counter s) (hc.peek_closed s hs)

theorem unaryFramedRow_counter_bound (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) (hempty : s.stk (.inr c) = []) :
    ((unaryFramedRowEval p c mode bump C s).stk (.inr c)).length ≤ L := by
  have hu := unaryField_visit_invariant p c hc C L s hs
  have hloop := countdown_counter_le_on (.inr c) (unaryIdentifierRoutine p mode bump)
    (unaryIdentifierEval p mode bump C) (UnaryVisitInv p C L) (7 * C + 10 * L + 22)
    (unaryIdentifierContract p c hc mode bump C L) _ hu
  have hprefix := (guardedUnaryField_output_bound (.inl .source : NumericStack K) (.inr c) s hempty).trans hs.1.2.2.2.2
  exact hloop.trans hprefix

def BoundedUnaryRowsInv (p : UnaryVisitPorts K) (c : K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) : Prop :=
  UnaryRowsInv p c C L s ∧ (s.stk (.inr c)).length ≤ L

theorem guardedUnaryRow_counter_bound (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : BoundedUnaryRowsInv p c C L s) :
    ((guardedUnaryRowEval p c mode bump C s).stk (.inr c)).length ≤ L := by
  cases hf : s.state.2 with
  | false => simpa [guardedUnaryRowEval, hf, countdownReset, countdownResetOp, Op.apply] using hs.2
  | true => simpa only [guardedUnaryRowEval, hf, ↓reduceIte] using
      unaryFramedRow_counter_bound p c hc mode bump C L s hs.1.1 (hs.1.2 hf)

def boundedUnaryRowsOuterContract (q : UnaryRowsPorts K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C L : ℕ) :
    CountdownContract (.inr q.d) (guardedUnaryRowRoutine q.p q.c mode bump)
      (guardedUnaryRowEval q.p q.c mode bump C) (BoundedUnaryRowsInv q.p q.c C L)
      (unaryFramedRowBound C L + 1) where
  peek_closed s hs := ⟨(unaryRowsOuterContract q.p q.c q.d q.hc q.hd q.hcd mode bump C L).peek_closed s hs.1, hs.2⟩
  pop_closed s hs hg := by
    refine ⟨(unaryRowsOuterContract q.p q.c q.d q.hc q.hd q.hcd mode bump C L).pop_closed s hs.1 hg, ?_⟩
    simpa [countdownPop, countdownPopOp, Op.apply, q.hcd] using hs.2
  body_closed s hs :=
    ⟨(unaryRowsOuterContract q.p q.c q.d q.hc q.hd q.hcd mode bump C L).body_closed s hs.1,
      guardedUnaryRow_counter_bound q.p q.c q.hc mode bump C L s hs⟩
  reset_closed s hs := ⟨(unaryRowsOuterContract q.p q.c q.d q.hc q.hd q.hcd mode bump C L).reset_closed s hs.1, hs.2⟩
  counter_preserved s hs := (unaryRowsOuterContract q.p q.c q.d q.hc q.hd q.hcd mode bump C L).counter_preserved s hs.1
  body_executes s hs := (unaryRowsOuterContract q.p q.c q.d q.hc q.hd q.hcd mode bump C L).body_executes s hs.1

theorem unaryRows_counter_bounds (q : UnaryRowsPorts K) (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) (hd : s.stk (.inr q.d) = []) (hz : s.stk (.inr q.saved) = []) :
    ((unaryRowsEval q mode bump C s).stk (.inr q.c)).length ≤ L ∧
    ((unaryRowsEval q mode bump C s).stk (.inr q.d)).length ≤ L ∧
    ((unaryRowsEval q mode bump C s).stk (.inr q.saved)).length ≤ L := by
  let u := guardedUnaryFieldEval (.inl .source) (.inr q.d) s
  let v := unaryRowsPrefixEval q s
  have hinner : v.stk (.inr q.c) = [] := by
    simp only [v, unaryRowsPrefixEval, wordDuplicateEval,
      Function.update_of_ne (by simpa using Ne.symm q.hsc)]
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using q.hcd)]; exact hc
  have hi : BoundedUnaryRowsInv q.p q.c C L v :=
    ⟨unaryRowsPrefix_invariant q C L s hs hc, by rw [hinner]; simp⟩
  obtain ⟨n, hn, he, hfinal, hg, hclear⟩ := countdownRoutine_executes (.inr q.d)
    (guardedUnaryRowRoutine q.p q.c mode bump) (guardedUnaryRowEval q.p q.c mode bump C)
    (BoundedUnaryRowsInv q.p q.c C L) (unaryFramedRowBound C L + 1)
    (boundedUnaryRowsOuterContract q mode bump C L) v hi
  have hdle := countdown_counter_le_on (.inr q.d) (guardedUnaryRowRoutine q.p q.c mode bump)
    (guardedUnaryRowEval q.p q.c mode bump C) (UnaryRowsInv q.p q.c C L) (unaryFramedRowBound C L + 1)
    (unaryRowsOuterContract q.p q.c q.d q.hc q.hd q.hcd mode bump C L) v hi.1
  have hcount := (guardedUnaryField_output_bound (.inl .source : NumericStack K) (.inr q.d) s hd).trans hs.1.2.2.2.2
  have hvd : v.stk (.inr q.d) = u.stk (.inr q.d) := by
    simp [v, u, unaryRowsPrefixEval, wordDuplicateEval, Ne.symm q.hsd]
  have huv : u.stk (.inr q.saved) = [] := by
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using q.hsd)]; exact hz
  have hvz : v.stk (.inr q.saved) = u.stk (.inr q.d) := by
    simp [v, unaryRowsPrefixEval, wordDuplicateEval, ← u, huv]
  have hzpres := unaryRowsOuter_extra q.p q.c q.d q.saved q.hc q.hd q.hcd q.hsc q.hsd mode bump C L v hi.1
  exact ⟨hfinal.2, hdle.trans (by rw [hvd]; exact hcount), by rw [unaryRowsEval, hzpres, hvz]; exact hcount⟩

end PolytomyReductionModel
