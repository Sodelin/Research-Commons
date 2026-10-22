/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Whole original internal rows section: read its physical unary row count,
actually preserve a copy, then visit nested rows. This does not accept a
whole record: header-count equality, final suffix and coverage controller
are separate obligations. The stored count is retained even on row failure.
-/
import PolytomyUnaryRowsOuter

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

structure UnaryRowsPorts (K : Type) where
  p : UnaryVisitPorts K
  c : K
  d : K
  saved : K
  hc : UnaryVisitOutside p c
  hd : UnaryVisitOutside p d
  hs : UnaryVisitOutside p saved
  hcd : c ≠ d
  hsc : saved ≠ c
  hsd : saved ≠ d

def unaryRowsPrefixEval (q : UnaryRowsPorts K) (s : CountdownStore (NumericStack K) F) :=
  wordDuplicateEval (.inr q.d) (.inr q.saved)
    (guardedUnaryFieldEval (.inl .source) (.inr q.d) s)

def unaryRowsRoutine (q : UnaryRowsPorts K) (mode : UnaryVisitMode) (bump : F → Bool → F) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (guardedUnaryFieldRoutine (.inl .source) (.inr q.d))
    (RoutineComposition.seq (wordDuplicateRoutine (.inr q.d) (.inr q.p.t) (.inr q.saved))
      (unaryRowsOuterRoutine q.p q.c q.d mode bump))

def unaryRowsEval (q : UnaryRowsPorts K) (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C : ℕ) (s : CountdownStore (NumericStack K) F) :=
  unaryRowsOuterEval q.p q.c q.d mode bump C (unaryRowsPrefixEval q s)

def unaryRowsBound (C L : ℕ) := L * (unaryFramedRowBound C L + 4) + 5 * L + 10

theorem unaryRowsPrefix_invariant (q : UnaryRowsPorts K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) : UnaryRowsInv q.p q.c C L (unaryRowsPrefixEval q s) := by
  have hi := unaryField_visit_invariant q.p q.d q.hd C L s hs
  have hinner : (guardedUnaryFieldEval (.inl .source) (.inr q.d) s).stk (.inr q.c) = [] := by
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using q.hcd)]; exact hc
  refine ⟨?_, ?_⟩
  · rcases q.hs with ⟨hsm, hst, hsl, hsr⟩
    simpa [unaryRowsPrefixEval, wordDuplicateEval, UnaryVisitInv, NumericLoopInv,
      Ne.symm hsm, Ne.symm hst, Ne.symm hsl, Ne.symm hsr] using hi
  · intro hf
    simpa [unaryRowsPrefixEval, wordDuplicateEval, Ne.symm q.hsc] using hinner

theorem unaryRows_executes (q : UnaryRowsPorts K) (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) (hd : s.stk (.inr q.d) = []) (hz : s.stk (.inr q.saved) = []) :
    ∃ n ≤ unaryRowsBound C L,
      (unaryRowsRoutine q mode bump).Executes s (unaryRowsEval q mode bump C s) n ∧
      UnaryRowsInv q.p q.c C L (unaryRowsEval q mode bump C s) ∧
      (unaryRowsEval q mode bump C s).state.1.2 = false ∧
      ((unaryRowsEval q mode bump C s).state.2 = true →
        (unaryRowsEval q mode bump C s).stk (.inr q.d) = []) := by
  let u := guardedUnaryFieldEval (.inl .source) (.inr q.d) s
  obtain ⟨n, hn, hread⟩ := guardedUnaryField_executes (.inl .source : NumericStack K) (.inr q.d)
    (by simp) s hd L hs.1.2.2.2.2
  have htemp : u.stk (.inr q.p.t) = [] := by
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using Ne.symm q.hd.2.1)]; exact hs.2.2.1
  have hcopy := wordDuplicate_executes (.inr q.d : NumericStack K) (.inr q.p.t) (.inr q.saved)
    (by simpa using q.hd.2.1) (by simpa using Ne.symm q.hsd) (by simpa using Ne.symm q.hs.2.1) u htemp
  have hlen := (guardedUnaryField_output_bound (.inl .source : NumericStack K) (.inr q.d) s hd).trans hs.1.2.2.2.2
  have hcount : ((unaryRowsPrefixEval q s).stk (.inr q.d)).length = (u.stk (.inr q.d)).length := by
    simp [unaryRowsPrefixEval, wordDuplicateEval, Ne.symm q.hsd, u]
  obtain ⟨m, hm, houter, hi, hg, hclear⟩ := unaryRowsOuter_executes q.p q.c q.d q.hc q.hd q.hcd
    mode bump C L (unaryRowsPrefixEval q s) (unaryRowsPrefix_invariant q C L s hs hc)
  rw [hcount] at hm
  have hmul := Nat.mul_le_mul_right (unaryFramedRowBound C L + 4) hlen
  have htail := RoutineComposition.seq_executes (wordDuplicateRoutine (.inr q.d) (.inr q.p.t) (.inr q.saved))
    (unaryRowsOuterRoutine q.p q.c q.d mode bump) hcopy houter
  have hall := RoutineComposition.seq_executes (guardedUnaryFieldRoutine (.inl .source) (.inr q.d))
    (RoutineComposition.seq (wordDuplicateRoutine (.inr q.d) (.inr q.p.t) (.inr q.saved))
      (unaryRowsOuterRoutine q.p q.c q.d mode bump)) hread htail
  exact ⟨n + ((3 * (u.stk (.inr q.d)).length + 3) + m), by unfold unaryRowsBound; omega, hall, hi, hg, hclear⟩

theorem unaryRows_observation (q : UnaryRowsPorts K) (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) :
    unaryVisitObservation (unaryRowsEval q mode bump C s) =
      if s.state.2 then (readFramedList (readFramedList readUnaryFrame) (s.stk (.inl .source))).map
        (fun z => (z.2, z.1.foldl (fun acc row => row.foldl (unaryVisitStep mode bump C) acc) s.state.1.1))
      else none := by
  rw [unaryRowsEval, unaryRowsOuter_observation q.p q.c q.d q.hc q.hd q.hcd mode bump C L _
    (unaryRowsPrefix_invariant q C L s hs hc)]
  cases hf : s.state.2 with
  | false => simp [unaryRowsPrefixEval, wordDuplicateEval, guardedUnaryFieldEval, hf]
  | true =>
      cases hp : readUnaryFrame (s.stk (.inl .source)) with
      | none => simp [unaryRowsPrefixEval, wordDuplicateEval, guardedUnaryFieldEval, hf, hp,
          unaryCallerResult, frameCallerStore, readFramedList]
      | some z =>
          rcases z with ⟨n, rest⟩
          simp [unaryRowsPrefixEval, wordDuplicateEval, guardedUnaryFieldEval, hf, hp,
            unaryCallerResult, frameCallerStore, Ne.symm q.hsd, readFramedList]

theorem unaryRows_saved_count (q : UnaryRowsPorts K) (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) (hz : s.stk (.inr q.saved) = [])
    (hf : s.state.2 = true) (n : ℕ) (rest : List Bool)
    (hp : readUnaryFrame (s.stk (.inl .source)) = some (n, rest)) :
    (unaryRowsEval q mode bump C s).stk (.inr q.saved) = List.replicate n true := by
  rw [unaryRowsEval, unaryRowsOuter_extra q.p q.c q.d q.saved q.hc q.hd q.hcd q.hsc q.hsd
    mode bump C L _ (unaryRowsPrefix_invariant q C L s hs hc)]
  simp [unaryRowsPrefixEval, wordDuplicateEval, guardedUnaryFieldEval, hf, hp, unaryCallerResult,
    frameCallerStore, q.hsd, hz]

theorem unaryRows_extra (q : UnaryRowsPorts K) (k : K) (hkc : k ≠ q.c) (hkd : k ≠ q.d)
    (hkz : k ≠ q.saved) (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) :
    (unaryRowsEval q mode bump C s).stk (.inr k) = s.stk (.inr k) := by
  rw [unaryRowsEval, unaryRowsOuter_extra q.p q.c q.d k q.hc q.hd q.hcd hkc hkd
    mode bump C L _ (unaryRowsPrefix_invariant q C L s hs hc)]
  simp only [unaryRowsPrefixEval, wordDuplicateEval, Function.update_of_ne (by simpa using hkz)]
  exact guardedUnaryField_extra _ _ _ (by simp) (by simpa using hkd) s

/- Returned observation is exact even for empty rows/lists and malformed
or trailing input. It deliberately retains the suffix instead of accepting
it. The saved count is a real tape, not recovered from a consumed counter.
Final suffix rejection, declared-count equality and repeated coverage
queries remain required for the original whole validity check.
-/

end PolytomyReductionModel
