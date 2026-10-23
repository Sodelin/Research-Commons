/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The ACTUAL star-map objective: at each genuine certificate internal node,
including its root, physically copy A, subtract the node's scoped number
of distinct terminal types, and transfer the remaining unary cost to the
score tape. Neither labels nor full-alphabet enumeration replace that
cardinality. The subtree mask excludes all residual sibling/ancestor data.

The score tape is changed by each query, so the old stack-restoring query
contract is NOT asserted. The separate data-changing countdown below is
charged on every path. Header construction/bounds and the whole-verifier
rejection/clean-halt join remain separate obligations.
-/
import PolytomyRowMarkerController
import PolytomyUnarySubtractCaller
import Mathlib.Data.Fintype.Card

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive ScorePort where
  | outer (port : RangeCursorPort)
  | node (port : ScopedTypePort)
  | cost | temp | score
  deriving DecidableEq, Fintype

abbrev ScorePorts (K : Type) := ScorePort ↪ K

@[simp] theorem scorePorts_eq (p : ScorePorts K) (a b : ScorePort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def scoreOuterPorts (p : ScorePorts K) : RangeCursorPorts K where
  toFun := fun j => p (.outer j)
  inj' := by intro a b h; simpa using p.injective h

def scoreNodeMap : ScopedTypePort → ScorePort
  | .word => .outer .word
  | .rows => .outer .rows
  | .types => .outer .types
  | j => .node j

theorem scoreNodeMap_injective : Function.Injective scoreNodeMap := by decide

def scoreNodePorts (p : ScorePorts K) : ScopedTypePorts K where
  toFun := fun j => p (scoreNodeMap j)
  inj' := fun _ _ h => scoreNodeMap_injective (p.injective h)

def ScoreStackInv (p : ScorePorts K) (m A L : ℕ) (stk : K → List Bool) : Prop :=
  ScopedTypeEntry (scoreNodePorts p) m A L
    (⟨(((), false), false), stk⟩ : CountdownStore K Unit) ∧
  stk (p (.node .output)) = [] ∧ stk (p .cost) = [] ∧ stk (p .temp) = []

theorem scoreInv_transport (p : ScorePorts K) (m A L : ℕ) (stk stk' : K → List Bool)
    (hs : ScoreStackInv p m A L stk) (hL : (stk' (p (.outer .word))).length ≤ L)
    (hx : ∀ j : K, j ≠ p (.outer .word) → j ≠ p (.outer .mask) →
      j ≠ p (.outer .counter) → j ≠ p .score → stk' j = stk j) :
    ScoreStackInv p m A L stk' := by
  refine ⟨?_, (hx _ (by simp) (by simp) (by simp) (by simp)).trans hs.2.1,
    (hx _ (by simp) (by simp) (by simp) (by simp)).trans hs.2.2.1,
    (hx _ (by simp) (by simp) (by simp) (by simp)).trans hs.2.2.2⟩
  apply scopedTypeEntry_transport (scoreNodePorts p) m A L _ _ hs.1 hL
  intro j hj
  apply hx
  all_goals cases j <;> simp_all [scoreNodePorts, scoreNodeMap]

/-- These two functions are semantic observations only. No natural
number computed here is placed in finite machine control. -/
def scoreNodeGood (m A : ℕ) (word : List Bool) : Bool :=
  if word.head? = some false then
    match scopedTypeAnswer m A word with
    | none => false
    | some n => decide (n ≤ A)
  else true

def scoreNodeWeight (m A : ℕ) (word : List Bool) : ℕ :=
  if word.head? = some false then
    match scopedTypeAnswer m A word with
    | none => 0
    | some n => A - n
  else 0

theorem scoreNodeWeight_le (m A : ℕ) (word : List Bool) :
    scoreNodeWeight m A word ≤ A := by
  unfold scoreNodeWeight
  split
  · cases scopedTypeAnswer m A word <;> simp
  · exact Nat.zero_le _

def scoreArithmeticResult (p : ScorePorts K) (A c : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  ⟨(s.state.1, decide (c ≤ A)),
    Function.update (Function.update s.stk (p (.node .output)) []) (p .score)
      (List.replicate (A - c) true ++ s.stk (p .score))⟩

def scoreArithmeticRoutine (p : ScorePorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p (.outer .types)) (p .temp) (p .cost))
    (RoutineComposition.seq (unarySubtractRoutine (p .cost) (p (.node .output)))
      (frameReverseRoutine (p .cost) (p .score)))

/-- Even underflow consumes the distinct-count operand and leaves the
cost scratch empty. Only the score accumulator may change, by A-c bits.
Its old contents are not traversed. A and c are PHYSICAL unary operands. -/
theorem scoreArithmetic_executes (p : ScorePorts K) (A c : ℕ) (s : CountdownStore K F)
    (hA : s.stk (p (.outer .types)) = List.replicate A true)
    (hc : s.stk (p (.node .output)) = List.replicate c true)
    (hcost : s.stk (p .cost) = []) (htemp : s.stk (p .temp) = []) :
    (scoreArithmeticRoutine p).Executes s (scoreArithmeticResult p A c s)
      (3 * A + 3 + ((c + 1) + (A - c + 1))) := by
  let u := wordDuplicateEval (p (.outer .types)) (p .cost) s
  have h1 := wordDuplicate_executes (p (.outer .types)) (p .temp) (p .cost)
    (by simp) (by simp) (by simp) s htemp
  have huA : u.stk (p .cost) = List.replicate A true := by
    simp [u, wordDuplicateEval, hA, hcost]
  have huc : u.stk (p (.node .output)) = List.replicate c true := by
    simpa [u, wordDuplicateEval] using hc
  have h2 := unarySubtract_executes (p .cost) (p (.node .output)) (by simp)
    u.stk u.state.1 u.state.2 A c
  rw [← huA, ← huc, frameCallerStore_self] at h2
  let v := frameCallerStore (p .cost) (p (.node .output)) u.stk u.state.1
    (decide (c ≤ A)) (List.replicate (A - c) true) []
  change (unarySubtractRoutine (p .cost) (p (.node .output))).Executes u v (c + 1) at h2
  have h3 := reverseMove_executes (p .cost) (p .score) (by simp) v
  have hv : v.stk (p .cost) = List.replicate (A - c) true := by
    simp [v, frameCallerStore, unaryCallerStacks]
  rw [hv, List.length_replicate] at h3
  have hr : reverseMoveEval (p .cost) (p .score) v = scoreArithmeticResult p A c s := by
    apply countdownStore_ext
    · rfl
    · funext j
      by_cases hjcost : j = p .cost
      · subst j; simp [reverseMoveEval, scoreArithmeticResult, hcost]
      · by_cases hjout : j = p (.node .output)
        · subst j
          simp [reverseMoveEval, scoreArithmeticResult, v, frameCallerStore, unaryCallerStacks]
        · by_cases hjscore : j = p .score
          · subst j
            simp [reverseMoveEval, scoreArithmeticResult, v, frameCallerStore,
              unaryCallerStacks, u, wordDuplicateEval, List.reverse_replicate]
          · simp [reverseMoveEval, scoreArithmeticResult, v, frameCallerStore,
              unaryCallerStacks, u, wordDuplicateEval, hjcost, hjout, hjscore, htemp]
  rw [hr] at h3
  rw [hA, List.length_replicate] at h1
  exact RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)

def scoreInternalRoutine (p : ScorePorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (scopedTypeRoutine (scoreNodePorts p))
    (RoutineControl.branch Prod.snd (scoreArithmeticRoutine p) (Atom.routine cleanupNoop))

def scoreInternalResult (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  match scopedTypeAnswer m A (s.stk (p (.outer .word))) with
  | none => ⟨((s.state.1.1, true), false), s.stk⟩
  | some c => ⟨((s.state.1.1, true), decide (c ≤ A)),
      Function.update s.stk (p .score) (List.replicate (A - c) true ++ s.stk (p .score))⟩

theorem scoreInternal_executes (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : ScoreStackInv p m A L s.stk) :
    ∃ n ≤ scopedTypeBound m A L + 4 * A + L + 6,
      (scoreInternalRoutine p).Executes s (scoreInternalResult p m A s) n := by
  let t := scoreNodePorts p
  let u := scopedTypeResult t m A s
  obtain ⟨a, ha, h1⟩ := scopedType_executes t m A L s hs.1
  cases hc : scopedTypeAnswer m A (s.stk (p (.outer .word))) with
  | none =>
      have hf : u.state.2 = false := by simp [u, scopedTypeResult, t, scoreNodePorts, scoreNodeMap, hc]
      have h2 := RoutineControl.branch_false Prod.snd (scoreArithmeticRoutine p)
        (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop u)
      refine ⟨a + 2, by omega, ?_⟩
      simpa [scoreInternalRoutine, scoreInternalResult, u, scopedTypeResult,
        t, scoreNodePorts, scoreNodeMap, hc, cleanupNoop, Op.apply] using
        RoutineComposition.seq_executes _ _ h1 h2
  | some c =>
      have hcL : c ≤ L := (scopedTypeAnswer_bound m A _ c hc).trans hs.1.1.1
      have hf : u.state.2 = true := by simp [u, scopedTypeResult, t, scoreNodePorts, scoreNodeMap, hc]
      have huA : u.stk (p (.outer .types)) = List.replicate A true := by
        simpa [u, scopedTypeResult, t, scoreNodePorts, scoreNodeMap, hc] using hs.1.2.1.2.2.2.1
      have huout : u.stk (p (.node .output)) = List.replicate c true := by
        simp [u, scopedTypeResult, t, scoreNodePorts, scoreNodeMap, hc, hs.2.1]
      have hucost : u.stk (p .cost) = [] := by
        simpa [u, scopedTypeResult, t, scoreNodePorts, scoreNodeMap, hc] using hs.2.2.1
      have hutemp : u.stk (p .temp) = [] := by
        simpa [u, scopedTypeResult, t, scoreNodePorts, scoreNodeMap, hc] using hs.2.2.2
      have h2 := scoreArithmetic_executes p A c u huA huout hucost hutemp
      have h3 := RoutineControl.branch_true Prod.snd (scoreArithmeticRoutine p)
        (Atom.routine cleanupNoop) hf h2
      have hr : scoreArithmeticResult p A c u = scoreInternalResult p m A s := by
        apply countdownStore_ext
        · simp [scoreArithmeticResult, scoreInternalResult, u, scopedTypeResult,
            t, scoreNodePorts, scoreNodeMap, hc]
        · funext j
          by_cases hj : j = p (.node .output)
          · subst j
            simp [scoreArithmeticResult, scoreInternalResult, u, scopedTypeResult,
              t, scoreNodePorts, scoreNodeMap, hc, hs.2.1]
          · simp [scoreArithmeticResult, scoreInternalResult, u, scopedTypeResult,
              t, scoreNodePorts, scoreNodeMap, hc, hj]
      rw [hr] at h3
      exact ⟨a + (3 * A + 3 + ((c + 1) + (A - c + 1)) + 1),
        by have hsub := Nat.sub_le A c; omega, RoutineComposition.seq_executes _ _ h1 h3⟩

def scoreNodeRoutine (p : ScorePorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (internalTagPeekOp (p (.outer .word))))
    (RoutineComposition.seq
      (RoutineControl.branch (fun st => st.1.2) (scoreInternalRoutine p) (Atom.routine forestSyntaxStartOp))
      (Atom.routine inclusionSelectedOp))

def scoreNodeResult (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  ⟨((s.state.1.1, true), scoreNodeGood m A (s.stk (p (.outer .word)))),
    Function.update s.stk (p .score)
      (List.replicate (scoreNodeWeight m A (s.stk (p (.outer .word)))) true ++ s.stk (p .score))⟩

def scoreNodeBound (m A L : ℕ) : ℕ := scopedTypeBound m A L + 4 * A + L + 9

theorem scoreNode_executes (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : ScoreStackInv p m A L s.stk) :
    ∃ n ≤ scoreNodeBound m A L,
      (scoreNodeRoutine p).Executes s (scoreNodeResult p m A s) n := by
  let u := (internalTagPeekOp (p (.outer .word))).apply s
  have h1 := Atom.executes (internalTagPeekOp (p (.outer .word))) s
  by_cases hw : (s.stk (p (.outer .word))).head? = some false
  · have hg : u.state.1.2 = true := by simp [u, internalTagPeekOp, Op.apply, hw]
    obtain ⟨a, ha, h2⟩ := scoreInternal_executes p m A L u hs
    have h3 := RoutineControl.branch_true (fun st : CountdownState F => st.1.2)
      (scoreInternalRoutine p) (Atom.routine forestSyntaxStartOp) hg h2
    have h4 := Atom.executes (inclusionSelectedOp (K := K) (F := F)) (scoreInternalResult p m A u)
    have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h3 h4)
    refine ⟨1 + ((a + 1) + 1), by unfold scoreNodeBound; omega, ?_⟩
    cases hc : scopedTypeAnswer m A (s.stk (p (.outer .word))) <;>
      simpa [scoreNodeRoutine, scoreNodeResult, scoreNodeGood, scoreNodeWeight,
        scoreInternalResult, hw, hc, u, internalTagPeekOp, inclusionSelectedOp, Op.apply] using he
  · have hg : u.state.1.2 = false := by simp [u, internalTagPeekOp, Op.apply, hw]
    have h2 := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
      (scoreInternalRoutine p) (Atom.routine forestSyntaxStartOp) hg (Atom.executes forestSyntaxStartOp u)
    have h3 := Atom.executes (inclusionSelectedOp (K := K) (F := F)) (forestSyntaxStartOp.apply u)
    refine ⟨4, by unfold scoreNodeBound; omega, ?_⟩
    simpa [scoreNodeRoutine, scoreNodeResult, scoreNodeGood, scoreNodeWeight, hw,
      u, internalTagPeekOp, forestSyntaxStartOp, inclusionSelectedOp, Op.apply] using
      RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)

/-! The following countdown must be data-changing: its score tape grows.
No instance of MaskedQueryContract is asserted for scoreNodeRoutine. -/

def scoreBodyEval (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  let u := maskedBodyEval (scoreOuterPorts p) (scoreNodeGood m A) s
  ⟨u.state, Function.update u.stk (p .score)
    (List.replicate (if (s.stk (p (.outer .mask))).head?.getD false
      then scoreNodeWeight m A (s.stk (p (.outer .word))) else 0) true ++ s.stk (p .score))⟩

def scoreBodyRoutine (p : ScorePorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  maskedBodyRoutine (scoreOuterPorts p) (scoreNodeRoutine p)

theorem scoreBody_extra (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) (j : K)
    (hjw : j ≠ p (.outer .word)) (hjm : j ≠ p (.outer .mask)) (hjo : j ≠ p .score) :
    (scoreBodyEval p m A s).stk j = s.stk j := by
  simp [scoreBodyEval, maskedBodyEval, scoreOuterPorts, hjw, hjm, hjo]

theorem scoreBody_cursor (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) :
    (scoreBodyEval p m A s).stk (p (.outer .word)) = (s.stk (p (.outer .word))).tail ∧
    (scoreBodyEval p m A s).stk (p (.outer .mask)) = (s.stk (p (.outer .mask))).tail := by
  simp [scoreBodyEval, maskedBodyEval, scoreOuterPorts]

theorem scoreBody_executes (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : ScoreStackInv p m A L s.stk) :
    ∃ n ≤ scoreNodeBound m A L + 4,
      (scoreBodyRoutine p).Executes s (scoreBodyEval p m A s) n := by
  let o := scoreOuterPorts p
  let u := (rangeSelectMaskOp o).apply s
  have h1 := Atom.executes (rangeSelectMaskOp o) s
  cases hg : u.state.1.2 with
  | false =>
      have h2 := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
        (scoreNodeRoutine p) (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop u)
      have h3 := Atom.executes (rangePopWordOp o) u
      have h4 := Atom.executes (rangePopMaskOp o) ((rangePopWordOp o).apply u)
      refine ⟨5, by unfold scoreNodeBound; omega, ?_⟩
      simpa [scoreBodyRoutine, maskedBodyRoutine, scoreBodyEval, maskedBodyEval,
        u, o, scoreOuterPorts, rangeSelectMaskOp, rangePopWordOp, rangePopMaskOp,
        cleanupNoop, Op.apply, hg] using
        RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
          (RoutineComposition.seq_executes _ _ h3 h4))
  | true =>
      obtain ⟨a, ha, h2⟩ := scoreNode_executes p m A L u hs
      have h3 := RoutineControl.branch_true (fun st : CountdownState F => st.1.2)
        (scoreNodeRoutine p) (Atom.routine cleanupNoop) hg h2
      let v := scoreNodeResult p m A u
      have h4 := Atom.executes (rangePopWordOp o) v
      have h5 := Atom.executes (rangePopMaskOp o) ((rangePopWordOp o).apply v)
      refine ⟨1 + ((a + 1) + (1 + 1)), by omega, ?_⟩
      have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h3
        (RoutineComposition.seq_executes _ _ h4 h5))
      convert he using 1
      apply countdownStore_ext
      · simp [scoreBodyEval, maskedBodyEval, v, scoreNodeResult, u, o, scoreOuterPorts,
          rangeSelectMaskOp, rangePopWordOp, rangePopMaskOp, Op.apply, hg]
      · funext j
        by_cases hjw : j = p (.outer .word)
        · subst j
          simp [scoreBodyEval, maskedBodyEval, v, scoreNodeResult, u, o, scoreOuterPorts,
            rangeSelectMaskOp, rangePopWordOp, rangePopMaskOp, Op.apply]
        · by_cases hjm : j = p (.outer .mask)
          · subst j
            simp [scoreBodyEval, maskedBodyEval, v, scoreNodeResult, u, o, scoreOuterPorts,
              rangeSelectMaskOp, rangePopWordOp, rangePopMaskOp, Op.apply]
          · simp [scoreBodyEval, maskedBodyEval, v, scoreNodeResult, u, o, scoreOuterPorts,
              rangeSelectMaskOp, rangePopWordOp, rangePopMaskOp, Op.apply, hg, hjw, hjm]

def scoreCountdownContract (p : ScorePorts K) (m A L : ℕ) :
    CountdownContract (p (.outer .counter)) (scoreBodyRoutine p) (scoreBodyEval p m A)
      (fun s => ScoreStackInv p m A L s.stk) (scoreNodeBound m A L + 4) where
  peek_closed s hs := hs
  pop_closed s hs hg := by
    apply scoreInv_transport p m A L s.stk _ hs
    · simpa [countdownPop, countdownPopOp, Op.apply] using hs.1.1.1
    · intro j hjw hjm hjc hjo; simp [countdownPop, countdownPopOp, Op.apply, hjc]
  body_closed s hs := by
    apply scoreInv_transport p m A L s.stk _ hs
    · rw [(scoreBody_cursor p m A s).1]
      exact (by cases s.stk (p (.outer .word)) <;> simp).trans hs.1.1.1
    · intro j hjw hjm hjc hjo; exact scoreBody_extra p m A s j hjw hjm hjo
  reset_closed s hs := hs
  counter_preserved s hs := scoreBody_extra p m A s _ (by simp) (by simp) (by simp)
  body_executes s hs := scoreBody_executes p m A L s hs

def scoreLoopRoutine (p : ScorePorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  countdownRoutine (p (.outer .counter)) (scoreBodyRoutine p)

def scoreLoopEval (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  countdownEval (p (.outer .counter)) (scoreBodyEval p m A) s

theorem scoreLoop_executes (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : ScoreStackInv p m A L s.stk) :
    ∃ n ≤ (s.stk (p (.outer .counter))).length * (scoreNodeBound m A L + 7) + 3,
      (scoreLoopRoutine p).Executes s (scoreLoopEval p m A s) n ∧
      ScoreStackInv p m A L (scoreLoopEval p m A s).stk ∧
      (scoreLoopEval p m A s).state.1.2 = false ∧
      ((scoreLoopEval p m A s).state.2 = true →
        (scoreLoopEval p m A s).stk (p (.outer .counter)) = []) := by
  simpa only [scoreLoopRoutine, scoreLoopEval, Nat.add_assoc] using
    countdownRoutine_executes (p (.outer .counter)) (scoreBodyRoutine p) (scoreBodyEval p m A)
      (fun s => ScoreStackInv p m A L s.stk) (scoreNodeBound m A L + 4)
      (scoreCountdownContract p m A L) s hs

theorem scoreLoop_extra (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) (j : K)
    (hjw : j ≠ p (.outer .word)) (hjm : j ≠ p (.outer .mask))
    (hjc : j ≠ p (.outer .counter)) (hjo : j ≠ p .score) :
    (scoreLoopEval p m A s).stk j = s.stk j :=
  countdownLoop_preserves (p (.outer .counter)) (scoreBodyEval p m A) (fun t => t.stk j)
    (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hjc])
    (fun t => scoreBody_extra p m A t j hjw hjm hjo)
    (s.stk (p (.outer .counter))).length (countdownPeek (p (.outer .counter)) s)

theorem scoreLoop_frame (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) :
    (scoreLoopEval p m A s).state.1.1 = s.state.1.1 :=
  countdownLoop_preserves (p (.outer .counter)) (scoreBodyEval p m A) (fun t => t.state.1.1)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (s.stk (p (.outer .counter))).length (countdownPeek (p (.outer .counter)) s)

theorem scoreBody_lengths (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F)
    (j : K) (hj : j ≠ p .score) :
    ((scoreBodyEval p m A s).stk j).length ≤ (s.stk j).length := by
  simpa only [scoreBodyEval, Function.update_of_ne hj] using
    maskedBody_lengths (scoreOuterPorts p) (scoreNodeGood m A) s j

theorem scoreLoop_lengths (p : ScorePorts K) (m A : ℕ) (fuel : ℕ) :
    ∀ (s : CountdownStore K F) (j : K), j ≠ p .score →
      ((countdownLoopEval (p (.outer .counter)) (scoreBodyEval p m A) fuel s).stk j).length ≤
        (s.stk j).length := by
  induction fuel with
  | zero => intro s j hj; exact le_refl _
  | succ fuel ih =>
      intro s j hj
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          have hpop : ((countdownPop (p (.outer .counter)) s).stk j).length ≤ (s.stk j).length := by
            by_cases hc : j = p (.outer .counter)
            · subst j; rw [countdownPop_counter]; cases s.stk (p (.outer .counter)) <;> simp
            · simp [countdownPop, countdownPopOp, Op.apply, hc]
          have hb := scoreBody_lengths p m A (countdownPop (p (.outer .counter)) s) j hj
          have hi := ih (countdownPeek (p (.outer .counter))
            (scoreBodyEval p m A (countdownPop (p (.outer .counter)) s))) j hj
          simpa only [countdownLoopEval, hg, ↓reduceIte] using hi.trans (hb.trans hpop)

/-- This bound includes early rejection and every malformed scope. It
does not infer successful loop exhaustion on a failed path. -/
theorem scoreLoop_output_bound (p : ScorePorts K) (m A : ℕ) (fuel : ℕ) :
    ∀ s : CountdownStore K F,
      ((countdownLoopEval (p (.outer .counter)) (scoreBodyEval p m A) fuel s).stk (p .score)).length ≤
        fuel * A + (s.stk (p .score)).length := by
  induction fuel with
  | zero => intro s; simp [countdownLoopEval]
  | succ fuel ih =>
      intro s
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          let u := countdownPeek (p (.outer .counter))
            (scoreBodyEval p m A (countdownPop (p (.outer .counter)) s))
          have hi := ih u
          have hb : (u.stk (p .score)).length ≤ A + (s.stk (p .score)).length := by
            have hw := scoreNodeWeight_le m A (s.stk (p (.outer .word)))
            simp only [u, countdownPeek, countdownPeekOp, scoreBodyEval, countdownPop,
              countdownPopOp, Op.apply, Function.update_same, List.length_append, List.length_replicate]
            simp only [scorePorts_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne]
            split <;> omega
          simp only [countdownLoopEval, hg, ↓reduceIte]
          have he : (fuel + 1) * A = fuel * A + A := Nat.succ_mul fuel A
          omega

def scoreMaskSum (m A : ℕ) (word mask : List Bool) : ℕ :=
  ((rawMarkedSuffixes word mask).map (scoreNodeWeight m A)).sum

/-- Exact successful aggregate. The premise is later discharged by the
typed range observation, not by a promise of constructor provenance. -/
theorem scoreLoop_output (p : ScorePorts K) (m A : ℕ) (fuel : ℕ) :
    ∀ s : CountdownStore K F, s.state.2 = true →
      (s.stk (p (.outer .counter))).length = (s.stk (p (.outer .mask))).length →
      (s.stk (p (.outer .mask))).length ≤ (s.stk (p (.outer .word))).length →
      (s.stk (p (.outer .counter))).length ≤ fuel →
      s.state.1.2 = (s.stk (p (.outer .counter))).head?.isSome →
      (rawMarkedSuffixes (s.stk (p (.outer .word))) (s.stk (p (.outer .mask)))).all
        (scoreNodeGood m A) = true →
      (countdownLoopEval (p (.outer .counter)) (scoreBodyEval p m A) fuel s).state.2 = true ∧
      (countdownLoopEval (p (.outer .counter)) (scoreBodyEval p m A) fuel s).stk (p .score) =
        List.replicate (scoreMaskSum m A (s.stk (p (.outer .word)))
          (s.stk (p (.outer .mask)))) true ++ s.stk (p .score) := by
  induction fuel with
  | zero =>
      intro s hf hsame hfit hlen hpeek hgood
      have hm : s.stk (p (.outer .mask)) = [] := List.eq_nil_of_length_eq_zero (by omega)
      cases hw : s.stk (p (.outer .word)) <;>
        simp [countdownLoopEval, scoreMaskSum, rawMarkedSuffixes, hm, hw, hf]
  | succ fuel ih =>
      intro s hf hsame hfit hlen hpeek hgood
      cases hm : s.stk (p (.outer .mask)) with
      | nil =>
          have hc : s.stk (p (.outer .counter)) = [] :=
            List.eq_nil_of_length_eq_zero (by simpa [hm] using hsame)
          cases hw : s.stk (p (.outer .word)) <;>
            simp [countdownLoopEval, countdownGuard, hpeek, hc, hf, hm, hw,
              scoreMaskSum, rawMarkedSuffixes]
      | cons mark mask =>
          cases hw : s.stk (p (.outer .word)) with
          | nil => simp [hm, hw] at hfit
          | cons bit bits =>
              have hc : (s.stk (p (.outer .counter))).head?.isSome = true := by
                cases hcs : s.stk (p (.outer .counter)) with
                | nil => simp [hcs, hm] at hsame
                | cons b bs => rfl
              have hg : countdownGuard s.state = true := by simp [countdownGuard, hpeek, hc, hf]
              have hgroot : mark = true → scoreNodeGood m A (bit :: bits) = true := by
                intro ht
                have hh : scoreNodeGood m A (bit :: bits) = true ∧
                    (rawMarkedSuffixes bits mask).all (scoreNodeGood m A) = true := by
                  simpa [hw, hm, rawMarkedSuffixes, ht] using hgood
                exact hh.1
              have hgtail : (rawMarkedSuffixes bits mask).all (scoreNodeGood m A) = true := by
                cases ht : mark with
                | false => simpa [hw, hm, rawMarkedSuffixes, ht] using hgood
                | true =>
                    have hh : scoreNodeGood m A (bit :: bits) = true ∧
                        (rawMarkedSuffixes bits mask).all (scoreNodeGood m A) = true := by
                      simpa [hw, hm, rawMarkedSuffixes, ht] using hgood
                    exact hh.2
              let u := countdownPeek (p (.outer .counter))
                (scoreBodyEval p m A (countdownPop (p (.outer .counter)) s))
              have huw : u.stk (p (.outer .word)) = bits := by
                simp [u, scoreBodyEval, maskedBodyEval, scoreOuterPorts, countdownPeek,
                  countdownPeekOp, countdownPop, countdownPopOp, Op.apply, hw]
              have hum : u.stk (p (.outer .mask)) = mask := by
                simp [u, scoreBodyEval, maskedBodyEval, scoreOuterPorts, countdownPeek,
                  countdownPeekOp, countdownPop, countdownPopOp, Op.apply, hm]
              have huc : u.stk (p (.outer .counter)) = (s.stk (p (.outer .counter))).tail := by
                change (scoreBodyEval p m A (countdownPop (p (.outer .counter)) s)).stk _ = _
                rw [scoreBody_extra p m A _ _ (by simp) (by simp) (by simp), countdownPop_counter]
              have huo : u.stk (p .score) =
                  List.replicate (if mark then scoreNodeWeight m A (bit :: bits) else 0) true ++ s.stk (p .score) := by
                simp [u, scoreBodyEval, countdownPeek, countdownPeekOp, countdownPop,
                  countdownPopOp, Op.apply, hw, hm]
              have huf : u.state.2 = true := by
                cases ht : mark with
                | false => simp [u, scoreBodyEval, maskedBodyEval, scoreOuterPorts,
                    countdownPeek, countdownPeekOp, countdownPop, countdownPopOp, Op.apply, hw, hm, ht, hf]
                | true => simp [u, scoreBodyEval, maskedBodyEval, scoreOuterPorts,
                    countdownPeek, countdownPeekOp, countdownPop, countdownPopOp, Op.apply, hw, hm, ht, hf, hgroot ht]
              have husame : (u.stk (p (.outer .counter))).length = (u.stk (p (.outer .mask))).length := by
                rw [huc, hum]
                cases hcs : s.stk (p (.outer .counter)) with
                | nil => simp [hcs, hm] at hsame
                | cons b bs => simpa [hcs, hm] using hsame
              have hufit : (u.stk (p (.outer .mask))).length ≤ (u.stk (p (.outer .word))).length := by
                rw [hum, huw]; simpa [hm, hw] using hfit
              have hulen : (u.stk (p (.outer .counter))).length ≤ fuel := by
                rw [huc]
                cases hcs : s.stk (p (.outer .counter)) with
                | nil => simp
                | cons b bs => simpa [hcs] using hlen
              have hi := ih u huf husame hufit hulen (countdownPeek_control _ _)
                (by simpa only [huw, hum] using hgtail)
              simp only [countdownLoopEval, hg, ↓reduceIte]
              refine ⟨hi.1, ?_⟩
              rw [hi.2, huw, hum, huo, ← List.append_assoc, List.replicate_append_replicate]
              congr 2
              cases mark <;> simp [scoreMaskSum, rawMarkedSuffixes, hw, hm, Nat.add_comm]

def ScoreAllEntry (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  RangeAllEntry (scoreOuterPorts p) m A L s ∧ ScoreStackInv p m A L s.stk

theorem scoreAll_prepared_inv (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m A L s) :
    ScoreStackInv p m A L (rangeAllPrepared (scoreOuterPorts p) s).stk := by
  let o := scoreOuterPorts p
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  have hstk := rangeAllPrepared_stacks o s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  apply scoreInv_transport p m A L s.stk _ hs.2
  · rw [hstk]; simpa [o, scoreOuterPorts] using hs.1.1
  · intro j hjw hjm hjc hjo
    rw [hstk]; simp [o, scoreOuterPorts, hjw, hjm, hjc]

def scoreAllRoutine (p : ScorePorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (rangeAllPrepareRoutine (scoreOuterPorts p))
    (RoutineComposition.seq (scoreLoopRoutine p) (clearManyRoutine (rangeCursorOwned (scoreOuterPorts p))))

def scoreAllEval (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  clearManyEval (rangeCursorOwned (scoreOuterPorts p))
    (scoreLoopEval p m A (rangeAllPrepared (scoreOuterPorts p) s))

def scoreAllBound (m A L : ℕ) : ℕ := L * (scoreNodeBound m A L + 7) + 12 * L + 17

/-- Every physical entry store, including malformed node scopes. Cursor
work is cleared even on failure; the score mass has its own all-path
bound and is intentionally retained for the following budget comparison. -/
theorem scoreAll_executes (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m A L s) :
    ∃ n ≤ scoreAllBound m A L,
      (scoreAllRoutine p).Executes s (scoreAllEval p m A s) n ∧
      (∀ j : K, j ≠ p .score → (scoreAllEval p m A s).stk j = s.stk j) ∧
      (scoreAllEval p m A s).state.1 = (s.state.1.1, false) ∧
      ((scoreAllEval p m A s).stk (p .score)).length ≤ L * A + (s.stk (p .score)).length := by
  let o := scoreOuterPorts p
  let u := rangeAllPrepared o s
  let v := scoreLoopEval p m A u
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  have hustk := rangeAllPrepared_stacks o s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  have huw : u.stk (p (.outer .word)) = s.stk (p (.outer .originalWord)) := by simp [u, hustk, o, scoreOuterPorts]
  have hum : u.stk (p (.outer .mask)) = s.stk (p (.outer .originalMask)) := by simp [u, hustk, o, scoreOuterPorts]
  have huc : u.stk (p (.outer .counter)) = s.stk (p (.outer .originalMask)) := by simp [u, hustk, o, scoreOuterPorts]
  have hux (j : K) (hjw : j ≠ p (.outer .word)) (hjm : j ≠ p (.outer .mask))
      (hjc : j ≠ p (.outer .counter)) : u.stk j = s.stk j := by
    simp [u, hustk, o, scoreOuterPorts, hjw, hjm, hjc]
  have hprep := rangeAllPrepare_executes o s (hf .temp (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
  obtain ⟨a, ha, hrun, hvinv, hvguard, hvempty⟩ := scoreLoop_executes p m A L u (scoreAll_prepared_inv p m A L s hs)
  obtain ⟨b, hb, hclear⟩ := clearMany_executes (rangeCursorOwned o) v
  have hvlen (j : K) (hj : j ≠ p .score) : (v.stk j).length ≤ (u.stk j).length :=
    scoreLoop_lengths p m A (u.stk (p (.outer .counter))).length (countdownPeek (p (.outer .counter)) u) j hj
  have hvw := hvlen (p (.outer .word)) (by simp)
  have hvm := hvlen (p (.outer .mask)) (by simp)
  have hvc := hvlen (p (.outer .counter)) (by simp)
  rw [huw] at hvw
  rw [hum] at hvm
  rw [huc] at hvc
  have hL : (s.stk (p (.outer .originalWord))).length ≤ L := hs.1.1
  have hM : (s.stk (p (.outer .originalMask))).length ≤ L := hs.1.2.1.trans hL
  have hmass : cleanupMass (rangeCursorOwned o) v ≤ 3 * L := by
    simp only [cleanupMass, rangeCursorOwned, o, scoreOuterPorts, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hrestore : ∀ j : K, j ≠ p .score → (scoreAllEval p m A s).stk j = s.stk j := by
    intro j hjo
    by_cases hj : j ∈ rangeCursorOwned o
    · rw [scoreAllEval, clearMany_member _ _ hj]
      apply (hs.1.2.2.2.2 j _).symm
      simp only [rangeCursorOwned, List.mem_cons, List.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> simp [rangeAllWork]
    · have hjw : j ≠ p (.outer .word) := by intro he; apply hj; simp [rangeCursorOwned, o, scoreOuterPorts, he]
      have hjm : j ≠ p (.outer .mask) := by intro he; apply hj; simp [rangeCursorOwned, o, scoreOuterPorts, he]
      have hjc : j ≠ p (.outer .counter) := by intro he; apply hj; simp [rangeCursorOwned, o, scoreOuterPorts, he]
      rw [scoreAllEval, clearMany_outside _ _ hj, scoreLoop_extra p m A u j hjw hjm hjc hjo]
      exact hux j hjw hjm hjc
  have hframe : (scoreAllEval p m A s).state.1 = (s.state.1.1, false) := by
    rw [scoreAllEval, clearMany_state]
    exact Prod.ext (scoreLoop_frame p m A u) hvguard
  have hscore : ((scoreAllEval p m A s).stk (p .score)).length ≤ L * A + (s.stk (p .score)).length := by
    have hi := scoreLoop_output_bound p m A (u.stk (p (.outer .counter))).length
      (countdownPeek (p (.outer .counter)) u)
    have hmul := Nat.mul_le_mul_right A hM
    rw [scoreAllEval, clearMany_outside _ _ (by simp [rangeCursorOwned, scoreOuterPorts])]
    change (v.stk (p .score)).length ≤ _
    change (v.stk (p .score)).length ≤ (u.stk (p (.outer .counter))).length * A + (u.stk (p .score)).length at hi
    rw [huc, hux _ (by simp) (by simp) (by simp)] at hi
    omega
  have he := RoutineComposition.seq_executes _ _ hprep (RoutineComposition.seq_executes _ _ hrun hclear)
  refine ⟨(3 * (s.stk (o .originalWord)).length + 6 * (s.stk (o .originalMask)).length + 10) + (a + b),
    ?_, he, hrestore, hframe, hscore⟩
  rw [huc] at ha
  have hmul := Nat.mul_le_mul_right (scoreNodeBound m A L + 7) hM
  simp only [rangeCursorOwned, List.length_cons, List.length_nil] at hb
  unfold scoreAllBound
  simpa only [o, scoreOuterPorts] using (by omega :
    3 * (s.stk (p (.outer .originalWord))).length +
      6 * (s.stk (p (.outer .originalMask))).length + 10 + (a + b) ≤
      L * (scoreNodeBound m A L + 7) + 12 * L + 17)

theorem scoreAll_success (p : ScorePorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m A L s)
    (hgood : (rawMarkedSuffixes (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask)))).all (scoreNodeGood m A) = true) :
    (scoreAllEval p m A s).state.2 = true ∧
    (scoreAllEval p m A s).stk (p .score) =
      List.replicate (scoreMaskSum m A (s.stk (p (.outer .originalWord)))
        (s.stk (p (.outer .originalMask)))) true ++ s.stk (p .score) := by
  let o := scoreOuterPorts p
  let u := rangeAllPrepared o s
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  have hstk := rangeAllPrepared_stacks o s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  have huw : u.stk (p (.outer .word)) = s.stk (p (.outer .originalWord)) := by simp [u, hstk, o, scoreOuterPorts]
  have hum : u.stk (p (.outer .mask)) = s.stk (p (.outer .originalMask)) := by simp [u, hstk, o, scoreOuterPorts]
  have huc : u.stk (p (.outer .counter)) = s.stk (p (.outer .originalMask)) := by simp [u, hstk, o, scoreOuterPorts]
  have huo : u.stk (p .score) = s.stk (p .score) := by simp [u, hstk, o, scoreOuterPorts]
  have hi := scoreLoop_output p m A (u.stk (p (.outer .counter))).length
    (countdownPeek (p (.outer .counter)) u) rfl
    (by change (u.stk _).length = (u.stk _).length; rw [huc, hum])
    (by change (u.stk _).length ≤ (u.stk _).length; rw [hum, huw]; exact hs.1.2.1)
    (le_refl _) (countdownPeek_control _ _)
    (by change (rawMarkedSuffixes (u.stk _) (u.stk _)).all _ = true; simpa [huw, hum] using hgood)
  refine ⟨hi.1, ?_⟩
  rw [scoreAllEval, clearMany_outside _ _ (by simp [rangeCursorOwned, scoreOuterPorts])]
  simpa only [countdownPeek, countdownPeekOp, Op.apply, huw, hum, huo] using hi.2

/-! ## Exact original objective, with the root included -/

theorem rawTypeCount_le_terminal (N m : ℕ) (R : BTree (ℕ × ℕ)) (hR : rawTreeValid N m R) :
    scanTypeCount Prod.snd R ≤ N + m * N + 3 := by
  obtain ⟨T, rfl⟩ := (rawTreeValid_iff_typed N m R).mp hR
  rw [scanTypeCount_rawTreeCodes, scanTypeCount_spec, ← terminal_card N m]
  exact Finset.card_le_univ _

theorem scoreNodeGood_tree (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    scoreNodeGood m (N + m * N + 3) (rawCellTreeBits R ++ rest) = true := by
  cases R with
  | leaf c => simp [scoreNodeGood, rawCellTreeBits]
  | node l r =>
      have hc := rawTypeCount_le_terminal N m (.node l r) hR
      simp only [scoreNodeGood, rawCellTreeBits, List.cons_append, List.head?_cons,
        ↓reduceIte]
      change (match scopedTypeAnswer m (N + m * N + 3)
        (rawCellTreeBits (.node l r) ++ rest) with
        | none => false | some n => decide (n ≤ N + m * N + 3)) = true
      rw [scopedTypeAnswer_tree N m (.node l r) rest hR]
      exact decide_eq_true hc

theorem scoreNodeWeight_leaf (m A : ℕ) (c : ℕ × ℕ) (rest : List Bool) :
    scoreNodeWeight m A (rawCellTreeBits (.leaf c) ++ rest) = 0 := by
  simp [scoreNodeWeight, rawCellTreeBits]

theorem scoreNodeWeight_node (N m : ℕ) (l r : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m (.node l r)) :
    scoreNodeWeight m (N + m * N + 3) (rawCellTreeBits (.node l r) ++ rest) =
      N + m * N + 3 - scanTypeCount Prod.snd (.node l r) := by
  unfold scoreNodeWeight
  have hh : (rawCellTreeBits (.node l r) ++ rest).head? = some false := rfl
  rw [if_pos hh, scopedTypeAnswer_tree N m (.node l r) rest hR]
  rfl

theorem scoreViews_tree (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    (((rawNodeViews R rest).map rawViewSuffix).map (scoreNodeWeight m (N + m * N + 3))).sum =
      scanStarScore (N + m * N + 3) Prod.snd R := by
  revert hR
  induction R generalizing rest with
  | leaf c =>
      intro hR
      simp [rawNodeViews, rawViewSuffix, scoreNodeWeight_leaf, scanStarScore]
  | node l r ihl ihr =>
      intro hR
      have hp := (rawTreeValid_node N m l r).mp hR
      simp only [rawNodeViews, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
        rawViewSuffix, scoreNodeWeight_node N m l r rest hR,
        ihl (rawCellTreeBits r ++ rest) hp.1, ihr rest hp.2, scanStarScore]
      omega

theorem scoreMask_tree (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    (rawMarkedSuffixes (rawCellTreeBits R ++ rest) (rawNodeMask R)).all
        (scoreNodeGood m (N + m * N + 3)) = true ∧
    scoreMaskSum m (N + m * N + 3) (rawCellTreeBits R ++ rest) (rawNodeMask R) =
        scanStarScore (N + m * N + 3) Prod.snd R := by
  have hv : rawMarkedSuffixes (rawCellTreeBits R ++ rest) (rawNodeMask R) =
      (rawNodeViews R rest).map rawViewSuffix := by
    simpa only [List.append_nil, rawMarkedSuffixes] using rawMarkedSuffixes_tree R rest []
  refine ⟨?_, ?_⟩
  · rw [hv, List.all_map, List.all_eq_true]
    intro v hmem
    exact scoreNodeGood_tree N m v.1 v.2 (rawNodeViews_valid N m R rest hR v hmem)
  · rw [scoreMaskSum, hv, scoreViews_tree N m R rest hR]

theorem scanStarScore_rawTreeCodes {N m : ℕ} (A : ℕ) (T : BTree (Cell N m)) :
    scanStarScore A Prod.snd (rawTreeCodes T) = scanStarScore A Prod.snd T := by
  induction T with
  | leaf c => rfl
  | node l r ihl ihr =>
      change scanStarScore A Prod.snd (rawTreeCodes l) + scanStarScore A Prod.snd (rawTreeCodes r) +
        (A - scanTypeCount Prod.snd (rawTreeCodes (.node l r))) = _
      rw [ihl, ihr, scanTypeCount_rawTreeCodes]
      rfl

theorem scoreAll_executes_tree (p : ScorePorts K) (N m L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m (N + m * N + 3) L s) (T : BTree (Cell N m)) (rest : List Bool)
    (hword : s.stk (p (.outer .originalWord)) = treeBits T ++ rest)
    (hmask : s.stk (p (.outer .originalMask)) = rawNodeMask (rawTreeCodes T)) :
    ∃ n ≤ scoreAllBound m (N + m * N + 3) L,
      (scoreAllRoutine p).Executes s
        ⟨((s.state.1.1, false), true), Function.update s.stk (p .score)
          (List.replicate (scanStarScore (N + m * N + 3) Prod.snd T) true ++ s.stk (p .score))⟩ n := by
  obtain ⟨a, ha, he, hx, hf, hb⟩ := scoreAll_executes p m (N + m * N + 3) L s hs
  have hv := scoreMask_tree N m (rawTreeCodes T) rest (rawTreeCodes_valid T)
  rw [rawTreeCodes_bits, scanStarScore_rawTreeCodes] at hv
  have hsuccess := scoreAll_success p m (N + m * N + 3) L s hs
    (by simpa only [hword, hmask] using hv.1)
  have hr : scoreAllEval p m (N + m * N + 3) s =
      ⟨((s.state.1.1, false), true), Function.update s.stk (p .score)
        (List.replicate (scanStarScore (N + m * N + 3) Prod.snd T) true ++ s.stk (p .score))⟩ := by
    apply countdownStore_ext
    · exact Prod.ext hf hsuccess.1
    · funext j
      by_cases hj : j = p .score
      · subst j; simpa only [Function.update_same, hword, hmask, hv.2] using hsuccess.2
      · simpa only [Function.update_of_ne hj] using hx j hj
  exact ⟨a, ha, hr ▸ he⟩

/-- The certificate is reconstructed from the actual ONE-tree prefix
parser plus range observation, for arbitrary raw input and residual.
Full certificate consumption remains the enclosing end guard's job. -/
theorem scoreAll_executes_observed_typed (p : ScorePorts K) (N m L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m (N + m * N + 3) L s) (rest : List Bool)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length 1
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true) :
    ∃ T : BTree (Cell N m), ∃ n : ℕ,
      s.stk (p (.outer .originalWord)) = treeBits T ++ rest ∧
      n ≤ scoreAllBound m (N + m * N + 3) L ∧
      (scoreAllRoutine p).Executes s
        ⟨((s.state.1.1, false), true), Function.update s.stk (p .score)
          (List.replicate (scanStarScore (N + m * N + 3) Prod.snd T) true ++ s.stk (p .score))⟩ n := by
  obtain ⟨Rs, hlen, hw, hm⟩ := (rawForestMaskParse_all_words _ rest _ 1).mp hparse
  cases Rs with
  | nil => simp at hlen
  | cons R Rs =>
      have hz : Rs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst Rs
      have hR := (forestMaskCellCheck_iff N m [R] rest).mp (by simpa only [← hw, ← hm] using hcheck)
      obtain ⟨T, hT⟩ := (rawTreeValid_iff_typed N m R).mp (hR R (by simp))
      have hword : s.stk (p (.outer .originalWord)) = treeBits T ++ rest := by
        simpa [rawForestWord, ← hT, rawTreeCodes_bits] using hw
      have hmask : s.stk (p (.outer .originalMask)) = rawNodeMask (rawTreeCodes T) := by
        simpa [rawForestNodeMask, ← hT] using hm
      obtain ⟨n, hn, he⟩ := scoreAll_executes_tree p N m L s hs T rest hword hmask
      exact ⟨T, n, hword, hn, he⟩

/-! ## Physical budget comparison and all-path score cleanup -/

theorem scoreLoop_unary (p : ScorePorts K) (m A : ℕ) (fuel : ℕ) :
    ∀ (s : CountdownStore K F) (C : ℕ), s.stk (p .score) = List.replicate C true →
      ∃ D : ℕ, (countdownLoopEval (p (.outer .counter)) (scoreBodyEval p m A) fuel s).stk
        (p .score) = List.replicate D true := by
  induction fuel with
  | zero => intro s C hC; exact ⟨C, hC⟩
  | succ fuel ih =>
      intro s C hC
      cases hg : countdownGuard s.state with
      | false => exact ⟨C, by simpa only [countdownLoopEval, hg, Bool.false_eq_true, ↓reduceIte] using hC⟩
      | true =>
          let u := countdownPeek (p (.outer .counter))
            (scoreBodyEval p m A (countdownPop (p (.outer .counter)) s))
          let d := if (s.stk (p (.outer .mask))).head?.getD false
            then scoreNodeWeight m A (s.stk (p (.outer .word))) else 0
          have hu : u.stk (p .score) = List.replicate (d + C) true := by
            simp [u, scoreBodyEval, countdownPeek, countdownPeekOp, countdownPop,
              countdownPopOp, Op.apply, hC, d, List.replicate_append_replicate]
          obtain ⟨D, hD⟩ := ih u (d + C) hu
          exact ⟨D, by simpa only [countdownLoopEval, hg, ↓reduceIte] using hD⟩

theorem scoreAll_unary (p : ScorePorts K) (m A : ℕ) (s : CountdownStore K F)
    (hs : s.stk (p .score) = []) :
    ∃ S : ℕ, (scoreAllEval p m A s).stk (p .score) = List.replicate S true := by
  let u := rangeAllPrepared (scoreOuterPorts p) s
  have hu : u.stk (p .score) = List.replicate 0 true := by
    simp [u, rangeAllPrepared, wordDuplicateEval, forestSyntaxStartOp, Op.apply, scoreOuterPorts, hs]
  obtain ⟨S, hS⟩ := scoreLoop_unary p m A (u.stk (p (.outer .counter))).length
    (countdownPeek (p (.outer .counter)) u) 0 hu
  refine ⟨S, ?_⟩
  rw [scoreAllEval, clearMany_outside _ _ (by simp [rangeCursorOwned, scoreOuterPorts])]
  exact hS

def scoreBudgetFinishRoutine (p : ScorePorts K) (budget : K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine budget (p .temp) (p .cost))
    (RoutineComposition.seq (unarySubtractRoutine (p .cost) (p .score))
      (clearManyRoutine [p .cost]))

def scoreBudgetFinishResult (p : ScorePorts K) (B S : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  ⟨(s.state.1, decide (S ≤ B)), Function.update s.stk (p .score) []⟩

theorem scoreBudgetFinish_executes (p : ScorePorts K) (budget : K)
    (hbudget : ∀ j : ScorePort, budget ≠ p j) (B S : ℕ) (s : CountdownStore K F)
    (hB : s.stk budget = List.replicate B true)
    (hS : s.stk (p .score) = List.replicate S true)
    (hcost : s.stk (p .cost) = []) (htemp : s.stk (p .temp) = []) :
    ∃ n ≤ 4 * B + S + 6,
      (scoreBudgetFinishRoutine p budget).Executes s (scoreBudgetFinishResult p B S s) n := by
  let u := wordDuplicateEval budget (p .cost) s
  have h1 := wordDuplicate_executes budget (p .temp) (p .cost)
    (hbudget .temp) (hbudget .cost) (by simp) s htemp
  rw [hB, List.length_replicate] at h1
  have huB : u.stk (p .cost) = List.replicate B true := by simp [u, wordDuplicateEval, hB, hcost]
  have huS : u.stk (p .score) = List.replicate S true := by simpa [u, wordDuplicateEval] using hS
  have h2 := unarySubtract_executes (p .cost) (p .score) (by simp) u.stk u.state.1 u.state.2 B S
  rw [← huB, ← huS, frameCallerStore_self] at h2
  let v := frameCallerStore (p .cost) (p .score) u.stk u.state.1 (decide (S ≤ B))
    (List.replicate (B - S) true) []
  change (unarySubtractRoutine (p .cost) (p .score)).Executes u v (S + 1) at h2
  obtain ⟨d, hd, h3⟩ := clearMany_executes [p .cost] v
  have hmass : cleanupMass [p .cost] v = B - S := by
    simp [cleanupMass, v, frameCallerStore]
  have hr : clearManyEval [p .cost] v = scoreBudgetFinishResult p B S s := by
    apply countdownStore_ext
    · rfl
    · funext j
      by_cases hjc : j = p .cost
      · subst j
        simp [clearManyEval, clearStackEval, scoreBudgetFinishResult, hcost]
      · by_cases hjs : j = p .score
        · subst j
          simp [clearManyEval, clearStackEval, scoreBudgetFinishResult, v, frameCallerStore]
        · simp [clearManyEval, clearStackEval, scoreBudgetFinishResult, v,
            frameCallerStore, u, wordDuplicateEval, hjc, hjs]
  rw [hr] at h3
  refine ⟨3 * B + 3 + (S + 1 + d), ?_,
    RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)⟩
  simp only [hmass, List.length_cons, List.length_nil] at hd
  have hsub := Nat.sub_le B S
  omega

/-- Only a successful aggregate may enter the flag-overwriting unary
comparison. Failure instead clears the accumulated score and stays false. -/
def scoreBudgetRoutine (p : ScorePorts K) (budget : K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (scoreAllRoutine p)
    (RoutineControl.branch Prod.snd (scoreBudgetFinishRoutine p budget) (clearManyRoutine [p .score]))

def scoreBudgetResult (p : ScorePorts K) (m A B : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  let v := scoreAllEval p m A s
  ⟨((s.state.1.1, false), v.state.2 && decide ((v.stk (p .score)).length ≤ B)), s.stk⟩

def scoreBudgetBound (m A B L : ℕ) : ℕ := scoreAllBound m A L + 4 * B + L * A + 7

theorem scoreBudget_executes (p : ScorePorts K) (budget : K)
    (hbudget : ∀ j : ScorePort, budget ≠ p j) (m A B L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m A L s) (hscore : s.stk (p .score) = [])
    (hB : s.stk budget = List.replicate B true) :
    ∃ n ≤ scoreBudgetBound m A B L,
      (scoreBudgetRoutine p budget).Executes s (scoreBudgetResult p m A B s) n := by
  let v := scoreAllEval p m A s
  obtain ⟨a, ha, h1, hx, hf, hmass⟩ := scoreAll_executes p m A L s hs
  obtain ⟨S, hS⟩ := scoreAll_unary p m A s hscore
  have hSL : S ≤ L * A := by simpa only [hS, List.length_replicate, hscore, List.length_nil, Nat.add_zero] using hmass
  have hBv : v.stk budget = List.replicate B true := (hx budget (hbudget .score)).trans hB
  have hcost : v.stk (p .cost) = [] := (hx _ (by simp)).trans hs.2.2.2.1
  have htemp : v.stk (p .temp) = [] := (hx _ (by simp)).trans hs.2.2.2.2
  cases hg : v.state.2 with
  | false =>
      obtain ⟨d, hd, h2⟩ := clearMany_executes [p .score] v
      have hb := RoutineControl.branch_false Prod.snd (scoreBudgetFinishRoutine p budget)
        (clearManyRoutine [p .score]) hg h2
      have hr : clearManyEval [p .score] v = scoreBudgetResult p m A B s := by
        apply countdownStore_ext
        · rw [clearMany_state]
          simpa only [scoreBudgetResult, hg, Bool.false_and] using Prod.ext hf hg
        · funext j
          by_cases hj : j = p .score
          · subst j; simp [clearManyEval, clearStackEval, scoreBudgetResult, hscore]
          · rw [clearMany_outside _ _ (by simp [hj])]
            exact hx j hj
      rw [hr] at hb
      refine ⟨a + (d + 1), ?_, RoutineComposition.seq_executes _ _ h1 hb⟩
      have hm : cleanupMass [p .score] v = S := by simp [cleanupMass, hS]
      simp only [hm, List.length_cons, List.length_nil] at hd
      unfold scoreBudgetBound
      omega
  | true =>
      obtain ⟨d, hd, h2⟩ := scoreBudgetFinish_executes p budget hbudget B S v hBv hS hcost htemp
      have hb := RoutineControl.branch_true Prod.snd (scoreBudgetFinishRoutine p budget)
        (clearManyRoutine [p .score]) hg h2
      have hr : scoreBudgetFinishResult p B S v = scoreBudgetResult p m A B s := by
        apply countdownStore_ext
        · simp only [scoreBudgetFinishResult, scoreBudgetResult, hg, Bool.true_and, hS,
            List.length_replicate]
          exact congrArg (fun f => (f, decide (S ≤ B))) hf
        · funext j
          by_cases hj : j = p .score
          · subst j; simp [scoreBudgetFinishResult, scoreBudgetResult, hscore]
          · simpa only [scoreBudgetFinishResult, scoreBudgetResult, Function.update_of_ne hj] using hx j hj
      rw [hr] at hb
      exact ⟨a + (d + 1), by unfold scoreBudgetBound; omega,
        RoutineComposition.seq_executes _ _ h1 hb⟩

theorem scoreBudget_executes_observed_typed (p : ScorePorts K) (budget : K)
    (hbudget : ∀ j : ScorePort, budget ≠ p j) (N m B L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m (N + m * N + 3) L s) (hscore : s.stk (p .score) = [])
    (hB : s.stk budget = List.replicate B true) (rest : List Bool)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length 1
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true) :
    ∃ T : BTree (Cell N m), ∃ n : ℕ,
      s.stk (p (.outer .originalWord)) = treeBits T ++ rest ∧
      n ≤ scoreBudgetBound m (N + m * N + 3) B L ∧
      (scoreBudgetRoutine p budget).Executes s
        ⟨((s.state.1.1, false), decide (scanStarScore (N + m * N + 3) Prod.snd T ≤ B)), s.stk⟩ n := by
  obtain ⟨Rs, hlen, hw, hm⟩ := (rawForestMaskParse_all_words _ rest _ 1).mp hparse
  cases Rs with
  | nil => simp at hlen
  | cons R Rs =>
      have hz : Rs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst Rs
      have hR := (forestMaskCellCheck_iff N m [R] rest).mp (by simpa only [← hw, ← hm] using hcheck)
      obtain ⟨T, hT⟩ := (rawTreeValid_iff_typed N m R).mp (hR R (by simp))
      have hword : s.stk (p (.outer .originalWord)) = treeBits T ++ rest := by
        simpa [rawForestWord, ← hT, rawTreeCodes_bits] using hw
      have hmask : s.stk (p (.outer .originalMask)) = rawNodeMask (rawTreeCodes T) := by
        simpa [rawForestNodeMask, ← hT] using hm
      have hv := scoreMask_tree N m (rawTreeCodes T) rest (rawTreeCodes_valid T)
      rw [rawTreeCodes_bits, scanStarScore_rawTreeCodes] at hv
      have hsuccess := scoreAll_success p m (N + m * N + 3) L s hs
        (by simpa only [hword, hmask] using hv.1)
      have hsval : ((scoreAllEval p m (N + m * N + 3) s).stk (p .score)).length =
          scanStarScore (N + m * N + 3) Prod.snd T := by
        rw [hsuccess.2, hword, hmask, hv.2, hscore, List.append_nil, List.length_replicate]
      obtain ⟨n, hn, he⟩ := scoreBudget_executes p budget hbudget m (N + m * N + 3) B L s hs hscore hB
      refine ⟨T, n, hword, hn, ?_⟩
      simpa only [scoreBudgetResult, hsuccess.1, hsval, Bool.true_and] using he

/- This is the original restricted star-map score and budget test, not
an arbitrary differentiation-DAG verifier. All bounds still contain the
PHYSICAL m,A,B parameters. A=N+mN+3 and the clipped budget must be built
only after bounded headers/caps. One inventory, all preceding guards,
monotone global rejection and the exact accepted/rejected clean halt
remain unjoined. VerifierMachineWitness and EncodedSourceHardness remain
independent. No elaboration, execution, kernel or novelty claim. -/

end PolytomyReductionModel.WholeVerifierController
