/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The same physical mask cursor, now with a paid unary tally rather than an
all/exists Boolean. A query is still fully instantiated, stack-restoring
code. A physical selected-and-true branch pushes ONE bit, then restores
the local loop flag. This reset is local counting control, not permission
to erase a prior whole-verifier rejection.
-/
import PolytomyWholeUniquenessGuard

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def maskedTally (q : List Bool → Bool) : List Bool → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | b :: bits, mark :: mask =>
      (if mark && q (b :: bits) then 1 else 0) + maskedTally q bits mask

theorem maskedTally_le_length (q : List Bool → Bool) (word mask : List Bool) :
    maskedTally q word mask ≤ mask.length := by
  induction word generalizing mask with
  | nil => simp [maskedTally]
  | cons b bits ih =>
      cases mask with
      | nil => simp [maskedTally]
      | cons mark mask =>
          have hi := ih mask
          simp only [maskedTally, List.length_cons]
          split <;> omega

def tallyPushOp (out : K) : Op K Bool (CountdownState F) := .push out (fun _ => true)

def tallyIncrementEval (out : K) (s : CountdownStore K F) : CountdownStore K F :=
  if countdownGuard s.state then (tallyPushOp out).apply s else s

def tallyIncrementRoutine (out : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineControl.branch countdownGuard (Atom.routine (tallyPushOp out)) (Atom.routine cleanupNoop)

theorem tallyIncrement_executes (out : K) (s : CountdownStore K F) :
    (tallyIncrementRoutine out).Executes s (tallyIncrementEval out s) 2 := by
  cases hg : countdownGuard s.state with
  | false =>
      simpa [tallyIncrementRoutine, tallyIncrementEval, hg, cleanupNoop, Op.apply] using
        RoutineControl.branch_false countdownGuard (Atom.routine (tallyPushOp out))
          (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop s)
  | true =>
      simpa [tallyIncrementRoutine, tallyIncrementEval, hg] using
        RoutineControl.branch_true countdownGuard (Atom.routine (tallyPushOp out))
          (Atom.routine cleanupNoop) hg (Atom.executes (tallyPushOp out) s)

def tallyBodyEval (p : RangeCursorPorts K) (out : K) (q : List Bool → Bool)
    (s : CountdownStore K F) : CountdownStore K F :=
  forestSyntaxStartOp.apply (tallyIncrementEval out (maskedBodyEval p q s))

def tallyBodyRoutine (p : RangeCursorPorts K) (out : K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (maskedBodyRoutine p query)
    (RoutineComposition.seq (tallyIncrementRoutine out) (Atom.routine forestSyntaxStartOp))

theorem tallyBody_state (p : RangeCursorPorts K) (out : K) (q : List Bool → Bool)
    (s : CountdownStore K F) :
    (tallyBodyEval p out q s).state = ((s.state.1.1, (s.stk (p .mask)).head?.getD false), true) := by
  unfold tallyBodyEval tallyIncrementEval
  split <;> rfl

theorem tallyBody_stacks (p : RangeCursorPorts K) (out : K) (q : List Bool → Bool)
    (s : CountdownStore K F) :
    (tallyBodyEval p out q s).stk =
      if (s.stk (p .mask)).head?.getD false && q (s.stk (p .word)) then
        Function.update (maskedBodyEval p q s).stk out (true :: (maskedBodyEval p q s).stk out)
      else (maskedBodyEval p q s).stk := by
  cases hm : (s.stk (p .mask)).head?.getD false <;>
    simp [tallyBodyEval, tallyIncrementEval, maskedBodyEval, countdownGuard,
      hm, tallyPushOp, forestSyntaxStartOp, Op.apply]

theorem tallyBody_extra (p : RangeCursorPorts K) (out : K) (q : List Bool → Bool)
    (s : CountdownStore K F) (j : K) (hjo : j ≠ out) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) :
    (tallyBodyEval p out q s).stk j = s.stk j := by
  rw [tallyBody_stacks]
  split <;> simp [hjo, maskedBody_extra p q s j hjw hjm]

theorem tallyBody_executes (p : RangeCursorPorts K) (out : K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) (q : List Bool → Bool)
    (I : (K → List Bool) → Prop) (M : ℕ) (h : MaskedQueryContract p query q I M)
    (s : CountdownStore K F) (hs : I s.stk) :
    ∃ n ≤ M + 7, (tallyBodyRoutine p out query).Executes s (tallyBodyEval p out q s) n := by
  obtain ⟨a, ha, h1⟩ := maskedBody_executes p query q I M h s hs
  have h2 := tallyIncrement_executes out (maskedBodyEval p q s)
  have h3 := Atom.executes (forestSyntaxStartOp (K := K) (F := F))
    (tallyIncrementEval out (maskedBodyEval p q s))
  exact ⟨a + (2 + 1), by omega,
    RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)⟩

def tallyCountdownContract (p : RangeCursorPorts K) (out : K)
    (hoc : out ≠ p .counter)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) (q : List Bool → Bool)
    (I : (K → List Bool) → Prop) (M : ℕ) (h : MaskedQueryContract p query q I M)
    (hpush : ∀ stk, I stk → I (Function.update stk out (true :: stk out))) :
    CountdownContract (p .counter) (tallyBodyRoutine p out query) (tallyBodyEval p out q)
      (fun s => I s.stk) (M + 7) where
  peek_closed s hs := hs
  pop_closed s hs hg := h.counter_closed s.stk hs
  body_closed s hs := by
    rw [tallyBody_stacks]
    have hi := h.cursor_closed s.stk hs
    split
    · exact hpush (maskedBodyEval p q s).stk hi
    · exact hi
  reset_closed s hs := hs
  counter_preserved s hs := tallyBody_extra p out q s (p .counter) hoc.symm (by simp) (by simp)
  body_executes s hs := tallyBody_executes p out query q I M h s hs

theorem tallyLoop_flag (p : RangeCursorPorts K) (out : K) (q : List Bool → Bool) (fuel : ℕ) :
    ∀ s : CountdownStore K F, s.state.2 = true →
      (countdownLoopEval (p .counter) (tallyBodyEval p out q) fuel s).state.2 = true := by
  induction fuel with
  | zero => intro s hs; exact hs
  | succ fuel ih =>
      intro s hs
      cases hg : countdownGuard s.state with
      | false => simpa only [countdownLoopEval, hg, Bool.false_eq_true, ↓reduceIte] using hs
      | true =>
          simp only [countdownLoopEval, hg, ↓reduceIte]
          apply ih
          change (tallyBodyEval p out q (countdownPop (p .counter) s)).state.2 = true
          rw [tallyBody_state]

theorem tallyLoop_output (p : RangeCursorPorts K) (out : K)
    (how : out ≠ p .word) (hom : out ≠ p .mask) (hoc : out ≠ p .counter)
    (q : List Bool → Bool) (fuel : ℕ) :
    ∀ s : CountdownStore K F, s.state.2 = true →
      (s.stk (p .counter)).length = (s.stk (p .mask)).length →
      (s.stk (p .mask)).length ≤ (s.stk (p .word)).length →
      (s.stk (p .counter)).length ≤ fuel →
      s.state.1.2 = (s.stk (p .counter)).head?.isSome →
      (countdownLoopEval (p .counter) (tallyBodyEval p out q) fuel s).stk out =
        List.replicate (maskedTally q (s.stk (p .word)) (s.stk (p .mask))) true ++ s.stk out := by
  induction fuel with
  | zero =>
      intro s hf hsame hfit hlen hpeek
      have hm : s.stk (p .mask) = [] := List.eq_nil_of_length_eq_zero (by omega)
      cases hw : s.stk (p .word) <;> simp [countdownLoopEval, maskedTally, hm, hw]
  | succ fuel ih =>
      intro s hf hsame hfit hlen hpeek
      cases hm : s.stk (p .mask) with
      | nil =>
          have hc : s.stk (p .counter) = [] := List.eq_nil_of_length_eq_zero (by simpa [hm] using hsame)
          cases hw : s.stk (p .word) <;>
            simp [countdownLoopEval, countdownGuard, hpeek, hc, hm, hw, maskedTally]
      | cons mark mask =>
          cases hw : s.stk (p .word) with
          | nil => simp [hm, hw] at hfit
          | cons bit bits =>
              have hc : (s.stk (p .counter)).head?.isSome = true := by
                cases hcs : s.stk (p .counter) with
                | nil => simp [hcs, hm] at hsame
                | cons c cs => rfl
              have hg : countdownGuard s.state = true := by simp [countdownGuard, hpeek, hc, hf]
              let u := countdownPeek (p .counter) (tallyBodyEval p out q (countdownPop (p .counter) s))
              have hustk := tallyBody_stacks p out q (countdownPop (p .counter) s)
              have huw : u.stk (p .word) = bits := by
                change (tallyBodyEval p out q (countdownPop (p .counter) s)).stk (p .word) = _
                rw [hustk]
                split <;> simp [maskedBodyEval, countdownPop, countdownPopOp, Op.apply, how.symm, hw]
              have hum : u.stk (p .mask) = mask := by
                change (tallyBodyEval p out q (countdownPop (p .counter) s)).stk (p .mask) = _
                rw [hustk]
                split <;> simp [maskedBodyEval, countdownPop, countdownPopOp, Op.apply, hom.symm, hm]
              have huc : u.stk (p .counter) = (s.stk (p .counter)).tail := by
                change (tallyBodyEval p out q (countdownPop (p .counter) s)).stk (p .counter) = _
                rw [tallyBody_extra p out q _ (p .counter) hoc.symm (by simp) (by simp), countdownPop_counter]
              have huo : u.stk out =
                  if mark && q (bit :: bits) then true :: s.stk out else s.stk out := by
                change (tallyBodyEval p out q (countdownPop (p .counter) s)).stk out = _
                rw [hustk]
                simp [maskedBodyEval, countdownPop, countdownPopOp, Op.apply, hoc, how, hom, hw, hm]
              have huf : u.state.2 = true := by
                change (tallyBodyEval p out q (countdownPop (p .counter) s)).state.2 = true
                rw [tallyBody_state]
              have husame : (u.stk (p .counter)).length = (u.stk (p .mask)).length := by
                rw [huc, hum]
                cases hcs : s.stk (p .counter) with
                | nil => simp [hcs, hm] at hsame
                | cons c cs => simpa [hcs, hm] using hsame
              have hufit : (u.stk (p .mask)).length ≤ (u.stk (p .word)).length := by
                rw [hum, huw]; simpa [hm, hw] using hfit
              have hulen : (u.stk (p .counter)).length ≤ fuel := by
                rw [huc]
                cases hcs : s.stk (p .counter) with
                | nil => simp
                | cons c cs => simpa [hcs] using hlen
              have hi := ih u huf husame hufit hulen (countdownPeek_control (p .counter) _)
              simp only [countdownLoopEval, hg, ↓reduceIte]
              rw [hi, huw, hum, huo]
              cases hmark : mark && q (bit :: bits) with
              | false => simp [maskedTally, hw, hm, hmark]
              | true =>
                  simp only [maskedTally, hw, hm, hmark, ↓reduceIte]
                  have hrep : List.replicate (1 + maskedTally q bits mask) true =
                      List.replicate (maskedTally q bits mask) true ++ [true] := by
                    rw [Nat.add_comm, ← List.replicate_append_replicate]
                    rfl
                  rw [hrep, List.append_assoc]
                  rfl

theorem tallyLoop_lengths (p : RangeCursorPorts K) (out : K) (q : List Bool → Bool) (fuel : ℕ) :
    ∀ (s : CountdownStore K F) (j : K), j ≠ out →
      ((countdownLoopEval (p .counter) (tallyBodyEval p out q) fuel s).stk j).length ≤ (s.stk j).length := by
  induction fuel with
  | zero => intro s j hjo; exact le_refl _
  | succ fuel ih =>
      intro s j hjo
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          have hpop : ((countdownPop (p .counter) s).stk j).length ≤ (s.stk j).length := by
            by_cases hj : j = p .counter
            · subst j; rw [countdownPop_counter]; cases s.stk (p .counter) <;> simp
            · simp [countdownPop, countdownPopOp, Op.apply, hj]
          have hb : ((tallyBodyEval p out q (countdownPop (p .counter) s)).stk j).length ≤
              ((countdownPop (p .counter) s).stk j).length := by
            rw [tallyBody_stacks]
            split <;> simpa [hjo] using maskedBody_lengths p q (countdownPop (p .counter) s) j
          have hi := ih (countdownPeek (p .counter) (tallyBodyEval p out q (countdownPop (p .counter) s))) j hjo
          simpa only [countdownLoopEval, hg, ↓reduceIte] using hi.trans (hb.trans hpop)

def tallyAllRoutine (p : RangeCursorPorts K) (out : K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) :=
  RoutineComposition.seq (rangeAllPrepareRoutine p)
    (RoutineComposition.seq (countdownRoutine (p .counter) (tallyBodyRoutine p out query))
      (clearManyRoutine (rangeCursorOwned p)))

def tallyAllResult (p : RangeCursorPorts K) (out : K) (q : List Bool → Bool)
    (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false), true), Function.update s.stk out
    (List.replicate (maskedTally q (s.stk (p .originalWord)) (s.stk (p .originalMask))) true ++ s.stk out)⟩

theorem tallyAll_executes (p : RangeCursorPorts K) (out : K)
    (hout : ∀ j : RangeCursorPort, out ≠ p j)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) (q : List Bool → Bool)
    (I : (K → List Bool) → Prop) (M L : ℕ) (h : MaskedQueryContract p query q I M)
    (hpush : ∀ stk, I stk → I (Function.update stk out (true :: stk out)))
    (s : CountdownStore K F)
    (hL : (s.stk (p .originalWord)).length ≤ L)
    (hfit : (s.stk (p .originalMask)).length ≤ (s.stk (p .originalWord)).length)
    (hw0 : s.stk (p .word) = []) (hm0 : s.stk (p .mask) = [])
    (hc0 : s.stk (p .counter) = []) (ht0 : s.stk (p .temp) = [])
    (hi : I (rangeAllPrepared p s).stk) :
    ∃ n ≤ L * (M + 10) + 12 * L + 17,
      (tallyAllRoutine p out query).Executes s (tallyAllResult p out q s) n := by
  let u := rangeAllPrepared p s
  let v := countdownEval (p .counter) (tallyBodyEval p out q) u
  have hustk := rangeAllPrepared_stacks p s hw0 hm0 hc0
  have huw : u.stk (p .word) = s.stk (p .originalWord) := by simp [u, hustk]
  have hum : u.stk (p .mask) = s.stk (p .originalMask) := by simp [u, hustk]
  have huc : u.stk (p .counter) = s.stk (p .originalMask) := by simp [u, hustk]
  have hux (j : K) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) (hjc : j ≠ p .counter) :
      u.stk j = s.stk j := by simp [u, hustk, hjw, hjm, hjc]
  have hprep := rangeAllPrepare_executes p s ht0 hm0
  obtain ⟨a, ha, hrun, hvinv, hvguard, hvexhaust⟩ := countdownRoutine_executes (p .counter)
    (tallyBodyRoutine p out query) (tallyBodyEval p out q) (fun t => I t.stk) (M + 7)
    (tallyCountdownContract p out (hout .counter) query q I M h hpush) u hi
  have hvflag : v.state.2 = true := tallyLoop_flag p out q (u.stk (p .counter)).length
    (countdownPeek (p .counter) u) rfl
  have hvout : v.stk out = List.replicate
      (maskedTally q (s.stk (p .originalWord)) (s.stk (p .originalMask))) true ++ s.stk out := by
    have hh := tallyLoop_output p out (hout .word) (hout .mask) (hout .counter) q
      (u.stk (p .counter)).length (countdownPeek (p .counter) u) rfl
      (by rw [huc, hum]) (by rw [hum, huw]; exact hfit) (le_refl _)
      (countdownPeek_control (p .counter) u)
    simpa only [huw, hum, hux out (hout .word) (hout .mask) (hout .counter)] using hh
  have hvframe : v.state.1.1 = s.state.1.1 := by
    exact countdownLoop_preserves (p .counter) (tallyBodyEval p out q) (fun t => t.state.1.1)
      (fun _ => rfl) (fun _ => rfl) (fun t => congrArg (fun st => st.1.1) (tallyBody_state p out q t))
      (u.stk (p .counter)).length (countdownPeek (p .counter) u)
  have hvextra (j : K) (hjo : j ≠ out) (hjw : j ≠ p .word)
      (hjm : j ≠ p .mask) (hjc : j ≠ p .counter) : v.stk j = s.stk j := by
    have hh := countdownLoop_preserves (p .counter) (tallyBodyEval p out q) (fun t => t.stk j)
      (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hjc])
      (fun t => tallyBody_extra p out q t j hjo hjw hjm)
      (u.stk (p .counter)).length (countdownPeek (p .counter) u)
    exact hh.trans (hux j hjw hjm hjc)
  have hvlen (j : K) (hjo : j ≠ out) : (v.stk j).length ≤ (u.stk j).length :=
    tallyLoop_lengths p out q (u.stk (p .counter)).length (countdownPeek (p .counter) u) j hjo
  have hvw := hvlen (p .word) (hout .word).symm
  have hvm := hvlen (p .mask) (hout .mask).symm
  have hvc := hvlen (p .counter) (hout .counter).symm
  rw [huw] at hvw
  rw [hum] at hvm
  rw [huc] at hvc
  obtain ⟨b, hb, hclear⟩ := clearMany_executes (rangeCursorOwned p) v
  have hmass : cleanupMass (rangeCursorOwned p) v ≤ 3 * L := by
    simp only [cleanupMass, rangeCursorOwned, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hresult : clearManyEval (rangeCursorOwned p) v = tallyAllResult p out q s := by
    apply countdownStore_ext
    · rw [clearMany_state]
      exact Prod.ext (Prod.ext hvframe hvguard) hvflag
    · funext j
      by_cases hjo : j = out
      · subst j
        rw [clearMany_outside _ _ (by simp [rangeCursorOwned, hout]), Function.update_same]
        exact hvout
      · rw [Function.update_of_ne hjo]
        by_cases hj : j ∈ rangeCursorOwned p
        · rw [clearMany_member _ _ hj]
          simp only [rangeCursorOwned, List.mem_cons, List.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl
          · exact hw0.symm
          · exact hm0.symm
          · exact hc0.symm
        · rw [clearMany_outside _ _ hj]
          apply hvextra j hjo
          · intro he; apply hj; simp [rangeCursorOwned, he]
          · intro he; apply hj; simp [rangeCursorOwned, he]
          · intro he; apply hj; simp [rangeCursorOwned, he]
  have he := RoutineComposition.seq_executes _ _ hprep (RoutineComposition.seq_executes _ _ hrun hclear)
  rw [hresult] at he
  refine ⟨(3 * (s.stk (p .originalWord)).length + 6 * (s.stk (p .originalMask)).length + 10) + (a + b), ?_, he⟩
  rw [huc] at ha
  simp only [rangeCursorOwned, List.length_cons, List.length_nil] at hb
  have hmul := Nat.mul_le_mul_right (M + 10) (hfit.trans hL)
  omega

end PolytomyReductionModel.WholeVerifierController
