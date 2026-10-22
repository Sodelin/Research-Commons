/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual multiport Routine-level counted loops, with a PHYSICAL stack
counter, finite guard/success bits and early failure. A body's exact
semantics, invariant, preservation and transition bound are explicit
premises, not assumed library axioms. This combinator is intended for
the original nested row/entry parser; its instances remain to be supplied.
-/
import PolytomyUnaryRecordNormalForm
import Lax218471Proofs.RoutineControl
import Lax218471Proofs.Atom

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

/-- F is the caller's finite frame. The first Bool is this loop's cached
    nonemptiness guard; the last Bool is the parser success flag. -/
abbrev CountdownState (F : Type) := (F × Bool) × Bool
abbrev CountdownStore (K F : Type) := Store (fun _ : K => Bool) (CountdownState F)

def countdownGuard (s : CountdownState F) : Bool := s.1.2 && s.2

def countdownPeekOp (counter : K) : Op K Bool (CountdownState F) :=
  .peek counter (fun s h => ((s.1.1, h.isSome), s.2))
def countdownPopOp (counter : K) : Op K Bool (CountdownState F) :=
  .pop counter (fun s _ => s)
def countdownResetOp : Op K Bool (CountdownState F) :=
  .load (fun s => ((s.1.1, false), s.2))

def countdownPeek (counter : K) (s : CountdownStore K F) : CountdownStore K F :=
  (countdownPeekOp counter).apply s
def countdownPop (counter : K) (s : CountdownStore K F) : CountdownStore K F :=
  (countdownPopOp counter).apply s
def countdownReset (s : CountdownStore K F) : CountdownStore K F :=
  countdownResetOp.apply s

def countdownBodyStep (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F)) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (countdownPopOp counter))
    (RoutineComposition.seq body (Atom.routine (countdownPeekOp counter)))

def countdownRoutine (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F)) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (countdownPeekOp counter))
    (RoutineComposition.seq
      (RoutineControl.loop countdownGuard (countdownBodyStep counter body))
      (Atom.routine countdownResetOp))

/-- Fuel is used only in the mathematical semantics. The actual routine
    above does NOT store a Nat in its finite control. -/
def countdownLoopEval (counter : K) (f : CountdownStore K F → CountdownStore K F) :
    ℕ → CountdownStore K F → CountdownStore K F
  | 0, s => s
  | n + 1, s =>
      if countdownGuard s.state then
        countdownLoopEval counter f n (countdownPeek counter (f (countdownPop counter s)))
      else s

def countdownEval (counter : K) (f : CountdownStore K F → CountdownStore K F)
    (s : CountdownStore K F) : CountdownStore K F :=
  countdownReset
    (countdownLoopEval counter f (s.stk counter).length (countdownPeek counter s))

/-- These are operational proof obligations for the ACTUAL supplied body.
    The invariant must cover intermediate/failing states, not only a final
    successfully parsed record. The counter is reserved from body writes. -/
structure CountdownContract (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F))
    (f : CountdownStore K F → CountdownStore K F)
    (Inv : CountdownStore K F → Prop) (M : ℕ) : Prop where
  peek_closed : ∀ s, Inv s → Inv (countdownPeek counter s)
  pop_closed : ∀ s, Inv s → countdownGuard s.state = true → Inv (countdownPop counter s)
  body_closed : ∀ s, Inv s → Inv (f s)
  reset_closed : ∀ s, Inv s → Inv (countdownReset s)
  counter_preserved : ∀ s, Inv s → (f s).stk counter = s.stk counter
  body_executes : ∀ s, Inv s → ∃ n ≤ M, body.Executes s (f s) n

theorem countdownPeek_control (counter : K) (s : CountdownStore K F) :
    (countdownPeek counter s).state.1.2 =
      ((countdownPeek counter s).stk counter).head?.isSome := by rfl

theorem countdownPop_counter (counter : K) (s : CountdownStore K F) :
    (countdownPop counter s).stk counter = (s.stk counter).tail := by
  simp [countdownPop, countdownPopOp, Op.apply]

theorem countdownBodyStep_executes (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F))
    (f : CountdownStore K F → CountdownStore K F) (s : CountdownStore K F)
    (n : ℕ) (h : body.Executes (countdownPop counter s) (f (countdownPop counter s)) n) :
    (countdownBodyStep counter body).Executes s
      (countdownPeek counter (f (countdownPop counter s))) (n + 2) := by
  have hp := Atom.executes (countdownPopOp counter) s
  have hq := Atom.executes (countdownPeekOp counter) (f (countdownPop counter s))
  have hr := RoutineComposition.seq_executes body (Atom.routine (countdownPeekOp counter)) h hq
  have ht := RoutineComposition.seq_executes (Atom.routine (countdownPopOp counter))
    (RoutineComposition.seq body (Atom.routine (countdownPeekOp counter))) hp hr
  simpa only [countdownBodyStep, countdownPop, countdownPeek, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using ht

/-- Exact operational realization, including final loop dispatch. The
    returned state has a faithful cached guard and has stopped either on
    failure or on an exhausted physical counter. -/
theorem countdownLoop_executes (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F))
    (f : CountdownStore K F → CountdownStore K F) (Inv : CountdownStore K F → Prop)
    (M : ℕ) (hc : CountdownContract counter body f Inv M) (fuel : ℕ) :
    ∀ s, Inv s → (s.stk counter).length ≤ fuel →
      s.state.1.2 = (s.stk counter).head?.isSome →
      ∃ n ≤ fuel * (M + 3) + 1,
        (RoutineControl.loop countdownGuard (countdownBodyStep counter body)).Executes s
          (countdownLoopEval counter f fuel s) n ∧
        Inv (countdownLoopEval counter f fuel s) ∧
        countdownGuard (countdownLoopEval counter f fuel s).state = false ∧
        (countdownLoopEval counter f fuel s).state.1.2 =
          ((countdownLoopEval counter f fuel s).stk counter).head?.isSome := by
  induction fuel with
  | zero =>
      intro s hs hlen hpeek
      have hz : s.stk counter = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hg : countdownGuard s.state = false := by simp [countdownGuard, hpeek, hz]
      refine ⟨1, by simp, ?_, hs, hg, hpeek⟩
      exact RoutineControl.loop_false countdownGuard (countdownBodyStep counter body) s hg
  | succ fuel ih =>
      intro s hs hlen hpeek
      cases hg : countdownGuard s.state with
      | false =>
          refine ⟨1, by omega, ?_, ?_, ?_, ?_⟩
          · simpa only [countdownLoopEval, hg, Bool.false_eq_true, ↓reduceIte] using
              RoutineControl.loop_false countdownGuard (countdownBodyStep counter body) s hg
          · simpa only [countdownLoopEval, hg, Bool.false_eq_true, ↓reduceIte] using hs
          · simpa only [countdownLoopEval, hg, Bool.false_eq_true, ↓reduceIte] using hg
          · simpa only [countdownLoopEval, hg, Bool.false_eq_true, ↓reduceIte] using hpeek
      | true =>
          have hpop := hc.pop_closed s hs hg
          obtain ⟨m, hm, hbody⟩ := hc.body_executes (countdownPop counter s) hpop
          let u := countdownPeek counter (f (countdownPop counter s))
          have hu : Inv u := hc.peek_closed _ (hc.body_closed _ hpop)
          have huCounter : u.stk counter = (s.stk counter).tail := by
            change (f (countdownPop counter s)).stk counter = (s.stk counter).tail
            rw [hc.counter_preserved _ hpop, countdownPop_counter]
          have huLen : (u.stk counter).length ≤ fuel := by
            rw [huCounter]
            cases hw : s.stk counter with
            | nil => simp [countdownGuard, hpeek, hw] at hg
            | cons b bs =>
                simp only [hw, List.length_cons] at hlen
                simp only [List.tail_cons]
                omega
          obtain ⟨n, hn, hrun, hinv, hstop, hfaith⟩ :=
            ih u hu huLen (countdownPeek_control counter _)
          have hstep := countdownBodyStep_executes counter body f s m hbody
          have hall := RoutineControl.loop_true countdownGuard (countdownBodyStep counter body)
            hg hstep hrun
          refine ⟨(m + 2) + n + 1, ?_, ?_, ?_, ?_, ?_⟩
          · nlinarith
          · simpa only [countdownLoopEval, hg, ↓reduceIte, u] using hall
          · simpa only [countdownLoopEval, hg, ↓reduceIte, u] using hinv
          · simpa only [countdownLoopEval, hg, ↓reduceIte, u] using hstop
          · simpa only [countdownLoopEval, hg, ↓reduceIte, u] using hfaith

theorem countdownRoutine_executes (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F))
    (f : CountdownStore K F → CountdownStore K F) (Inv : CountdownStore K F → Prop)
    (M : ℕ) (hc : CountdownContract counter body f Inv M)
    (s : CountdownStore K F) (hs : Inv s) :
    ∃ n ≤ (s.stk counter).length * (M + 3) + 3,
      (countdownRoutine counter body).Executes s (countdownEval counter f s) n ∧
      Inv (countdownEval counter f s) ∧
      (countdownEval counter f s).state.1.2 = false ∧
      ((countdownEval counter f s).state.2 = true →
        (countdownEval counter f s).stk counter = []) := by
  let p := countdownPeek counter s
  obtain ⟨n, hn, hloop, hi, hstop, hfaith⟩ :=
    countdownLoop_executes counter body f Inv M hc (s.stk counter).length p
      (hc.peek_closed s hs) (le_refl _) (countdownPeek_control counter s)
  let t := countdownLoopEval counter f (s.stk counter).length p
  have htail := RoutineComposition.seq_executes
    (RoutineControl.loop countdownGuard (countdownBodyStep counter body))
    (Atom.routine countdownResetOp) hloop (Atom.executes countdownResetOp t)
  have hfull := RoutineComposition.seq_executes (Atom.routine (countdownPeekOp counter))
    (RoutineComposition.seq (RoutineControl.loop countdownGuard (countdownBodyStep counter body))
      (Atom.routine countdownResetOp)) (Atom.executes (countdownPeekOp counter) s) htail
  refine ⟨n + 2, by omega, ?_, hc.reset_closed t hi, rfl, ?_⟩
  · simpa only [countdownRoutine, countdownEval, countdownPeek, countdownReset, p, t,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfull
  · intro hok
    have ht : t.state.2 = true := hok
    have hnempty : (t.stk counter).head?.isSome = false := by
      change countdownGuard t.state = false at hstop
      change t.state.1.2 = (t.stk counter).head?.isSome at hfaith
      simpa only [countdownGuard, ht, Bool.and_true, hfaith] using hstop
    change t.stk counter = []
    cases hw : t.stk counter with
    | nil => rfl
    | cons b bs => simp [hw] at hnempty

/- This actual loop code and conditional body-composition theorem are NOT
the full nested parser. Each inner/outer body still needs its concrete
reader/output/copy code and a valid CountdownContract, including failing
partial-storage states. A counter cannot alias a body output/work port.
Success exhausts the counter; early failure may leave its suffix, so the
whole parser must clear it before returning. Two nested loops have distinct
counter ports and cached guard bits. Full constructor/checker, compatible
closed hardness and every kernel check remain open. No runtime was used.
-/

end PolytomyReductionModel
