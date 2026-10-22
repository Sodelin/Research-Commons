/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual failure-absorbing INTERNAL unary field read into a fresh physical
scalar stack. This stores the value, not merely an output log. Entry reset
needed by the primitive is explicit, and skipped after earlier failure.
-/
import PolytomyFaithfulWordCopy

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def unaryFieldStartOp : Op K Bool (CountdownState F) := .load (fun s => (s.1, false))

def guardedUnaryFieldRoutine (source output : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd
    (RoutineComposition.seq (Atom.routine unaryFieldStartOp) (unaryCountRoutine source output))
    (Atom.routine cleanupNoop)

def guardedUnaryFieldEval (source output : K) (s : CountdownStore K F) : CountdownStore K F :=
  if s.state.2 then unaryCallerResult source output s.stk s.state.1 (readUnaryFrame (s.stk source)) else s

theorem guardedUnaryField_executes (source output : K) (hne : source ≠ output)
    (s : CountdownStore K F) (ho : s.stk output = []) (L : ℕ) (hL : (s.stk source).length ≤ L) :
    ∃ n ≤ 2 * L + 4,
      (guardedUnaryFieldRoutine source output).Executes s (guardedUnaryFieldEval source output s) n := by
  cases hf : s.state.2 with
  | false =>
      have he := RoutineControl.branch_false Prod.snd
        (RoutineComposition.seq (Atom.routine unaryFieldStartOp) (unaryCountRoutine source output))
        (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop s)
      refine ⟨2, by omega, ?_⟩
      simpa [guardedUnaryFieldRoutine, guardedUnaryFieldEval, hf, cleanupNoop, Op.apply] using he
  | true =>
      obtain ⟨n, hn, hr⟩ := unaryCount_executes source output hne s.stk s.state.1 (s.stk source)
      have hentry : frameCallerStore source output s.stk s.state.1 false (s.stk source) [] =
          unaryFieldStartOp.apply s := by
        apply countdownStore_ext
        · rfl
        · funext k; by_cases hk : k = output <;> by_cases hks : k = source <;>
            simp_all [frameCallerStore, unaryFieldStartOp, Op.apply]
      rw [hentry] at hr
      have hseq := RoutineComposition.seq_executes (Atom.routine unaryFieldStartOp)
        (unaryCountRoutine source output) (Atom.executes unaryFieldStartOp s) hr
      have hall := RoutineControl.branch_true Prod.snd
        (RoutineComposition.seq (Atom.routine unaryFieldStartOp) (unaryCountRoutine source output))
        (Atom.routine cleanupNoop) hf hseq
      refine ⟨(1 + n) + 1, by omega, ?_⟩
      simpa only [guardedUnaryFieldRoutine, guardedUnaryFieldEval, hf, ↓reduceIte] using hall

theorem guardedUnaryField_source_bound (source output : K) (hne : source ≠ output)
    (s : CountdownStore K F) :
    ((guardedUnaryFieldEval source output s).stk source).length ≤ (s.stk source).length := by
  cases hf : s.state.2 with
  | false => simp [guardedUnaryFieldEval, hf]
  | true =>
      cases hp : readUnaryFrame (s.stk source) with
      | none => simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore, hne]
      | some p =>
          rcases p with ⟨a, rest⟩
          have h := readUnaryFrame_consumption (s.stk source) a rest hp
          simp only [guardedUnaryFieldEval, hf, ↓reduceIte, hp, unaryCallerResult, frameCallerStore,
            Function.update_of_ne hne, Function.update_same]
          omega

theorem guardedUnaryField_output_bound (source output : K) (s : CountdownStore K F)
    (ho : s.stk output = []) :
    ((guardedUnaryFieldEval source output s).stk output).length ≤ (s.stk source).length := by
  cases hf : s.state.2 with
  | false => simp [guardedUnaryFieldEval, hf, ho]
  | true =>
      cases hp : readUnaryFrame (s.stk source) with
      | none => simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore]
      | some p =>
          rcases p with ⟨a, rest⟩
          have h := readUnaryFrame_consumption (s.stk source) a rest hp
          simp only [guardedUnaryFieldEval, hf, ↓reduceIte, hp, unaryCallerResult, frameCallerStore,
            Function.update_same, List.length_replicate]
          omega

theorem guardedUnaryField_extra (source output k : K) (hks : k ≠ source) (hko : k ≠ output)
    (s : CountdownStore K F) :
    (guardedUnaryFieldEval source output s).stk k = s.stk k := by
  cases hf : s.state.2 with
  | false => simp [guardedUnaryFieldEval, hf]
  | true => simpa only [guardedUnaryFieldEval, hf, ↓reduceIte] using
      (unaryCaller_preserves source output k hks hko s.stk s.state.1 (readUnaryFrame (s.stk source))).2

def IsUnaryWord (xs : List Bool) : Prop := xs = List.replicate xs.length true

theorem guardedUnaryField_output_unary (source output : K) (s : CountdownStore K F)
    (ho : s.stk output = []) : IsUnaryWord ((guardedUnaryFieldEval source output s).stk output) := by
  cases hf : s.state.2 with
  | false => simp [IsUnaryWord, guardedUnaryFieldEval, hf, ho]
  | true =>
      cases hp : readUnaryFrame (s.stk source) with
      | none => simp [IsUnaryWord, guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore]
      | some p =>
          rcases p with ⟨a, rest⟩
          simp [IsUnaryWord, guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore]

theorem guardedUnaryField_frame (source output : K) (s : CountdownStore K F) :
    (guardedUnaryFieldEval source output s).state.1 = s.state.1 := by
  cases hf : s.state.2 with
  | false => simp [guardedUnaryFieldEval, hf]
  | true =>
      cases hp : readUnaryFrame (s.stk source) with
      | none => simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore]
      | some p => rcases p with ⟨a, rest⟩; simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore]

theorem guardedUnaryField_observation (source output : K) (hne : source ≠ output)
    (s : CountdownStore K F) :
    observeUnaryCaller source output (guardedUnaryFieldEval source output s) =
      if s.state.2 then readUnaryFrame (s.stk source) else none := by
  cases hf : s.state.2 with
  | false => simp [guardedUnaryFieldEval, hf, observeUnaryCaller]
  | true => simpa only [guardedUnaryFieldEval, hf, ↓reduceIte] using
      unaryCaller_observe source output hne s.stk s.state.1 (readUnaryFrame (s.stk source))

/- The destination must be empty for an actual new read. The false-entry
branch is a real no-op, preserving earlier physical scalars and failure.
Both source/output lengths are controlled on all paths; outside stacks
and the entire caller frame (including its cached guard) are unchanged.
Tag/header and structured row-visitor composition remain next.
-/

end PolytomyReductionModel
