/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original-word replay at a PHYSICAL unary index. Restoring copies
build U(index) ++ word; the existing actual raw-frame parser consumes the
prefix, then owned discard data are physically cleared. No host drop or
unbounded finite-control index is assumed. Tree-node legality is separate.
-/
import PolytomyGuardedUnaryField

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive ReplayPort where
  | original | index | temp | source | discarded
  deriving DecidableEq, Fintype

abbrev ReplayPorts (K : Type) := ReplayPort ↪ K

variable {K F : Type} [DecidableEq K]

@[simp] theorem replayPorts_eq (p : ReplayPorts K) (a b : ReplayPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def replayDelimiterOp (p : ReplayPorts K) : Op K Bool (CountdownState F) :=
  .push (p .source) (fun _ => false)

def replayPrepareRoutine (p : ReplayPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p .original) (p .temp) (p .source))
    (RoutineComposition.seq (Atom.routine (replayDelimiterOp p))
      (RoutineComposition.seq (wordDuplicateRoutine (p .index) (p .temp) (p .source))
        (Atom.routine unaryFieldStartOp)))

def replayPrepareEval (p : ReplayPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  unaryFieldStartOp.apply (wordDuplicateEval (p .index) (p .source)
    ((replayDelimiterOp p).apply (wordDuplicateEval (p .original) (p .source) s)))

def replayPreparedStore (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  frameCallerStore (p .source) (p .discarded) s.stk s.state.1 false
    (unaryFrame I ++ s.stk (p .original)) []

theorem replayPrepare_effect (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F)
    (hs : s.stk (p .source) = []) (hd : s.stk (p .discarded) = [])
    (hi : s.stk (p .index) = List.replicate I true) :
    replayPrepareEval p s = replayPreparedStore p I s := by
  apply countdownStore_ext
  · rfl
  · funext k
    by_cases hk : k = p .source
    · subst k
      simp [replayPrepareEval, replayPreparedStore, wordDuplicateEval,
        replayDelimiterOp, unaryFieldStartOp, Op.apply, frameCallerStore,
        hs, hi, unaryFrame, List.append_assoc]
    · by_cases hkd : k = p .discarded
      · subst k
        simp [replayPrepareEval, replayPreparedStore, wordDuplicateEval,
          replayDelimiterOp, unaryFieldStartOp, Op.apply, frameCallerStore, hd]
      · simp [replayPrepareEval, replayPreparedStore, wordDuplicateEval,
          replayDelimiterOp, unaryFieldStartOp, Op.apply, frameCallerStore, hk, hkd]

theorem replayPrepare_executes (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F)
    (hs : s.stk (p .source) = []) (hd : s.stk (p .discarded) = [])
    (ht : s.stk (p .temp) = []) (hi : s.stk (p .index) = List.replicate I true) :
    (replayPrepareRoutine p).Executes s (replayPreparedStore p I s)
      (3 * (s.stk (p .original)).length + 3 * I + 8) := by
  let u₁ := wordDuplicateEval (p .original) (p .source) s
  let u₂ := (replayDelimiterOp p).apply u₁
  let u₃ := wordDuplicateEval (p .index) (p .source) u₂
  have ht₂ : u₂.stk (p .temp) = [] := by simp [u₂, u₁, replayDelimiterOp, Op.apply, wordDuplicateEval, ht]
  have hi₂ : u₂.stk (p .index) = List.replicate I true := by
    simp [u₂, u₁, replayDelimiterOp, Op.apply, wordDuplicateEval, hi]
  have h₁ := wordDuplicate_executes (p .original) (p .temp) (p .source)
    (by simp) (by simp) (by simp) s ht
  have h₂ := Atom.executes (replayDelimiterOp p) u₁
  have h₃ := wordDuplicate_executes (p .index) (p .temp) (p .source)
    (by simp) (by simp) (by simp) u₂ ht₂
  rw [hi₂, List.length_replicate] at h₃
  have h₄ := Atom.executes (unaryFieldStartOp (K := K) (F := F)) u₃
  have h₃₄ := RoutineComposition.seq_executes
    (wordDuplicateRoutine (p .index) (p .temp) (p .source)) (Atom.routine unaryFieldStartOp) h₃ h₄
  have h₂₃₄ := RoutineComposition.seq_executes (Atom.routine (replayDelimiterOp p))
    (RoutineComposition.seq (wordDuplicateRoutine (p .index) (p .temp) (p .source))
      (Atom.routine unaryFieldStartOp)) h₂ h₃₄
  have hall := RoutineComposition.seq_executes
    (wordDuplicateRoutine (p .original) (p .temp) (p .source))
    (RoutineComposition.seq (Atom.routine (replayDelimiterOp p))
      (RoutineComposition.seq (wordDuplicateRoutine (p .index) (p .temp) (p .source))
        (Atom.routine unaryFieldStartOp))) h₁ h₂₃₄
  rw [← replayPrepare_effect p I s hs hd hi]
  convert hall using 1 <;>
    simp only [replayPrepareRoutine, replayPrepareEval, u₁, u₂, u₃] <;> omega

theorem readRawBinaryFrame_replay (I : ℕ) (bits : List Bool) :
    readRawBinaryFrame (unaryFrame I ++ bits) =
      if I ≤ bits.length then some (bits.take I, bits.drop I) else none := by
  simp only [readRawBinaryFrame, readUnaryFrame_encode]

def replayAfterFrame (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  frameCallerResult (p .source) (p .discarded) s.stk s.state.1
    (readRawBinaryFrame (unaryFrame I ++ s.stk (p .original)))

def replaySuffixResult (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  if I ≤ (s.stk (p .original)).length then
    frameCallerStore (p .source) (p .discarded) s.stk s.state.1 true
      ((s.stk (p .original)).drop I) []
  else frameCallerStore (p .source) (p .discarded) s.stk s.state.1 false [] []

theorem replayAfterFrame_discard_bound (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) :
    ((replayAfterFrame p I s).stk (p .discarded)).length ≤ I := by
  by_cases h : I ≤ (s.stk (p .original)).length
  · simp [replayAfterFrame, readRawBinaryFrame_replay, h, frameCallerResult,
      frameCallerStore, List.length_take]
  · simp [replayAfterFrame, readRawBinaryFrame_replay, h, frameCallerResult, frameCallerStore]

theorem replayClear_effect (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) :
    clearStackEval (p .discarded) (replayAfterFrame p I s) = replaySuffixResult p I s := by
  by_cases h : I ≤ (s.stk (p .original)).length
  all_goals
    apply countdownStore_ext
    · simp [clearStackEval, replayAfterFrame, replaySuffixResult,
        readRawBinaryFrame_replay, h, frameCallerResult, frameCallerStore]
    · funext k
      by_cases hk : k = p .discarded <;>
        simp [clearStackEval, replayAfterFrame, replaySuffixResult,
          readRawBinaryFrame_replay, h, frameCallerResult, frameCallerStore, hk]

def replaySuffixRoutine (p : ReplayPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (replayPrepareRoutine p)
    (RoutineComposition.seq (frameCallerRoutine (p .source) (p .discarded) (by simp))
      (clearStackRoutine (p .discarded)))

/-- ALL word values and every physical unary index, including overshoot.
    The input word/index survive. Cost explicitly includes the index size. -/
theorem replaySuffix_executes (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F)
    (hs : s.stk (p .source) = []) (hd : s.stk (p .discarded) = [])
    (ht : s.stk (p .temp) = []) (hi : s.stk (p .index) = List.replicate I true) :
    ∃ n ≤ 5 * (s.stk (p .original)).length + 6 * I + 15,
      (replaySuffixRoutine p).Executes s (replaySuffixResult p I s) n := by
  have hprep := replayPrepare_executes p I s hs hd ht hi
  obtain ⟨n, hn, hparse⟩ := frameCaller_executes (p .source) (p .discarded)
    (by simp) s.stk s.state.1 (unaryFrame I ++ s.stk (p .original))
  have hclear := clearStack_executes (p .discarded) (replayAfterFrame p I s)
  rw [replayClear_effect] at hclear
  have hpc := RoutineComposition.seq_executes
    (frameCallerRoutine (p .source) (p .discarded) (by simp))
    (clearStackRoutine (p .discarded)) hparse hclear
  have hall := RoutineComposition.seq_executes (replayPrepareRoutine p)
    (RoutineComposition.seq (frameCallerRoutine (p .source) (p .discarded) (by simp))
      (clearStackRoutine (p .discarded))) hprep hpc
  have hdlen := replayAfterFrame_discard_bound p I s
  have hlen : (unaryFrame I ++ s.stk (p .original)).length =
      I + 1 + (s.stk (p .original)).length := by simp [unaryFrame]; omega
  rw [hlen] at hn
  refine ⟨(3 * (s.stk (p .original)).length + 3 * I + 8) +
    (n + (((replayAfterFrame p I s).stk (p .discarded)).length + 1)), by omega, ?_⟩
  exact hall

theorem replaySuffix_observation (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) :
    (if (replaySuffixResult p I s).state.2 then
      some ((replaySuffixResult p I s).stk (p .source)) else none) =
      if I ≤ (s.stk (p .original)).length then some ((s.stk (p .original)).drop I) else none := by
  by_cases h : I ≤ (s.stk (p .original)).length <;>
    simp [replaySuffixResult, h, frameCallerStore]

theorem replaySuffix_source (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) :
    (replaySuffixResult p I s).stk (p .source) = (s.stk (p .original)).drop I := by
  by_cases h : I ≤ (s.stk (p .original)).length
  · simp [replaySuffixResult, h, frameCallerStore]
  · have hd : (s.stk (p .original)).drop I = [] := List.drop_eq_nil_of_le (by omega)
    simp [replaySuffixResult, h, frameCallerStore, hd]

theorem replaySuffix_source_bound (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F) :
    ((replaySuffixResult p I s).stk (p .source)).length ≤ (s.stk (p .original)).length := by
  rw [replaySuffix_source, List.length_drop]
  omega

theorem replaySuffix_preserves (p : ReplayPorts K) (I : ℕ) (s : CountdownStore K F)
    (k : K) (hs : k ≠ p .source) (hd : k ≠ p .discarded) :
    (replaySuffixResult p I s).state.1 = s.state.1 ∧
      (replaySuffixResult p I s).stk (p .discarded) = [] ∧
      (replaySuffixResult p I s).stk k = s.stk k := by
  by_cases h : I ≤ (s.stk (p .original)).length <;>
    simp [replaySuffixResult, h, frameCallerStore, hs, hd]

/- A mask-selected index is proved legal by the separate exact node-mask
   theorem. This routine alone only replays bytes; it does not invent a
   tree, typed cell, clade or complete independent-verifier conclusion. -/

end PolytomyReductionModel
