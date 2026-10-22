/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

An ACTUAL instantiation of the physical countdown contract: drain a value
tally into a reversed unary-record buffer, optionally copying its count
to a separate stack. Original failure flags are preserved. This is not
yet the complete nested parser or constructor.
-/
import PolytomyPhysicalCountdown

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem countdownStore_ext {s t : CountdownStore K F}
    (hstate : s.state = t.state) (hstacks : s.stk = t.stk) : s = t := by
  cases s
  cases t
  cases hstate
  cases hstacks
  rfl

def emitStore (value record count : K) (base : K → List Bool)
    (frame : F) (guard flag : Bool) (xs ys zs : List Bool) : CountdownStore K F :=
  ⟨((frame, guard), flag),
    Function.update (Function.update (Function.update base value xs) record ys) count zs⟩

def emitRecordOp (record : K) (b : Bool) : Op K Bool (CountdownState F) :=
  .push record (fun _ => b)
def emitCountOp (count : K) : Op K Bool (CountdownState F) :=
  .push count (fun _ => true)

def emitBody (record count : K) (copy : Bool) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  if copy then RoutineComposition.seq (Atom.routine (emitRecordOp record true))
    (Atom.routine (emitCountOp count))
  else Atom.routine (emitRecordOp record true)

def emitBodyEval (record count : K) (copy : Bool) (s : CountdownStore K F) :
    CountdownStore K F :=
  let u := (emitRecordOp record true).apply s
  if copy then (emitCountOp count).apply u else u

theorem emitBody_executes (record count : K) (copy : Bool) (s : CountdownStore K F) :
    ∃ n ≤ 2, (emitBody record count copy).Executes s (emitBodyEval record count copy s) n := by
  cases copy with
  | false => exact ⟨1, by omega, Atom.executes (emitRecordOp record true) s⟩
  | true =>
      refine ⟨2, by omega, ?_⟩
      exact RoutineComposition.seq_executes (Atom.routine (emitRecordOp record true))
        (Atom.routine (emitCountOp count)) (Atom.executes (emitRecordOp record true) s)
        (Atom.executes (emitCountOp count) ((emitRecordOp record true).apply s))

theorem emitBody_counter (value record count : K) (hvr : value ≠ record)
    (hvc : value ≠ count) (copy : Bool) (s : CountdownStore K F) :
    (emitBodyEval record count copy s).stk value = s.stk value := by
  cases copy <;> simp [emitBodyEval, emitRecordOp, emitCountOp, Op.apply, hvr, hvc]

/-- A concrete contract, not a parameter assumed from a future parser.
    Every body consists of one or two actual constant-time push atoms. -/
def emitCountdownContract (value record count : K) (hvr : value ≠ record)
    (hvc : value ≠ count) (copy : Bool) :
    CountdownContract value (emitBody record count copy)
      (emitBodyEval record count copy) (fun _ : CountdownStore K F => True) 2 where
  peek_closed _ _ := trivial
  pop_closed _ _ _ := trivial
  body_closed _ _ := trivial
  reset_closed _ _ := trivial
  counter_preserved s _ := emitBody_counter value record count hvr hvc copy s
  body_executes s _ := emitBody_executes record count copy s

theorem emitStore_peek (value record count : K) (hvr : value ≠ record)
    (hvc : value ≠ count) (base : K → List Bool) (frame : F)
    (guard flag : Bool) (xs ys zs : List Bool) :
    countdownPeek value (emitStore value record count base frame guard flag xs ys zs) =
      emitStore value record count base frame xs.head?.isSome flag xs ys zs := by
  apply countdownStore_ext
  · simp [countdownPeek, countdownPeekOp, Op.apply, emitStore, hvr, hvc]
  · rfl

theorem emitStore_pop (value record count : K) (hvr : value ≠ record)
    (hvc : value ≠ count) (base : K → List Bool) (frame : F)
    (guard flag b : Bool) (xs ys zs : List Bool) :
    countdownPop value (emitStore value record count base frame guard flag (b :: xs) ys zs) =
      emitStore value record count base frame guard flag xs ys zs := by
  apply countdownStore_ext
  · rfl
  · funext k
    by_cases hk : k = value
    · subst k; simp [countdownPop, countdownPopOp, Op.apply, emitStore, hvr, hvc]
    · by_cases hr : k = record
      · subst k; simp [countdownPop, countdownPopOp, Op.apply, emitStore, hk]
      · by_cases hc : k = count
        · subst k; simp [countdownPop, countdownPopOp, Op.apply, emitStore, hk]
        · simp [countdownPop, countdownPopOp, Op.apply, emitStore, hk, hr, hc]

theorem emitStore_push (value record count : K) (hrc : record ≠ count)
    (base : K → List Bool) (frame : F) (guard flag copy : Bool)
    (xs ys zs : List Bool) :
    emitBodyEval record count copy (emitStore value record count base frame guard flag xs ys zs) =
      emitStore value record count base frame guard flag xs (true :: ys)
        (if copy then true :: zs else zs) := by
  apply countdownStore_ext
  · cases copy <;> rfl
  · funext k
    cases copy <;>
      by_cases hc : k = count <;>
      by_cases hr : k = record <;>
      simp_all [emitBodyEval, emitRecordOp, emitCountOp, Op.apply, emitStore]

theorem emitStore_delimiter (value record count : K) (hrc : record ≠ count)
    (base : K → List Bool) (frame : F) (guard flag : Bool) (xs ys zs : List Bool) :
    (emitRecordOp record false).apply (emitStore value record count base frame guard flag xs ys zs) =
      emitStore value record count base frame guard flag xs (false :: ys) zs := by
  apply countdownStore_ext
  · rfl
  · funext k
    by_cases hc : k = count <;> by_cases hr : k = record <;>
      simp_all [emitRecordOp, Op.apply, emitStore]

theorem emitStore_reset (value record count : K) (base : K → List Bool)
    (frame : F) (guard flag : Bool) (xs ys zs : List Bool) :
    countdownReset (emitStore value record count base frame guard flag xs ys zs) =
      emitStore value record count base frame false flag xs ys zs := by rfl

theorem emitLoop_semantics (value record count : K) (hvr : value ≠ record)
    (hvc : value ≠ count) (hrc : record ≠ count) (copy : Bool)
    (base : K → List Bool) (frame : F) (xs : List Bool) :
    ∀ guard ys zs,
      countdownLoopEval value (emitBodyEval record count copy) xs.length
        (countdownPeek value (emitStore value record count base frame guard true xs ys zs)) =
      emitStore value record count base frame false true []
        (List.replicate xs.length true ++ ys)
        (if copy then List.replicate xs.length true ++ zs else zs) := by
  induction xs with
  | nil =>
      intro guard ys zs
      rw [emitStore_peek value record count hvr hvc]
      cases copy <;> rfl
  | cons b xs ih =>
      intro guard ys zs
      rw [emitStore_peek value record count hvr hvc]
      simp only [List.head?_cons, Option.isSome_some, List.length_cons,
        countdownLoopEval, countdownGuard, emitStore, Bool.true_and, ↓reduceIte]
      -- Re-expose the store wrappers after the guard has been reduced.
      change countdownLoopEval value (emitBodyEval record count copy) xs.length
        (countdownPeek value (emitBodyEval record count copy
          (countdownPop value (emitStore value record count base frame true true (b :: xs) ys zs)))) = _
      rw [emitStore_pop value record count hvr hvc,
        emitStore_push value record count hrc, ih]
      cases copy <;> simp only [Bool.false_eq_true, Bool.true_eq_true, ↓reduceIte,
        List.replicate_succ', List.append_assoc, List.singleton_append]

theorem emitCountdown_semantics (value record count : K) (hvr : value ≠ record)
    (hvc : value ≠ count) (hrc : record ≠ count) (copy : Bool)
    (base : K → List Bool) (frame : F) (guard : Bool) (xs ys zs : List Bool) :
    countdownEval value (emitBodyEval record count copy)
      (emitStore value record count base frame guard true xs ys zs) =
      emitStore value record count base frame false true []
        (List.replicate xs.length true ++ ys)
        (if copy then List.replicate xs.length true ++ zs else zs) := by
  have hv : (emitStore value record count base frame guard true xs ys zs).stk value = xs := by
    simp [emitStore, hvr, hvc]
  unfold countdownEval
  rw [hv, emitLoop_semantics value record count hvr hvc hrc, emitStore_reset]

def emitFrameCore (value record count : K) (copy : Bool) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (countdownRoutine value (emitBody record count copy))
    (Atom.routine (emitRecordOp record false))

def emitFrameRoutine (value record count : K) (copy : Bool) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd (emitFrameCore value record count copy)
    (Atom.routine countdownResetOp)

def emitFrameResult (value record count : K) (copy : Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ys zs : List Bool) : CountdownStore K F :=
  if flag then emitStore value record count base frame false true []
    (false :: (List.replicate xs.length true ++ ys))
    (if copy then List.replicate xs.length true ++ zs else zs)
  else emitStore value record count base frame false false xs ys zs

theorem emitFrame_executes (value record count : K) (hvr : value ≠ record)
    (hvc : value ≠ count) (hrc : record ≠ count) (copy : Bool)
    (base : K → List Bool) (frame : F) (guard flag : Bool) (xs ys zs : List Bool) :
    ∃ n ≤ 5 * xs.length + 5,
      (emitFrameRoutine value record count copy).Executes
        (emitStore value record count base frame guard flag xs ys zs)
        (emitFrameResult value record count copy base frame flag xs ys zs) n := by
  cases flag with
  | false =>
      refine ⟨2, by omega, ?_⟩
      exact RoutineControl.branch_false Prod.snd (emitFrameCore value record count copy)
        (Atom.routine countdownResetOp) rfl
        (Atom.executes countdownResetOp (emitStore value record count base frame guard false xs ys zs))
  | true =>
      obtain ⟨n, hn, hr, hi, hg, hc⟩ := countdownRoutine_executes value
        (emitBody record count copy) (emitBodyEval record count copy) (fun _ => True) 2
        (emitCountdownContract value record count hvr hvc copy)
        (emitStore value record count base frame guard true xs ys zs) trivial
      have hv : (emitStore value record count base frame guard true xs ys zs).stk value = xs := by
        simp [emitStore, hvr, hvc]
      rw [hv] at hn
      rw [emitCountdown_semantics value record count hvr hvc hrc] at hr
      have hd := Atom.executes (emitRecordOp record false)
        (emitStore value record count base frame false true []
          (List.replicate xs.length true ++ ys)
          (if copy then List.replicate xs.length true ++ zs else zs))
      rw [emitStore_delimiter value record count hrc] at hd
      have hcore := RoutineComposition.seq_executes
        (countdownRoutine value (emitBody record count copy))
        (Atom.routine (emitRecordOp record false)) hr hd
      have hfull := RoutineControl.branch_true Prod.snd (emitFrameCore value record count copy)
        (Atom.routine countdownResetOp) rfl hcore
      exact ⟨n + 2, by omega, hfull⟩

theorem reverse_unaryFrame_append (n : ℕ) (ys : List Bool) :
    (unaryFrame n).reverse ++ ys = false :: (List.replicate n true ++ ys) := by
  simp [unaryFrame, List.reverse_append, List.reverse_replicate]

/-- Only on the reader-produced tally true^a is this a serializer of the
    numeric value a. On an arbitrary word it serializes physical LENGTH. -/
theorem emitFrame_tally_output (value record count : K) (hrc : record ≠ count)
    (copy : Bool) (base : K → List Bool) (frame : F) (a : ℕ) (ys zs : List Bool) :
    (emitFrameResult value record count copy base frame true (List.replicate a true) ys zs).stk record =
      (unaryFrame a).reverse ++ ys := by
  simp [emitFrameResult, emitStore, hrc, reverse_unaryFrame_append]

/- This component INSTANTIATES a countdown body contract with actual push
atoms; it does not merely posit it. The emitted order is reversed-frame
prefix plus the old reversed record. Successful zero emits its delimiter.
Failure emits nothing, keeps data stacks unchanged and resets only the
owned guard; whole-parser failure cleanup is still required. A copied list
counter must initially be empty in the intended parser. Actual numeric-
reader/row-body embeddings, nested contracts, caps, suffix checks, full
constructor/checker and upstream hardness/kernel closure remain open.
-/

end PolytomyReductionModel
