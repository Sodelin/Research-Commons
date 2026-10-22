/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original comb-node prefix: consume an accepted-leaf count q and
prepend q-1 false bits to the already emitted leaf sequence. No success
flag guard is used for this unconditional finishing routine. The caller
state and every outside stack are preserved, including the cost tape.
-/
import PolytomyAcceptedCanonicalLeaf

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def paintMoveRoutine (source output : K) (bit : Bool) :
    Routine (fun _ : K => Bool) (CountdownState F) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Unit
  entry := ()
  code _ := Transfer.stmt (Equiv.refl (CountdownState F × Option Bool))
    (.inl source) (.inl output) id (fun _ => bit) () none

def paintMoveEval (source output : K) (bit : Bool) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update (Function.update s.stk source []) output
    (List.replicate (s.stk source).length bit ++ s.stk output)⟩

theorem paintMap_eq_replicate (xs : List Bool) (bit : Bool) :
    xs.map (fun _ => bit) = List.replicate xs.length bit := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih, List.replicate_succ]

theorem paintMove_boundary (source output : K) (bit : Bool) (base : K → List Bool)
    (state : CountdownState F) (l : Option Unit) (xs ys : List Bool) :
    Transfer.cfg (Equiv.refl (CountdownState F × Option Bool))
      (Sum.inl source) (Sum.inl output) (frameReverseBase base) l state none xs ys =
    (paintMoveRoutine source output bit).boundary l
      (frameCallerStore source output base state.1 state.2 xs ys) := by
  exact frameReverse_boundary source output base state.1 state.2 l xs ys

theorem paintMove_executes (source output : K) (hne : source ≠ output) (bit : Bool)
    (s : CountdownStore K F) :
    (paintMoveRoutine source output bit).Executes s (paintMoveEval source output bit s)
      ((s.stk source).length + 1) := by
  have hn : (Sum.inl source : K ⊕ Empty) ≠ Sum.inl output := fun h => hne (Sum.inl.inj h)
  have h := Transfer.runs (Equiv.refl (CountdownState F × Option Bool))
    (.inl source) (.inl output) hn id (fun _ => bit) () none
    (paintMoveRoutine (F := F) source output bit).code (by rfl)
    (frameReverseBase s.stk) s.state none (s.stk source) (s.stk output)
  change Runs (TM2.step (paintMoveRoutine source output bit).code)
    (Transfer.cfg (Equiv.refl (CountdownState F × Option Bool))
      (.inl source) (.inl output) (frameReverseBase s.stk)
      (some ()) s.state none (s.stk source) (s.stk output))
    (Transfer.cfg (Equiv.refl (CountdownState F × Option Bool))
      (.inl source) (.inl output) (frameReverseBase s.stk)
      none s.state none [] (((s.stk source).map (fun _ => bit)).reverse ++ s.stk output))
    ((s.stk source).length + 1) at h
  rw [paintMap_eq_replicate, List.reverse_replicate,
    paintMove_boundary source output bit, paintMove_boundary source output bit,
    frameCallerStore_self] at h
  exact h.iterate

def canonicalCombPrefixRoutine (count output : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (countdownPopOp count)) (paintMoveRoutine count output false)

def canonicalCombPrefixEval (count output : K) (s : CountdownStore K F) : CountdownStore K F :=
  paintMoveEval count output false (countdownPop count s)

theorem canonicalCombPrefix_executes (count output : K) (hne : count ≠ output)
    (s : CountdownStore K F) :
    (canonicalCombPrefixRoutine count output).Executes s (canonicalCombPrefixEval count output s)
      ((s.stk count).length - 1 + 2) := by
  have h := RoutineComposition.seq_executes (Atom.routine (countdownPopOp count))
    (paintMoveRoutine count output false) (Atom.executes (countdownPopOp count) s)
    (paintMove_executes count output hne false (countdownPop count s))
  rw [countdownPop_counter] at h
  cases hc : s.stk count with
  | nil => simpa [canonicalCombPrefixRoutine, canonicalCombPrefixEval, hc] using h
  | cons b xs => simpa [canonicalCombPrefixRoutine, canonicalCombPrefixEval, hc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem canonicalCombPrefix_bytes (count output : K) (hne : count ≠ output) (s : CountdownStore K F) :
    (canonicalCombPrefixEval count output s).stk output =
      List.replicate ((s.stk count).length - 1) false ++ s.stk output := by
  simp [canonicalCombPrefixEval, paintMoveEval, countdownPop, countdownPopOp, Op.apply,
    Ne.symm hne, List.length_tail]

theorem canonicalCombPrefix_count (count output : K) (hne : count ≠ output) (s : CountdownStore K F) :
    (canonicalCombPrefixEval count output s).stk count = [] := by
  simp [canonicalCombPrefixEval, paintMoveEval, hne]

theorem canonicalCombPrefix_state (count output : K) (s : CountdownStore K F) :
    (canonicalCombPrefixEval count output s).state = s.state := rfl

theorem canonicalCombPrefix_extra (count output k : K) (hkc : k ≠ count) (hko : k ≠ output)
    (s : CountdownStore K F) : (canonicalCombPrefixEval count output s).stk k = s.stk k := by
  simp [canonicalCombPrefixEval, paintMoveEval, countdownPop, countdownPopOp, Op.apply, hkc, hko]

/- This proves the ORIGINAL q-1 comb prefix, including q=0/1 as a total
operation. Admissible reduction blocks have at least two marker leaves,
but this routine does not assume that fact. It does not implement the
descending membership/enumeration controller, global block order, binary
headers or independent target verifier. Those whole-claim obligations
remain open, together with all elaboration and kernel checks.
-/

end PolytomyReductionModel
