/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual finite source-length tally preserving EVERY original input bit.
The source is moved with a faithful bit copy to payload scratch, reversed
back, and one tally bit is added. This constructs L+1, not an assumed cap.
-/
import PolytomyOriginalPrefixObservation

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def lengthCapStacks (base : K → List Bool) (xs ps cs ws os : List Bool) :
    ∀ j : NumericStack K ⊕ Empty,
      List ((Sum.elim (fun _ : NumericStack K => Bool) (fun _ : Empty => Bool)) j)
  | .inl k => numericStacks base xs ps cs ws os k
  | .inr e => nomatch e

theorem lengthCapStacks_source (base : K → List Bool) (xs ps cs ws os zs : List Bool) :
    Function.update (lengthCapStacks base xs ps cs ws os) (.inl (.inl .source)) zs =
      lengthCapStacks base zs ps cs ws os := by
  funext j
  cases j with
  | inr e => nomatch e
  | inl k => cases k with
    | inl p => cases p <;> simp [lengthCapStacks, numericStacks]
    | inr k => simp [lengthCapStacks, numericStacks]

theorem lengthCapStacks_payload (base : K → List Bool) (xs ps cs ws os zs : List Bool) :
    Function.update (lengthCapStacks base xs ps cs ws os) (.inl (.inl .payload)) zs =
      lengthCapStacks base xs zs cs ws os := by
  funext j
  cases j with
  | inr e => nomatch e
  | inl k => cases k with
    | inl p => cases p <;> simp [lengthCapStacks, numericStacks]
    | inr k => simp [lengthCapStacks, numericStacks]

theorem lengthCapStacks_cap (base : K → List Bool) (xs ps cs ws os zs : List Bool) :
    Function.update (lengthCapStacks base xs ps cs ws os) (.inl (.inl .cap)) zs =
      lengthCapStacks base xs ps zs ws os := by
  funext j
  cases j with
  | inr e => nomatch e
  | inl k => cases k with
    | inl p => cases p <;> simp [lengthCapStacks, numericStacks]
    | inr k => simp [lengthCapStacks, numericStacks]

def inputLengthCopyRoutine : Routine (fun _ : NumericStack K => Bool) (F × Bool) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Unit
  entry := ()
  code _ := .pop (.inl (.inl .source)) (fun v h => (v.1, h))
    (.branch (fun v => v.2.isSome)
      (.push (.inl (.inl .payload)) (fun v => v.2.getD false)
        (.push (.inl (.inl .cap)) (fun _ => true) (.goto (fun _ => ()))))
      (.load (fun v => (v.1, none)) .halt))

def lengthCapCfg (l : Option Unit) (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ps cs ws os : List Bool) :
    TM2.Cfg (Sum.elim (fun _ : NumericStack K => Bool) (fun _ : Empty => Bool))
      Unit ((F × Bool) × Option Bool) :=
  ⟨l, ((frame, flag), o), lengthCapStacks base xs ps cs ws os⟩

theorem lengthCap_boundary (l : Option Unit) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ps cs ws os : List Bool) :
    lengthCapCfg l none base frame flag xs ps cs ws os =
      (inputLengthCopyRoutine (K := K) (F := F)).boundary l
        (numericStore base frame flag xs ps cs ws os) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext j; cases j with
    | inl k => rfl
    | inr e => nomatch e

theorem lengthCap_nil (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (ps cs ws os : List Bool) :
    TM2.step (inputLengthCopyRoutine (K := K) (F := F)).code
      (lengthCapCfg (some ()) o base frame flag [] ps cs ws os) =
      some (lengthCapCfg none none base frame flag [] ps cs ws os) := by
  simp [inputLengthCopyRoutine, lengthCapCfg, TM2.step, TM2.stepAux,
    lengthCapStacks_source, lengthCapStacks, numericStacks]

theorem lengthCap_cons (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag b : Bool) (xs ps cs ws os : List Bool) :
    TM2.step (inputLengthCopyRoutine (K := K) (F := F)).code
      (lengthCapCfg (some ()) o base frame flag (b :: xs) ps cs ws os) =
      some (lengthCapCfg (some ()) (some b) base frame flag xs (b :: ps) (true :: cs) ws os) := by
  simp [inputLengthCopyRoutine, lengthCapCfg, TM2.step, TM2.stepAux,
    lengthCapStacks_source, lengthCapStacks_payload, lengthCapStacks_cap, lengthCapStacks, numericStacks]

theorem lengthCapRun (xs : List Bool) (w : ℕ) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (ps ws os : List Bool) :
    Runs (TM2.step (inputLengthCopyRoutine (K := K) (F := F)).code)
      (lengthCapCfg (some ()) o base frame flag xs ps (List.replicate w true) ws os)
      (lengthCapCfg none none base frame flag [] (xs.reverse ++ ps)
        (List.replicate (w + xs.length) true) ws os) (xs.length + 1) := by
  induction xs generalizing w o ps with
  | nil => simpa using Runs.one (lengthCap_nil o base frame flag ps (List.replicate w true) ws os)
  | cons b xs ih =>
      have r := Runs.cons
        (lengthCap_cons o base frame flag b xs ps (List.replicate w true) ws os)
        (by simpa only [List.replicate_succ] using ih (w + 1) (some b) (b :: ps))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem inputLengthCopy_executes (xs : List Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (ws os : List Bool) :
    (inputLengthCopyRoutine (K := K) (F := F)).Executes
      (numericStore base frame flag xs [] [] ws os)
      (numericStore base frame flag [] xs.reverse (List.replicate xs.length true) ws os)
      (xs.length + 1) := by
  have r := lengthCapRun xs 0 none base frame flag [] ws os
  simp only [List.replicate_zero, Nat.zero_add, List.append_nil] at r
  rw [lengthCap_boundary, lengthCap_boundary] at r
  exact r.iterate

def smallCapPushOp : Op (NumericStack K) Bool (CountdownState F) :=
  .push (.inl .cap) (fun _ => true)

def smallCapRoutine : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (inputLengthCopyRoutine (F := F × Bool))
    (RoutineComposition.seq (frameReverseRoutine (.inl .payload) (.inl .source))
      (Atom.routine smallCapPushOp))

theorem smallCap_executes (bits : List Bool) (base : K → List Bool)
    (frame : F) (guard flag : Bool) (ws os : List Bool) :
    (smallCapRoutine (K := K) (F := F)).Executes
      (numericStore base (frame, guard) flag bits [] [] ws os)
      (numericStore base (frame, guard) flag bits [] (List.replicate (bits.length + 1) true) ws os)
      (2 * bits.length + 3) := by
  let u := numericStore base (frame, guard) flag [] bits.reverse (List.replicate bits.length true) ws os
  let v := numericStore base (frame, guard) flag bits [] (List.replicate bits.length true) ws os
  have h1 := inputLengthCopy_executes bits base (frame, guard) flag ws os
  have h2 := reverseMove_executes (.inl .payload : NumericStack K) (.inl .source) (by simp) u
  have hu : reverseMoveEval (.inl .payload) (.inl .source) u = v := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> simp [u, v, reverseMoveEval, numericStore, numericStacks]
      | inr k => rfl
  rw [hu] at h2
  have h3 := Atom.executes (smallCapPushOp (K := K) (F := F)) v
  have hv : smallCapPushOp.apply v =
      numericStore base (frame, guard) flag bits [] (List.replicate (bits.length + 1) true) ws os := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> simp [smallCapPushOp, Op.apply, v, numericStore, numericStacks, List.replicate_succ]
      | inr k => rfl
  rw [hv] at h3
  have h23 := RoutineComposition.seq_executes (frameReverseRoutine (.inl .payload) (.inl .source))
    (Atom.routine smallCapPushOp) h2 h3
  have hall := RoutineComposition.seq_executes (inputLengthCopyRoutine (F := F × Bool))
    (RoutineComposition.seq (frameReverseRoutine (.inl .payload) (.inl .source))
      (Atom.routine smallCapPushOp)) h1 h23
  convert hall using 1 <;> simp [smallCapRoutine, u, numericStore, numericStacks, Nat.two_mul, Nat.add_assoc]

/- Every input bit is restored, including false bits. Using a unary-only
copier on arbitrary source bits would be wrong. Payload/cap start empty;
payload returns empty, cap becomes true^(L+1), all other data and the
entire public state are unchanged. Large-cap squaring and complete-parser
finish/cleanup, downstream constructor/checker/hardness/kernel remain.
-/

end PolytomyReductionModel
