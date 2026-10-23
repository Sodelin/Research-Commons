/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual ORIGINAL pair split and input-derived physical caps. The target
and certificate have independent arbitrary Boolean contents. Their exact
combined length is used for the budget square, then the numeric source is
restored to the target and its own small sentinel cap is constructed.
This is part of the same whole restricted verifier, not a new encoding.
-/
import PolytomyVerifierHeaderController

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive PairCapPort where
  | target | certificate | temp | large | counter
  deriving DecidableEq, Fintype

abbrev PairCapPorts (K : Type) := PairCapPort ↪ K

@[simp] theorem pairCapPorts_eq (p : PairCapPorts K) (a b : PairCapPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

theorem readRawBinaryFrame_verifierPair (bits : List Bool) :
    readRawBinaryFrame bits = readVerifierPair bits := rfl

theorem numericCopySource_executes (dest temp : K) (hdt : dest ≠ temp)
    (base : K → List Bool) (frame : F) (guard flag : Bool) (xs ps cs ws os : List Bool)
    (ht : base temp = []) :
    (wordDuplicateRoutine (.inl .source : NumericStack K) (.inr temp) (.inr dest)).Executes
      (numericStore base (frame, guard) flag xs ps cs ws os)
      (numericStore (Function.update base dest (xs ++ base dest)) (frame, guard) flag xs ps cs ws os)
      (3 * xs.length + 3) := by
  let s := numericStore base (frame, guard) flag xs ps cs ws os
  have he := wordDuplicate_executes (.inl .source : NumericStack K) (.inr temp) (.inr dest)
    (by simp) (by simp) (by simpa using hdt.symm) s ht
  have hr : wordDuplicateEval (.inl .source) (.inr dest) s =
      numericStore (Function.update base dest (xs ++ base dest)) (frame, guard) flag xs ps cs ws os := by
    apply countdownStore_ext
    · rfl
    · funext j; cases j with
      | inl j => cases j <;> simp [wordDuplicateEval, s, numericStore, numericStacks]
      | inr j => simp [wordDuplicateEval, s, numericStore, numericStacks]
  rw [hr] at he
  exact he

theorem numericPrependExtra_executes (saved temp : K) (hst : saved ≠ temp)
    (base : K → List Bool) (frame : F) (guard flag : Bool) (xs ps cs ws os : List Bool)
    (ht : base temp = []) :
    (wordDuplicateRoutine (.inr saved : NumericStack K) (.inr temp) (.inl .source)).Executes
      (numericStore base (frame, guard) flag xs ps cs ws os)
      (numericStore base (frame, guard) flag (base saved ++ xs) ps cs ws os)
      (3 * (base saved).length + 3) := by
  let s := numericStore base (frame, guard) flag xs ps cs ws os
  have he := wordDuplicate_executes (.inr saved : NumericStack K) (.inr temp) (.inl .source)
    (by simpa using hst) (by simp) (by simp) s ht
  have hr : wordDuplicateEval (.inr saved) (.inl .source) s =
      numericStore base (frame, guard) flag (base saved ++ xs) ps cs ws os := by
    apply countdownStore_ext
    · rfl
    · funext j; cases j with
      | inl j => cases j <;> simp [wordDuplicateEval, s, numericStore, numericStacks]
      | inr j => simp [wordDuplicateEval, s, numericStore, numericStacks]
  rw [hr] at he
  exact he

theorem numericClearSource_executes (base : K → List Bool) (frame : F) (guard flag : Bool)
    (xs ps cs ws os : List Bool) :
    (clearStackRoutine (.inl .source : NumericStack K)).Executes
      (numericStore base (frame, guard) flag xs ps cs ws os)
      (numericStore base (frame, guard) flag [] ps cs ws os) (xs.length + 1) := by
  let s := numericStore base (frame, guard) flag xs ps cs ws os
  have he := clearStack_executes (.inl .source : NumericStack K) s
  have hr : clearStackEval (.inl .source) s = numericStore base (frame, guard) flag [] ps cs ws os := by
    apply countdownStore_ext
    · rfl
    · funext j; cases j with
      | inl j => cases j <;> simp [clearStackEval, s, numericStore, numericStacks]
      | inr j => simp [clearStackEval, s, numericStore, numericStacks]
  rw [hr] at he
  exact he

theorem numericClearCap_executes (base : K → List Bool) (frame : F) (guard flag : Bool)
    (xs ps cs ws os : List Bool) :
    (clearStackRoutine (.inl .cap : NumericStack K)).Executes
      (numericStore base (frame, guard) flag xs ps cs ws os)
      (numericStore base (frame, guard) flag xs ps [] ws os) (cs.length + 1) := by
  let s := numericStore base (frame, guard) flag xs ps cs ws os
  have he := clearStack_executes (.inl .cap : NumericStack K) s
  have hr : clearStackEval (.inl .cap) s = numericStore base (frame, guard) flag xs ps [] ws os := by
    apply countdownStore_ext
    · rfl
    · funext j; cases j with
      | inl j => cases j <;> simp [clearStackEval, s, numericStore, numericStacks]
      | inr j => simp [clearStackEval, s, numericStore, numericStacks]
  rw [hr] at he
  exact he

def pairCapsSuccessRoutine (p : PairCapPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (.inl .source) (.inr (p .temp)) (.inr (p .certificate)))
    (RoutineComposition.seq (clearStackRoutine (.inl .source))
      (RoutineComposition.seq (frameReverseRoutine (.inl .payload) (.inl .source))
        (RoutineComposition.seq (wordDuplicateRoutine (.inl .source) (.inr (p .temp)) (.inr (p .target)))
          (RoutineComposition.seq (wordDuplicateRoutine (.inr (p .certificate)) (.inr (p .temp)) (.inl .source))
            (RoutineComposition.seq smallCapRoutine
              (RoutineComposition.seq (capSquareRoutine (p .large) (p .counter))
                (RoutineComposition.seq (clearStackRoutine (.inl .source))
                  (RoutineComposition.seq (clearStackRoutine (.inl .cap))
                    (RoutineComposition.seq (wordDuplicateRoutine (.inr (p .target)) (.inr (p .temp)) (.inl .source))
                      smallCapRoutine)))))))))

def pairCapsBase (p : PairCapPorts K) (input cert : List Bool) (base : K → List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base (p .certificate) cert) (p .target) input)
    (p .large) (List.replicate (verifierBudgetCap input cert) true)

def pairCapsSuccessResult (p : PairCapPorts K) (input cert : List Bool)
    (base : K → List Bool) (frame : F) : CountdownStore (NumericStack K) F :=
  numericStore (pairCapsBase p input cert base) (frame, false) true input []
    (List.replicate (input.length + 1) true) [] []

def pairCapsSuccessBound (input cert : List Bool) : ℕ :=
  3 * (input.length + cert.length + 1) ^ 2 + 9 * (input.length + cert.length + 1) +
    13 * input.length + 11 * cert.length + 31

/-- Both saved words retain their original order. The temporary combined
source has certificate++target order solely to count its exact length;
it is never parsed as a target and is cleared before target restoration. -/
theorem pairCapsSuccess_executes (p : PairCapPorts K) (input cert : List Bool)
    (base : K → List Bool) (hfresh : ∀ j : PairCapPort, base (p j) = [])
    (frame : F) (guard : Bool) :
    ∃ n ≤ pairCapsSuccessBound input cert,
      (pairCapsSuccessRoutine p).Executes
        (numericStore base (frame, guard) true cert input.reverse [] [] [])
        (pairCapsSuccessResult p input cert base frame) n := by
  let b1 := Function.update base (p .certificate) cert
  let b2 := Function.update b1 (p .target) input
  let Q := cert.length + input.length + 1
  let b3 := Function.update b2 (p .large) (List.replicate (Q ^ 2) true)
  have hb1 (j : PairCapPort) (hj : j ≠ .certificate) : b1 (p j) = [] := by
    simp [b1, hj, hfresh]
  have hb2 (j : PairCapPort) (hjc : j ≠ .certificate) (hjt : j ≠ .target) : b2 (p j) = [] := by
    simp [b2, b1, hjc, hjt, hfresh]
  have hb3temp : b3 (p .temp) = [] := by simp [b3, b2, b1, hfresh]
  have hb2cert : b2 (p .certificate) = cert := by simp [b2, b1]
  have hb3target : b3 (p .target) = input := by simp [b3, b2]
  have h1 := numericCopySource_executes (p .certificate) (p .temp) (by simp)
    base frame guard true cert input.reverse [] [] [] (hfresh .temp)
  simp only [hfresh .certificate, List.append_nil] at h1
  have h2 := numericClearSource_executes b1 frame guard true cert input.reverse [] [] []
  let s2 := numericStore b1 (frame, guard) true [] input.reverse [] [] []
  have h3 := reverseMove_executes (.inl .payload : NumericStack K) (.inl .source) (by simp) s2
  have hr3 : reverseMoveEval (.inl .payload) (.inl .source) s2 =
      numericStore b1 (frame, guard) true input [] [] [] [] := by
    apply countdownStore_ext
    · rfl
    · funext j; cases j with
      | inl j => cases j <;> simp [reverseMoveEval, s2, numericStore, numericStacks]
      | inr j => simp [reverseMoveEval, s2, numericStore, numericStacks]
  rw [hr3] at h3
  have h4 := numericCopySource_executes (p .target) (p .temp) (by simp)
    b1 frame guard true input [] [] [] [] (hb1 .temp (by decide))
  simp only [hb1 .target (by decide), List.append_nil] at h4
  have h5 := numericPrependExtra_executes (p .certificate) (p .temp) (by simp)
    b2 frame guard true input [] [] [] [] (hb2 .temp (by decide) (by decide))
  rw [hb2cert] at h5
  have h6 := smallCap_executes (cert ++ input) b2 frame guard true [] []
  simp only [List.length_append] at h6
  obtain ⟨a, ha, h7⟩ := capSquare_executes (p .large) (p .counter) (by simp)
    Q (cert ++ input).length (cert ++ input) (le_refl _) b2
    (hb2 .large (by decide) (by decide)) (hb2 .counter (by decide) (by decide)) frame guard
  have h8 := numericClearSource_executes b3 frame false true (cert ++ input) [] (List.replicate Q true) [] []
  have h9 := numericClearCap_executes b3 frame false true [] [] (List.replicate Q true) [] []
  have h10 := numericPrependExtra_executes (p .target) (p .temp) (by simp)
    b3 frame false true [] [] [] [] [] hb3temp
  rw [hb3target, List.append_nil] at h10
  have h11 := smallCap_executes input b3 frame false true [] []
  have hcombined := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4
      (RoutineComposition.seq_executes _ _ h5 (RoutineComposition.seq_executes _ _ h6
        (RoutineComposition.seq_executes _ _ h7 (RoutineComposition.seq_executes _ _ h8
          (RoutineComposition.seq_executes _ _ h9 (RoutineComposition.seq_executes _ _ h10 h11)))))))))
  have hout : numericStore b3 (frame, false) true input [] (List.replicate (input.length + 1) true) [] [] =
      pairCapsSuccessResult p input cert base frame := by
    simp [pairCapsSuccessResult, pairCapsBase, b3, b2, b1, Q, verifierBudgetCap, Nat.add_comm]
  rw [hout] at hcombined
  refine ⟨_, ?_, hcombined⟩
  simp only [numericStore, numericStacks, s2, List.length_reverse, List.length_append,
    List.length_replicate] at *
  unfold pairCapsSuccessBound Q at *
  nlinarith

def pairCapsRoutine (p : PairCapPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine numericStartOp)
    (RoutineComposition.seq
      (frameCallerRoutine (.inl .source : NumericStack K) (.inl .payload) (by simp))
      (RoutineComposition.seq
        (RoutineControl.branch Prod.snd (pairCapsSuccessRoutine p) (Atom.routine cleanupNoop))
        (Atom.routine countdownResetOp)))

def pairCapsResult (p : PairCapPorts K) (bits : List Bool) (base : K → List Bool) (frame : F) :
    CountdownStore (NumericStack K) F :=
  match readVerifierPair bits with
  | none => numericStore base (frame, false) false [] [] [] [] []
  | some (input, cert) => pairCapsSuccessResult p input cert base frame

def pairCapsBound (L : ℕ) : ℕ := 3 * (L + 1) ^ 2 + 24 * L + 47

/-- ALL original pair words: malformed or too-large unary frame counts
reject with empty parser/cap work, without attempting cap production.
Success creates the EXACT small and budget caps from the parsed words.
The finite code is independent of their lengths and contents. -/
theorem pairCaps_executes (p : PairCapPorts K) (bits : List Bool)
    (base : K → List Bool) (hfresh : ∀ j : PairCapPort, base (p j) = [])
    (frame : F) (guard flag : Bool) :
    ∃ n ≤ pairCapsBound bits.length,
      (pairCapsRoutine p).Executes
        (numericStore base (frame, guard) flag bits [] [] [] [])
        (pairCapsResult p bits base frame) n := by
  let s := numericStore base (frame, guard) flag bits [] [] [] []
  let u := numericStore base (frame, guard) false bits [] [] [] []
  have h1 : (Atom.routine (numericStartOp (K := K) (F := F))).Executes s u 1 := Atom.executes numericStartOp s
  obtain ⟨a, ha, h2⟩ := frameCaller_executes (.inl .source : NumericStack K) (.inl .payload)
    (by simp) (numericStacks base [] [] [] [] []) (frame, guard) bits
  rw [numericFrame_store, numericFrame_raw_result, readRawBinaryFrame_verifierPair] at h2
  cases hp : readVerifierPair bits with
  | none =>
      let v := numericStore base (frame, guard) false [] [] [] [] []
      change (frameCallerRoutine (.inl .source : NumericStack K) (.inl .payload) _).Executes u
        (numericRawResult base (frame, guard) [] (readVerifierPair bits)) a at h2
      simp only [hp, numericRawResult] at h2
      have h3 := RoutineControl.branch_false Prod.snd (pairCapsSuccessRoutine p)
        (Atom.routine cleanupNoop) (show v.state.2 = false from rfl) (Atom.executes cleanupNoop v)
      have h4 := Atom.executes (countdownResetOp (K := NumericStack K) (F := F)) v
      refine ⟨1 + (a + (2 + 1)), by unfold pairCapsBound; nlinarith, ?_⟩
      simpa [pairCapsRoutine, pairCapsResult, hp, v, u, s, cleanupNoop,
        countdownResetOp, Op.apply, numericStore] using
        RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
          (RoutineComposition.seq_executes _ _ h3 h4))
  | some q =>
      rcases q with ⟨input, cert⟩
      let v := numericStore base (frame, guard) true cert input.reverse [] [] []
      simp only [hp, numericRawResult] at h2
      obtain ⟨b, hb, h3⟩ := pairCapsSuccess_executes p input cert base hfresh frame guard
      have h4 := RoutineControl.branch_true Prod.snd (pairCapsSuccessRoutine p)
        (Atom.routine cleanupNoop) (show v.state.2 = true from rfl) h3
      have h5 := Atom.executes (countdownResetOp (K := NumericStack K) (F := F))
        (pairCapsSuccessResult p input cert base frame)
      have hlen := readVerifierPair_payload_length bits input cert hp
      have hQ : (input.length + cert.length + 1) ^ 2 ≤ (bits.length + 1) ^ 2 := by nlinarith
      refine ⟨1 + (a + ((b + 1) + 1)), ?_, ?_⟩
      · unfold pairCapsBound pairCapsSuccessBound at *
        nlinarith
      · simpa [pairCapsRoutine, pairCapsResult, hp, pairCapsSuccessResult,
          countdownResetOp, Op.apply, numericStore] using
          RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
            (RoutineComposition.seq_executes _ _ h4 h5))

theorem pairCaps_success_data (p : PairCapPorts K) (bits input cert : List Bool)
    (base : K → List Bool) (frame : F) (hp : readVerifierPair bits = some (input, cert)) :
    (pairCapsResult p bits base frame).state = ((frame, false), true) ∧
      (pairCapsResult p bits base frame).stk (.inl .source) = input ∧
      (pairCapsResult p bits base frame).stk (.inl .cap) = List.replicate (input.length + 1) true ∧
      (pairCapsResult p bits base frame).stk (.inr (p .large)) =
        List.replicate (verifierBudgetCap input cert) true ∧
      (pairCapsResult p bits base frame).stk (.inr (p .target)) = input ∧
      (pairCapsResult p bits base frame).stk (.inr (p .certificate)) = cert := by
  simp [pairCapsResult, hp, pairCapsSuccessResult, pairCapsBase, numericStore, numericStacks]

/- The original pair parser and both success/failure branches now have a
composed source proposal. Exact physical caps are constructed, not entry
promises. The next join identifies these ports with the header inventory,
then continues through the saved original grammar/guard/score routines.
No whole-verifier, kernel or hardness closure is claimed. -/

end PolytomyReductionModel.WholeVerifierController
