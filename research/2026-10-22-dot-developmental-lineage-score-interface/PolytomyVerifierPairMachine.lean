/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution or kernel certificate.

Concrete total Boolean-TM2 adapter from the Lax434930 certificate convention
(0b blocks, then 1, then certificate) to our EXISTING unary-length framing.
The public convention is attributed to Edouard Bonnet and Codex 5.6 and 6,
classical-complexity commit 0c0840319318215fd7b36a9a822b81ce55cf6941,
Apache-2.0. The implementation/proofs below are dot's source proposal and
do not import that library or invoke its concept-side theorem axioms.
-/
import PolytomyBinaryFrameMachine
import Mathlib.Data.List.Induction

namespace PolytomyReductionModel

open Turing StateTransition

def blockPair : List Bool → List Bool → List Bool
  | [], cert => true :: cert
  | b :: xs, cert => false :: b :: blockPair xs cert

def readBlockPair : List Bool → Option (List Bool × List Bool)
  | [] => none
  | true :: cert => some ([], cert)
  | false :: [] => none
  | false :: b :: rest => (readBlockPair rest).map (fun p => (b :: p.1, p.2))

theorem readBlockPair_encode (xs cert : List Bool) :
    readBlockPair (blockPair xs cert) = some (xs, cert) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [blockPair, readBlockPair, ih]

def convertVerifierPair (bits : List Bool) : List Bool :=
  match readBlockPair bits with
  | none => []
  | some (xs, cert) => verifierPairBits xs cert

theorem convertVerifierPair_encode (xs cert : List Bool) :
    convertVerifierPair (blockPair xs cert) = verifierPairBits xs cert := by
  simp [convertVerifierPair, readBlockPair_encode]

inductive PairConversionLabel where
  | read | word | count | clear
  deriving DecidableEq, Fintype

abbrev PairConversionCfg :=
  TM2.Cfg (fun _ : FrameStack => Bool) PairConversionLabel FrameControl

def pairConversionCfg (l : Option PairConversionLabel) (v : FrameControl)
    (xs cs ps : List Bool) : PairConversionCfg := ⟨l, v, frameStacks xs cs ps⟩

def pairConversionHalt (xs : List Bool) : PairConversionCfg :=
  pairConversionCfg none (false, none) xs [] []

def pairConversionCode : PairConversionLabel →
    TM2.Stmt (fun _ : FrameStack => Bool) PairConversionLabel FrameControl
  | .read =>
      .pop .input (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2.getD false)
            (.goto (fun _ => .word))
            (.pop .input (fun _ h => (false, h))
              (.branch (fun v => v.2.isSome)
                (.push .payload (fun v => v.2.getD false)
                  (.push .count (fun _ => true) (.goto (fun _ => .read))))
                (.goto (fun _ => .clear)))))
          (.goto (fun _ => .clear)))
  | .word =>
      .pop .payload (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.push .input (fun v => v.2.getD false) (.goto (fun _ => .word)))
          (.push .input (fun _ => false) (.goto (fun _ => .count))))
  | .count =>
      .pop .count (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.push .input (fun _ => true) (.goto (fun _ => .count)))
          (.load (fun _ => (false, none)) .halt))
  | .clear =>
      .pop .count (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.goto (fun _ => .clear))
          (.pop .payload (fun _ h => (false, h))
            (.branch (fun v => v.2.isSome)
              (.goto (fun _ => .clear))
              (.load (fun _ => (false, none)) .halt))))

def pairConversionStep : PairConversionCfg → Option PairConversionCfg :=
  TM2.step pairConversionCode

def pairConversionPrepend {a b c : PairConversionCfg} {n : ℕ}
    (h : pairConversionStep a = some b)
    (run : EvalsToInTime pairConversionStep b (some c) n) :
    EvalsToInTime pairConversionStep a (some c) (n + 1) :=
  EvalsToInTime.trans pairConversionStep 1 n a b (some c) (evalsOneStep _ _ _ h) run

def pairConversionWeaken {a b : PairConversionCfg} {n m : ℕ}
    (run : EvalsToInTime pairConversionStep a (some b) n) (h : n ≤ m) :
    EvalsToInTime pairConversionStep a (some b) m :=
  { run with steps_le_m := run.steps_le_m.trans h }

theorem pairConversion_read_block (v : FrameControl) (b : Bool) (xs cs ps : List Bool) :
    pairConversionStep (pairConversionCfg (some .read) v (false :: b :: xs) cs ps) =
      some (pairConversionCfg (some .read) (false, some b) xs (true :: cs) (b :: ps)) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_input, frameStacks_update_count, frameStacks_update_payload, frameStacks]

theorem pairConversion_read_delimiter (v : FrameControl) (xs cs ps : List Bool) :
    pairConversionStep (pairConversionCfg (some .read) v (true :: xs) cs ps) =
      some (pairConversionCfg (some .word) (false, some true) xs cs ps) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_input, frameStacks]

theorem pairConversion_read_empty (v : FrameControl) (cs ps : List Bool) :
    pairConversionStep (pairConversionCfg (some .read) v [] cs ps) =
      some (pairConversionCfg (some .clear) (false, none) [] cs ps) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_input, frameStacks]

theorem pairConversion_read_short (v : FrameControl) (cs ps : List Bool) :
    pairConversionStep (pairConversionCfg (some .read) v [false] cs ps) =
      some (pairConversionCfg (some .clear) (false, none) [] cs ps) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_input, frameStacks]

theorem pairConversion_word_cons (v : FrameControl) (b : Bool) (xs cs ps : List Bool) :
    pairConversionStep (pairConversionCfg (some .word) v xs cs (b :: ps)) =
      some (pairConversionCfg (some .word) (false, some b) (b :: xs) cs ps) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_payload, frameStacks_update_input, frameStacks]

theorem pairConversion_word_done (v : FrameControl) (xs cs : List Bool) :
    pairConversionStep (pairConversionCfg (some .word) v xs cs []) =
      some (pairConversionCfg (some .count) (false, none) (false :: xs) cs []) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_payload, frameStacks_update_input, frameStacks]

theorem pairConversion_count_cons (v : FrameControl) (c : Bool) (xs cs : List Bool) :
    pairConversionStep (pairConversionCfg (some .count) v xs (c :: cs) []) =
      some (pairConversionCfg (some .count) (false, some c) (true :: xs) cs []) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks_update_input, frameStacks]

theorem pairConversion_count_done (v : FrameControl) (xs : List Bool) :
    pairConversionStep (pairConversionCfg (some .count) v xs [] []) =
      some (pairConversionHalt xs) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks, pairConversionHalt]

theorem pairConversion_clear_count (v : FrameControl) (c : Bool) (cs ps : List Bool) :
    pairConversionStep (pairConversionCfg (some .clear) v [] (c :: cs) ps) =
      some (pairConversionCfg (some .clear) (false, some c) [] cs ps) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks]

theorem pairConversion_clear_payload (v : FrameControl) (p : Bool) (ps : List Bool) :
    pairConversionStep (pairConversionCfg (some .clear) v [] [] (p :: ps)) =
      some (pairConversionCfg (some .clear) (false, some p) [] [] ps) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks_update_payload, frameStacks]

theorem pairConversion_clear_done (v : FrameControl) :
    pairConversionStep (pairConversionCfg (some .clear) v [] [] []) =
      some (pairConversionHalt []) := by
  simp [pairConversionStep, pairConversionCfg, pairConversionCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks_update_payload, frameStacks, pairConversionHalt]

def pairConversionClearRun (cs ps : List Bool) (v : FrameControl) :
    EvalsToInTime pairConversionStep (pairConversionCfg (some .clear) v [] cs ps)
      (some (pairConversionHalt [])) (cs.length + ps.length + 1) := by
  induction cs generalizing ps v with
  | nil =>
      induction ps generalizing v with
      | nil => exact evalsOneStep _ _ _ (pairConversion_clear_done v)
      | cons p ps ih =>
          simpa [List.length_cons, Nat.add_assoc] using
            pairConversionPrepend (pairConversion_clear_payload v p ps) (ih (false, some p))
  | cons c cs ih =>
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        pairConversionPrepend (pairConversion_clear_count v c cs ps) (ih ps (false, some c))

def pairConversionCountRun (n : ℕ) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime pairConversionStep
      (pairConversionCfg (some .count) v xs (List.replicate n true) [])
      (some (pairConversionHalt (List.replicate n true ++ xs))) (n + 1) := by
  induction n generalizing xs v with
  | zero => exact evalsOneStep _ _ _ (pairConversion_count_done v xs)
  | succ n ih =>
      have h := pairConversionPrepend
        (pairConversion_count_cons v true xs (List.replicate n true))
        (ih (true :: xs) (false, some true))
      have hout : List.replicate n true ++ true :: xs =
          List.replicate (n + 1) true ++ xs := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [hout] at h
      simpa only [List.replicate_succ] using h

def pairConversionWordRun (n : ℕ) (ps xs : List Bool) (v : FrameControl) :
    EvalsToInTime pairConversionStep
      (pairConversionCfg (some .word) v xs (List.replicate n true) ps)
      (some (pairConversionHalt (unaryFrame n ++ ps.reverse ++ xs)))
      (ps.length + n + 2) := by
  induction ps generalizing xs v with
  | nil =>
      have h := pairConversionPrepend (pairConversion_word_done v xs (List.replicate n true))
        (pairConversionCountRun n (false :: xs) (false, none))
      simpa [unaryFrame, List.append_assoc, Nat.add_assoc] using h
  | cons b ps ih =>
      have h := pairConversionPrepend (pairConversion_word_cons v b xs (List.replicate n true) ps)
        (ih (b :: xs) (false, some b))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

def pairConversionReadEnd (t : ℕ) (ps bits : List Bool) : List Bool :=
  match readBlockPair bits with
  | none => []
  | some (word, cert) => unaryFrame (t + word.length) ++ ps.reverse ++ word ++ cert

theorem pairConversionReadEnd_block (t : ℕ) (ps rest : List Bool) (b : Bool) :
    pairConversionReadEnd t ps (false :: b :: rest) =
      pairConversionReadEnd (t + 1) (b :: ps) rest := by
  unfold pairConversionReadEnd
  simp only [readBlockPair]
  cases h : readBlockPair rest with
  | none => rfl
  | some pair =>
      rcases pair with ⟨word, cert⟩
      simp [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

/-- Every input, including an incomplete two-bit block and missing delimiter.
    The number t is proof-side notation for a STACK length, not a register. -/
def pairConversionReadRun (t : ℕ) (ps bits : List Bool) (v : FrameControl) :
    EvalsToInTime pairConversionStep
      (pairConversionCfg (some .read) v bits (List.replicate t true) ps)
      (some (pairConversionHalt (pairConversionReadEnd t ps bits)))
      (2 * bits.length + t + ps.length + 4) := by
  induction bits using List.twoStepInduction generalizing t ps v with
  | nil =>
      have h := pairConversionPrepend (pairConversion_read_empty v (List.replicate t true) ps)
        (pairConversionClearRun (List.replicate t true) ps (false, none))
      exact pairConversionWeaken
        (by simpa [pairConversionReadEnd, readBlockPair] using h)
        (by simp only [List.length_replicate, List.length_nil]; omega)
  | singleton b =>
      cases b with
      | false =>
          have h := pairConversionPrepend (pairConversion_read_short v (List.replicate t true) ps)
            (pairConversionClearRun (List.replicate t true) ps (false, none))
          exact pairConversionWeaken
            (by simpa [pairConversionReadEnd, readBlockPair] using h)
            (by simp only [List.length_replicate, List.length_singleton]; omega)
      | true =>
          have h := pairConversionPrepend (pairConversion_read_delimiter v [] (List.replicate t true) ps)
            (pairConversionWordRun t ps [] (false, some true))
          exact pairConversionWeaken
            (by simpa [pairConversionReadEnd, readBlockPair] using h)
            (by simp only [List.length_singleton]; omega)
  | cons_cons b c rest ih _ihCons =>
      cases b with
      | true =>
          have h := pairConversionPrepend
            (pairConversion_read_delimiter v (c :: rest) (List.replicate t true) ps)
            (pairConversionWordRun t ps (c :: rest) (false, some true))
          exact pairConversionWeaken
            (by simpa [pairConversionReadEnd, readBlockPair] using h)
            (by simp only [List.length_cons]; omega)
      | false =>
          rw [pairConversionReadEnd_block]
          have h := pairConversionPrepend
            (pairConversion_read_block v c rest (List.replicate t true) ps)
            (by simpa [List.replicate_succ] using ih (t + 1) (c :: ps) (false, some c))
          exact pairConversionWeaken h (by simp only [List.length_cons]; omega)

theorem pairConversionReadEnd_initial (bits : List Bool) :
    pairConversionReadEnd 0 [] bits = convertVerifierPair bits := by
  unfold pairConversionReadEnd convertVerifierPair
  cases h : readBlockPair bits with
  | none => rfl
  | some pair => rcases pair with ⟨word, cert⟩; simp [verifierPairBits]

def pairConversionMachine : FinTM2 where
  K := FrameStack
  k₀ := .input
  k₁ := .input
  Γ _ := Bool
  Λ := PairConversionLabel
  main := .read
  σ := FrameControl
  initialState := (false, none)
  m := pairConversionCode

theorem pairConversion_init (bits : List Bool) :
    initList pairConversionMachine bits =
      pairConversionCfg (some .read) (false, none) bits [] [] := by
  change (⟨some .read, (false, none), _⟩ : PairConversionCfg) =
    ⟨some .read, (false, none), frameStacks bits [] []⟩
  congr 1
  funext k; cases k <;> simp [initList, pairConversionMachine, frameStacks]

theorem pairConversion_halt (bits : List Bool) :
    haltList pairConversionMachine bits = pairConversionHalt bits := by
  change (⟨none, (false, none), _⟩ : PairConversionCfg) =
    ⟨none, (false, none), frameStacks bits [] []⟩
  congr 1
  funext k; cases k <;> simp [haltList, pairConversionMachine, frameStacks]

/-- Supplied complete clean-output machine term for the PAIR ADAPTER only.
    It does not implement the independent target checker itself. -/
def verifierPairConversionPoly :
    TM2ComputableInPolyTime (fun xs : List Bool => xs)
      (fun xs : List Bool => xs) convertVerifierPair where
  tm := pairConversionMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 4
  outputsFun bits := by
    have h := pairConversionReadRun 0 [] bits (false, none)
    simpa [TM2OutputsInTime, pairConversion_init, pairConversion_halt,
      pairConversionReadEnd_initial, pairConversionStep, FinTM2.step,
      pairConversionMachine] using h

theorem convertedVerifier_pair (input cert : List Bool) :
    scanPairVerifier (convertVerifierPair (blockPair input cert)) =
      scanEncodedTarget input cert := by
  rw [convertVerifierPair_encode, scanPairVerifier_encode]

theorem convertedVerifier_malformed (bits : List Bool)
    (h : readBlockPair bits = none) :
    scanPairVerifier (convertVerifierPair bits) = false := by
  simp [convertVerifierPair, h, scanPairVerifier, readVerifierPair, readUnaryFrame]

/- All source is UNELABORATED. The complete original constructor/verifier,
upstream SAT-to-X3C/MSSC chain, compatible proof-network closure and kernel
verification remain open. This supplied adapter does not discharge them.
-/

end PolytomyReductionModel
