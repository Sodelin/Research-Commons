/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution, kernel check or certificate.

An actual finite TM2 transducer for the EXISTING binary-frame grammar.
The variable unary width is stored on a Boolean stack, not in unbounded
control. Successful output retains the raw payload (reversed) and suffix;
failure clears all stacks. This is a parser component, not the complete
constructor/verifier or a new machine-cost model. No external dependency.
-/
import PolytomyConstantBranchMachine

namespace PolytomyReductionModel

open Turing StateTransition

inductive FrameStack where
  | input | count | payload
  deriving DecidableEq, Fintype

inductive FrameLabel where
  | prefix | payload | clear
  deriving DecidableEq, Fintype

abbrev FrameControl := Bool × Option Bool
abbrev FrameCfg := TM2.Cfg (fun _ : FrameStack => Bool) FrameLabel FrameControl

def frameStacks (input count payload : List Bool) : FrameStack → List Bool
  | .input => input
  | .count => count
  | .payload => payload

theorem frameStacks_update_input (xs cs ps ys : List Bool) :
    Function.update (frameStacks xs cs ps) .input ys = frameStacks ys cs ps := by
  funext k; cases k <;> simp [frameStacks]

theorem frameStacks_update_count (xs cs ps ds : List Bool) :
    Function.update (frameStacks xs cs ps) .count ds = frameStacks xs ds ps := by
  funext k; cases k <;> simp [frameStacks]

theorem frameStacks_update_payload (xs cs ps qs : List Bool) :
    Function.update (frameStacks xs cs ps) .payload qs = frameStacks xs cs qs := by
  funext k; cases k <;> simp [frameStacks]

def frameCfg (l : Option FrameLabel) (v : FrameControl)
    (xs cs ps : List Bool) : FrameCfg := ⟨l, v, frameStacks xs cs ps⟩

def frameFailure : FrameCfg := frameCfg none (false, none) [] [] []
def frameSuccess (rest reversedPayload : List Bool) : FrameCfg :=
  frameCfg none (true, none) rest [] reversedPayload

/-- Three fixed instruction trees, with no input-dependent code generation.
    A counter pop and a payload pop can share one TM2 statement; this is the
    pinned operational model, with a uniform constant primitive overhead. -/
def frameCode : FrameLabel → TM2.Stmt (fun _ : FrameStack => Bool)
    FrameLabel FrameControl
  | .prefix =>
      .pop .input (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2.getD false)
            (.push .count (fun _ => true) (.goto (fun _ => .prefix)))
            (.goto (fun _ => .payload)))
          (.goto (fun _ => .clear)))
  | .payload =>
      .pop .count (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.pop .input (fun _ h => (false, h))
            (.branch (fun v => v.2.isSome)
              (.push .payload (fun v => v.2.getD false)
                (.goto (fun _ => .payload)))
              (.goto (fun _ => .clear))))
          (.load (fun _ => (true, none)) .halt))
  | .clear =>
      .pop .count (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.goto (fun _ => .clear))
          (.pop .payload (fun _ h => (false, h))
            (.branch (fun v => v.2.isSome)
              (.goto (fun _ => .clear))
              (.load (fun _ => (false, none)) .halt))))

def frameStep : FrameCfg → Option FrameCfg := TM2.step frameCode

theorem frame_prefix_true (v : FrameControl) (xs cs ps : List Bool) :
    frameStep (frameCfg (some .prefix) v (true :: xs) cs ps) =
      some (frameCfg (some .prefix) (false, some true) xs (true :: cs) ps) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux, frameStacks,
    frameStacks_update_input, frameStacks_update_count]

theorem frame_prefix_false (v : FrameControl) (xs cs ps : List Bool) :
    frameStep (frameCfg (some .prefix) v (false :: xs) cs ps) =
      some (frameCfg (some .payload) (false, some false) xs cs ps) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_input, frameStacks]

theorem frame_prefix_nil (v : FrameControl) (cs ps : List Bool) :
    frameStep (frameCfg (some .prefix) v [] cs ps) =
      some (frameCfg (some .clear) (false, none) [] cs ps) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_input, frameStacks]

theorem frame_payload_done (v : FrameControl) (xs ps : List Bool) :
    frameStep (frameCfg (some .payload) v xs [] ps) =
      some (frameSuccess xs ps) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks, frameSuccess]

theorem frame_payload_cons (v : FrameControl) (b c : Bool) (xs cs ps : List Bool) :
    frameStep (frameCfg (some .payload) v (b :: xs) (c :: cs) ps) =
      some (frameCfg (some .payload) (false, some b) xs cs (b :: ps)) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks_update_input,
    frameStacks_update_payload, frameStacks]

theorem frame_payload_short (v : FrameControl) (c : Bool) (cs ps : List Bool) :
    frameStep (frameCfg (some .payload) v [] (c :: cs) ps) =
      some (frameCfg (some .clear) (false, none) [] cs ps) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks_update_input, frameStacks]

theorem frame_clear_count (v : FrameControl) (c : Bool) (cs ps : List Bool) :
    frameStep (frameCfg (some .clear) v [] (c :: cs) ps) =
      some (frameCfg (some .clear) (false, some c) [] cs ps) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks]

theorem frame_clear_payload (v : FrameControl) (p : Bool) (ps : List Bool) :
    frameStep (frameCfg (some .clear) v [] [] (p :: ps)) =
      some (frameCfg (some .clear) (false, some p) [] [] ps) := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks_update_payload, frameStacks]

theorem frame_clear_done (v : FrameControl) :
    frameStep (frameCfg (some .clear) v [] [] []) = some frameFailure := by
  simp [frameStep, frameCfg, frameCode, TM2.step, TM2.stepAux,
    frameStacks_update_count, frameStacks_update_payload, frameStacks, frameFailure]

def framePrepend {a b c : FrameCfg} {n : ℕ} (h : frameStep a = some b)
    (run : EvalsToInTime frameStep b (some c) n) :
    EvalsToInTime frameStep a (some c) (n + 1) :=
  EvalsToInTime.trans frameStep 1 n a b (some c) (evalsOneStep _ _ _ h) run

def frameWeaken {a b : FrameCfg} {n m : ℕ}
    (run : EvalsToInTime frameStep a (some b) n) (h : n ≤ m) :
    EvalsToInTime frameStep a (some b) m :=
  { run with steps_le_m := run.steps_le_m.trans h }

/-- Cleanup covers both malformed cases: at cleanup entry the input is
    exhausted, but a width tally or partially collected payload may remain. -/
def frameClearRun (cs ps : List Bool) (v : FrameControl) :
    EvalsToInTime frameStep (frameCfg (some .clear) v [] cs ps)
      (some frameFailure) (cs.length + ps.length + 1) := by
  induction cs generalizing ps v with
  | nil =>
      induction ps generalizing v with
      | nil => exact evalsOneStep _ _ _ (frame_clear_done v)
      | cons p ps ih =>
          simpa [List.length_cons, Nat.add_assoc] using
            framePrepend (frame_clear_payload v p ps) (ih (false, some p))
  | cons c cs ih =>
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        framePrepend (frame_clear_count v c cs ps) (ih ps (false, some c))

def framePayloadEnd (n : ℕ) (xs ps : List Bool) : FrameCfg :=
  if n ≤ xs.length then frameSuccess (xs.drop n) ((xs.take n).reverse ++ ps)
  else frameFailure

theorem framePayloadEnd_zero (xs ps : List Bool) :
    framePayloadEnd 0 xs ps = frameSuccess xs ps := by
  simp [framePayloadEnd]

theorem framePayloadEnd_short (n : ℕ) (ps : List Bool) :
    framePayloadEnd (n + 1) [] ps = frameFailure := by
  simp [framePayloadEnd]

theorem framePayloadEnd_cons (n : ℕ) (b : Bool) (xs ps : List Bool) :
    framePayloadEnd (n + 1) (b :: xs) ps = framePayloadEnd n xs (b :: ps) := by
  simp [framePayloadEnd, List.reverse_cons, List.append_assoc]

/-- The payload loop is valid for EVERY raw bit list, including a truncated
    payload. It never evaluates the binary numeric value or enumerates it. -/
def framePayloadRun (n : ℕ) (xs ps : List Bool) (v : FrameControl) :
    EvalsToInTime frameStep
      (frameCfg (some .payload) v xs (List.replicate n true) ps)
      (some (framePayloadEnd n xs ps)) (n + xs.length + ps.length + 3) := by
  induction n generalizing xs ps v with
  | zero =>
      rw [framePayloadEnd_zero]
      exact frameWeaken (evalsOneStep _ _ _ (frame_payload_done v xs ps)) (by omega)
  | succ n ih =>
      cases xs with
      | nil =>
          rw [framePayloadEnd_short]
          have h := framePrepend (frame_payload_short v true (List.replicate n true) ps)
            (frameClearRun (List.replicate n true) ps (false, none))
          exact frameWeaken (by simpa [List.replicate_succ] using h)
            (by simp only [List.length_replicate, List.length_nil]; omega)
      | cons b xs =>
          rw [framePayloadEnd_cons]
          have h := framePrepend (frame_payload_cons v b true xs (List.replicate n true) ps)
            (ih xs (b :: ps) (false, some b))
          simpa [List.replicate_succ, List.length_cons, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h

def framePrefixEnd (t : ℕ) (bits : List Bool) : FrameCfg :=
  match readUnaryFrame bits with
  | none => frameFailure
  | some (n, rest) => framePayloadEnd (t + n) rest []

theorem framePrefixEnd_true (t : ℕ) (rest : List Bool) :
    framePrefixEnd t (true :: rest) = framePrefixEnd (t + 1) rest := by
  unfold framePrefixEnd
  simp only [readUnaryFrame]
  cases h : readUnaryFrame rest with
  | none => rfl
  | some result =>
      rcases result with ⟨n, after⟩
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Uniform bound from arbitrary partially accumulated unary width. The
    finite control contains only six possible values, independent of t. -/
def framePrefixRun (t : ℕ) (bits : List Bool) (v : FrameControl) :
    EvalsToInTime frameStep
      (frameCfg (some .prefix) v bits (List.replicate t true) [])
      (some (framePrefixEnd t bits)) (2 * bits.length + t + 4) := by
  induction bits generalizing t v with
  | nil =>
      have h := framePrepend (frame_prefix_nil v (List.replicate t true) [])
        (frameClearRun (List.replicate t true) [] (false, none))
      exact frameWeaken (by simpa [framePrefixEnd, readUnaryFrame] using h)
        (by simp only [List.length_replicate, List.length_nil]; omega)
  | cons b rest ih =>
      cases b with
      | false =>
          have h := framePrepend (frame_prefix_false v rest (List.replicate t true) [])
            (framePayloadRun t rest [] (false, some false))
          exact frameWeaken (by simpa [framePrefixEnd, readUnaryFrame] using h)
            (by simp only [List.length_nil, List.length_cons]; omega)
      | true =>
          rw [framePrefixEnd_true]
          have h := framePrepend (frame_prefix_true v rest (List.replicate t true) [])
            (by simpa [List.replicate_succ] using ih (t + 1) (false, some true))
          exact frameWeaken h (by simp only [List.length_cons]; omega)

/-- Raw payloads retain high zero bits: this parser accepts exactly the
    existing grammar, rather than silently canonicalizing its input. -/
def readRawBinaryFrame (bits : List Bool) : Option (List Bool × List Bool) :=
  match readUnaryFrame bits with
  | none => none
  | some (n, rest) =>
      if n ≤ rest.length then some (rest.take n, rest.drop n) else none

def rawFrameOutput : Option (List Bool × List Bool) → FrameCfg
  | none => frameFailure
  | some (payload, rest) => frameSuccess rest payload.reverse

theorem framePrefixEnd_zero (bits : List Bool) :
    framePrefixEnd 0 bits = rawFrameOutput (readRawBinaryFrame bits) := by
  unfold framePrefixEnd readRawBinaryFrame
  cases h : readUnaryFrame bits with
  | none => rfl
  | some result =>
      rcases result with ⟨n, rest⟩
      simp [framePayloadEnd, rawFrameOutput]

/-- This is the operational whole-frame claim, not merely encode/decode
    inversion: it covers every Boolean input and exact malformed cleanup. -/
def binaryFrameTransducerRun (bits : List Bool) :
    EvalsToInTime frameStep (frameCfg (some .prefix) (false, none) bits [] [])
      (some (rawFrameOutput (readRawBinaryFrame bits))) (2 * bits.length + 4) := by
  simpa [framePrefixEnd_zero] using framePrefixRun 0 bits (false, none)

/-- Exact adapter to the EXISTING numeric parser. No assertion that a
    parsed numeric value is bounded by input length is introduced. -/
theorem readBinaryNatFrame_as_raw (bits : List Bool) :
    readBinaryNatFrame bits =
      (readRawBinaryFrame bits).map (fun p => (fromBinaryBits p.1, p.2)) := by
  unfold readBinaryNatFrame readRawBinaryFrame
  cases h : readUnaryFrame bits with
  | none => rfl
  | some result =>
      rcases result with ⟨n, rest⟩
      by_cases hn : n ≤ rest.length <;> simp [hn]

/-- The verifier's pair framing is the VERY SAME splitting grammar. -/
theorem readRawBinaryFrame_eq_readVerifierPair (bits : List Bool) :
    readRawBinaryFrame bits = readVerifierPair bits := rfl

def observeFrameOutput (cfg : FrameCfg) : Option (List Bool × List Bool) :=
  if cfg.var.1 then some ((cfg.stk .payload).reverse, cfg.stk .input) else none

theorem observe_rawFrameOutput (result : Option (List Bool × List Bool)) :
    observeFrameOutput (rawFrameOutput result) = result := by
  cases result with
  | none => rfl
  | some pair =>
      rcases pair with ⟨payload, rest⟩
      simp [observeFrameOutput, rawFrameOutput, frameSuccess, frameCfg, frameStacks]

theorem rawFrameOutput_counter_empty (result : Option (List Bool × List Bool)) :
    (rawFrameOutput result).stk .count = [] := by
  cases result with
  | none => rfl
  | some pair => rcases pair with ⟨payload, rest⟩; rfl

/-- The same all-string operational component serves BOTH the numeric
    source/target headers and the independent verifier pair input. -/
theorem binaryFrameTransducer_full_output (bits : List Bool) :
    ∃ result : FrameCfg,
      Nonempty (EvalsToInTime frameStep
        (frameCfg (some .prefix) (false, none) bits [] [])
        (some result) (2 * bits.length + 4)) ∧
      result.stk .count = [] ∧
      observeFrameOutput result = readVerifierPair bits ∧
      (observeFrameOutput result).map (fun p => (fromBinaryBits p.1, p.2)) =
        readBinaryNatFrame bits := by
  refine ⟨rawFrameOutput (readRawBinaryFrame bits),
    ⟨binaryFrameTransducerRun bits⟩, rawFrameOutput_counter_empty _, ?_, ?_⟩
  · rw [observe_rawFrameOutput, readRawBinaryFrame_eq_readVerifierPair]
  · rw [observe_rawFrameOutput, readBinaryNatFrame_as_raw]

/-- Preserve the COMPLETE reduction endpoint alongside the operational
    parser progress. No whole constructor/verifier machine is inferred. -/
theorem full_reduction_with_operational_frame (input : List Bool) (lambda : ℝ) :
    (SourceBitMSSCDecision input ↔
      EncodedTargetCartaDecision (scanEncodedConstructor input) lambda) ∧
    (EncodedTargetCartaDecision (scanEncodedConstructor input) lambda ↔
      ∃ cert : List Bool,
        cert.length ≤ targetBitCertificateBound (scanEncodedConstructor input).length ∧
        scanPairVerifier (verifierPairBits (scanEncodedConstructor input) cert) = true) ∧
    ∀ bits : List Bool,
      Nonempty (EvalsToInTime frameStep
        (frameCfg (some .prefix) (false, none) bits [] [])
        (some (rawFrameOutput (readRawBinaryFrame bits))) (2 * bits.length + 4)) := by
  have h := full_explicit_pair_interface input lambda
  exact ⟨h.2.1, h.2.2, fun bits => ⟨binaryFrameTransducerRun bits⟩⟩

/- Missing integration is explicit. This transducer has two caller-visible
output stacks and a success flag, not the clean single-output interface of
TM2ComputableInPolyTime. Its width stack is clean at every exit. A framing,
caller-preservation and sequencing adapter must reuse the payload/suffix in
the whole constructor and independent checker. Binary arithmetic, tree/list
scans, output serialization, the complete machine witnesses, upstream formal
hardness, dependency compatibility and ALL elaboration remain open. The
full all-refinements actual-D_lambda theorem is unchanged. -/

end PolytomyReductionModel
