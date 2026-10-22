/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution or kernel certificate.

Concrete finite Boolean-TM2 machine computing the ORIGINAL binaryNatFrame
of its input length. A unary counter may therefore be serialized without
introducing a new numeral format or an unbounded control register.
This is an operational primitive for the whole direct constructor, not
the complete constructor/verifier or its upstream hardness proof.
-/
import PolytomyDirectCanonicalOutput
import PolytomyBinaryFrameMachine

namespace PolytomyReductionModel

open Turing StateTransition

def incrementBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: incrementBits bits

theorem incrementBits_nat (n : ℕ) : incrementBits n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [incrementBits]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases b with
      | false =>
          change true :: n.bits = (Nat.bit false n + 1).bits
          have he : Nat.bit false n + 1 = Nat.bit true n := by simp [Nat.bit]
          rw [he, Nat.bits_append_bit n true (fun _ => rfl)]
      | true =>
          change false :: incrementBits n.bits = (Nat.bit true n + 1).bits
          rw [ih]
          have he : Nat.bit true n + 1 = Nat.bit false (n + 1) := by
            simp only [Nat.bit]
            omega
          rw [he, Nat.bits_append_bit (n + 1) false (by intro h; omega)]

inductive CounterStack where
  | input | counter | scratch | width
  deriving DecidableEq, Fintype

inductive CounterLabel where
  | tick | carry | restore | toScratch | toOutput | frame
  deriving DecidableEq, Fintype

abbrev CounterCfg := TM2.Cfg (fun _ : CounterStack => Bool) CounterLabel FrameControl

def counterStacks (xs cs zs ws : List Bool) : CounterStack → List Bool
  | .input => xs
  | .counter => cs
  | .scratch => zs
  | .width => ws

theorem counterStacks_input (xs cs zs ws ys : List Bool) :
    Function.update (counterStacks xs cs zs ws) .input ys = counterStacks ys cs zs ws := by
  funext k; cases k <;> simp [counterStacks]
theorem counterStacks_counter (xs cs zs ws ds : List Bool) :
    Function.update (counterStacks xs cs zs ws) .counter ds = counterStacks xs ds zs ws := by
  funext k; cases k <;> simp [counterStacks]
theorem counterStacks_scratch (xs cs zs ws ts : List Bool) :
    Function.update (counterStacks xs cs zs ws) .scratch ts = counterStacks xs cs ts ws := by
  funext k; cases k <;> simp [counterStacks]
theorem counterStacks_width (xs cs zs ws vs : List Bool) :
    Function.update (counterStacks xs cs zs ws) .width vs = counterStacks xs cs zs vs := by
  funext k; cases k <;> simp [counterStacks]

def counterCfg (l : Option CounterLabel) (v : FrameControl)
    (xs cs zs ws : List Bool) : CounterCfg := ⟨l, v, counterStacks xs cs zs ws⟩

def counterHalt (xs : List Bool) : CounterCfg := counterCfg none (false, none) xs [] [] []

def counterCode : CounterLabel →
    TM2.Stmt (fun _ : CounterStack => Bool) CounterLabel FrameControl
  | .tick => .pop .input (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome)
        (.goto (fun _ => .carry)) (.goto (fun _ => .toScratch)))
  | .carry => .pop .counter (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome && v.2.getD false)
        (.push .scratch (fun _ => false) (.goto (fun _ => .carry)))
        (.push .counter (fun _ => true) (.goto (fun _ => .restore))))
  | .restore => .pop .scratch (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome)
        (.push .counter (fun _ => false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .tick)))
  | .toScratch => .pop .counter (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome)
        (.push .scratch (fun v => v.2.getD false)
          (.push .width (fun _ => true) (.goto (fun _ => .toScratch))))
        (.goto (fun _ => .toOutput)))
  | .toOutput => .pop .scratch (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome)
        (.push .input (fun v => v.2.getD false) (.goto (fun _ => .toOutput)))
        (.push .input (fun _ => false) (.goto (fun _ => .frame))))
  | .frame => .pop .width (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome)
        (.push .input (fun _ => true) (.goto (fun _ => .frame)))
        (.load (fun _ => (false, none)) .halt))

def counterStep : CounterCfg → Option CounterCfg := TM2.step counterCode

def counterPrepend {a b c : CounterCfg} {n : ℕ}
    (h : counterStep a = some b) (run : EvalsToInTime counterStep b (some c) n) :
    EvalsToInTime counterStep a (some c) (n + 1) :=
  EvalsToInTime.trans counterStep 1 n a b (some c) (evalsOneStep _ _ _ h) run

def counterChain {a b c : CounterCfg} {n m : ℕ}
    (r : EvalsToInTime counterStep a (some b) n)
    (s : EvalsToInTime counterStep b (some c) m) :
    EvalsToInTime counterStep a (some c) (n + m) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans counterStep n m a b (some c) r s

def counterWeaken {a b : CounterCfg} {n m : ℕ}
    (r : EvalsToInTime counterStep a (some b) n) (h : n ≤ m) :
    EvalsToInTime counterStep a (some b) m := { r with steps_le_m := r.steps_le_m.trans h }

theorem counter_tick_cons (v : FrameControl) (b : Bool) (xs cs : List Bool) :
    counterStep (counterCfg (some .tick) v (b :: xs) cs [] []) =
      some (counterCfg (some .carry) (false, some b) xs cs [] []) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_input, counterStacks]
theorem counter_tick_nil (v : FrameControl) (cs : List Bool) :
    counterStep (counterCfg (some .tick) v [] cs [] []) =
      some (counterCfg (some .toScratch) (false, none) [] cs [] []) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_input, counterStacks]
theorem counter_carry_nil (v : FrameControl) (xs zs : List Bool) :
    counterStep (counterCfg (some .carry) v xs [] zs []) =
      some (counterCfg (some .restore) (false, none) xs [true] zs []) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_counter, counterStacks]
theorem counter_carry_false (v : FrameControl) (xs cs zs : List Bool) :
    counterStep (counterCfg (some .carry) v xs (false :: cs) zs []) =
      some (counterCfg (some .restore) (false, some false) xs (true :: cs) zs []) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_counter, counterStacks]
theorem counter_carry_true (v : FrameControl) (xs cs zs : List Bool) :
    counterStep (counterCfg (some .carry) v xs (true :: cs) zs []) =
      some (counterCfg (some .carry) (false, some true) xs cs (false :: zs) []) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_counter, counterStacks_scratch, counterStacks]
theorem counter_restore_cons (v : FrameControl) (xs cs zs : List Bool) :
    counterStep (counterCfg (some .restore) v xs cs (false :: zs) []) =
      some (counterCfg (some .restore) (false, some false) xs (false :: cs) zs []) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_scratch, counterStacks_counter, counterStacks]
theorem counter_restore_nil (v : FrameControl) (xs cs : List Bool) :
    counterStep (counterCfg (some .restore) v xs cs [] []) =
      some (counterCfg (some .tick) (false, none) xs cs [] []) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_scratch, counterStacks]

def counterRestoreRun (z : ℕ) (xs cs : List Bool) (v : FrameControl) :
    EvalsToInTime counterStep
      (counterCfg (some .restore) v xs cs (List.replicate z false) [])
      (some (counterCfg (some .tick) (false, none) xs (List.replicate z false ++ cs) [] []))
      (z + 1) := by
  induction z generalizing cs v with
  | zero => exact evalsOneStep _ _ _ (counter_restore_nil v xs cs)
  | succ z ih =>
      have r := counterPrepend (counter_restore_cons v xs cs (List.replicate z false))
        (ih (false :: cs) (false, some false))
      have hout : List.replicate z false ++ false :: cs =
          List.replicate (z + 1) false ++ cs := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [hout] at r
      simpa only [List.replicate_succ] using r

def counterCarryRun (cs : List Bool) (z : ℕ) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime counterStep
      (counterCfg (some .carry) v xs cs (List.replicate z false) [])
      (some (counterCfg (some .tick) (false, none) xs
        (List.replicate z false ++ incrementBits cs) [] []))
      (2 * cs.length + z + 3) := by
  induction cs generalizing z v with
  | nil =>
      have r := counterPrepend (counter_carry_nil v xs (List.replicate z false))
        (counterRestoreRun z xs [true] (false, none))
      exact counterWeaken (by simpa only [incrementBits] using r) (by simp; omega)
  | cons b cs ih =>
      cases b with
      | false =>
          have r := counterPrepend (counter_carry_false v xs cs (List.replicate z false))
            (counterRestoreRun z xs (true :: cs) (false, some false))
          exact counterWeaken (by simpa only [incrementBits] using r)
            (by simp only [List.length_cons]; omega)
      | true =>
          have tail := ih (z + 1) (false, some true)
          have hout : List.replicate (z + 1) false ++ incrementBits cs =
              List.replicate z false ++ false :: incrementBits cs := by
            rw [List.replicate_succ', List.append_assoc]
            rfl
          rw [hout] at tail
          have tail' := (by simpa only [List.replicate_succ] using tail :
            EvalsToInTime counterStep
              (counterCfg (some .carry) (false, some true) xs cs
                (false :: List.replicate z false) [])
              (some (counterCfg (some .tick) (false, none) xs
                (List.replicate z false ++ false :: incrementBits cs) [] []))
              (2 * cs.length + (z + 1) + 3))
          have r := counterPrepend (counter_carry_true v xs cs (List.replicate z false)) tail'
          exact counterWeaken (by simpa only [incrementBits] using r)
            (by simp only [List.length_cons]; omega)

def counterTickBudget (k n : ℕ) : ℕ := n * (2 * (k + n) + 4) + 1

def counterTickRun (xs : List Bool) (k : ℕ) (v : FrameControl) :
    EvalsToInTime counterStep
      (counterCfg (some .tick) v xs k.bits [] [])
      (some (counterCfg (some .toScratch) (false, none) [] (k + xs.length).bits [] []))
      (counterTickBudget k xs.length) := by
  induction xs generalizing k v with
  | nil => simpa [counterTickBudget] using evalsOneStep _ _ _ (counter_tick_nil v k.bits)
  | cons b xs ih =>
      have carry := counterCarryRun k.bits 0 xs (false, some b)
      have carry' : EvalsToInTime counterStep
          (counterCfg (some .carry) (false, some b) xs k.bits [] [])
          (some (counterCfg (some .tick) (false, none) xs (k + 1).bits [] []))
          (2 * k.bits.length + 3) := by
        simpa only [List.replicate_zero, List.nil_append, Nat.add_zero, incrementBits_nat] using carry
      have r := counterChain
        (counterPrepend (counter_tick_cons v b xs k.bits) carry')
        (ih (k + 1) (false, none))
      have hk : (k + 1) + xs.length = k + (b :: xs).length := by simp; omega
      rw [hk] at r
      apply counterWeaken r
      have hlen := binaryBits_length_le k
      simp only [counterTickBudget, List.length_cons]
      nlinarith

theorem counter_toScratch_cons (v : FrameControl) (b : Bool) (xs cs zs ws : List Bool) :
    counterStep (counterCfg (some .toScratch) v xs (b :: cs) zs ws) =
      some (counterCfg (some .toScratch) (false, some b) xs cs (b :: zs) (true :: ws)) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_counter, counterStacks_scratch, counterStacks_width, counterStacks]
theorem counter_toScratch_nil (v : FrameControl) (xs zs ws : List Bool) :
    counterStep (counterCfg (some .toScratch) v xs [] zs ws) =
      some (counterCfg (some .toOutput) (false, none) xs [] zs ws) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_counter, counterStacks]
theorem counter_toOutput_cons (v : FrameControl) (b : Bool) (xs zs ws : List Bool) :
    counterStep (counterCfg (some .toOutput) v xs [] (b :: zs) ws) =
      some (counterCfg (some .toOutput) (false, some b) (b :: xs) [] zs ws) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_scratch, counterStacks_input, counterStacks]
theorem counter_toOutput_nil (v : FrameControl) (xs ws : List Bool) :
    counterStep (counterCfg (some .toOutput) v xs [] [] ws) =
      some (counterCfg (some .frame) (false, none) (false :: xs) [] [] ws) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_scratch, counterStacks_input, counterStacks]
theorem counter_frame_cons (v : FrameControl) (xs ws : List Bool) :
    counterStep (counterCfg (some .frame) v xs [] [] (true :: ws)) =
      some (counterCfg (some .frame) (false, some true) (true :: xs) [] [] ws) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_width, counterStacks_input, counterStacks]
theorem counter_frame_nil (v : FrameControl) (xs : List Bool) :
    counterStep (counterCfg (some .frame) v xs [] [] []) = some (counterHalt xs) := by
  simp [counterStep, counterCfg, counterCode, TM2.step, TM2.stepAux,
    counterStacks_width, counterStacks, counterHalt]

def counterFrameRun (w : ℕ) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime counterStep
      (counterCfg (some .frame) v xs [] [] (List.replicate w true))
      (some (counterHalt (List.replicate w true ++ xs))) (w + 1) := by
  induction w generalizing xs v with
  | zero => exact evalsOneStep _ _ _ (counter_frame_nil v xs)
  | succ w ih =>
      have r := counterPrepend (counter_frame_cons v xs (List.replicate w true))
        (ih (true :: xs) (false, some true))
      have hout : List.replicate w true ++ true :: xs =
          List.replicate (w + 1) true ++ xs := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [hout] at r
      simpa only [List.replicate_succ] using r

def counterOutputRun (zs : List Bool) (w : ℕ) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime counterStep
      (counterCfg (some .toOutput) v xs [] zs (List.replicate w true))
      (some (counterHalt (unaryFrame w ++ zs.reverse ++ xs))) (zs.length + w + 2) := by
  induction zs generalizing xs v with
  | nil =>
      have r := counterPrepend (counter_toOutput_nil v xs (List.replicate w true))
        (counterFrameRun w (false :: xs) (false, none))
      simpa [unaryFrame, List.append_assoc, Nat.add_assoc] using r
  | cons b zs ih =>
      have r := counterPrepend (counter_toOutput_cons v b xs zs (List.replicate w true))
        (ih (b :: xs) (false, some b))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using r

def counterFinishRun (cs zs : List Bool) (w : ℕ) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime counterStep
      (counterCfg (some .toScratch) v xs cs zs (List.replicate w true))
      (some (counterHalt (unaryFrame (w + cs.length) ++ zs.reverse ++ cs ++ xs)))
      (3 * cs.length + zs.length + w + 3) := by
  induction cs generalizing zs w v with
  | nil =>
      have r := counterPrepend (counter_toScratch_nil v xs zs (List.replicate w true))
        (counterOutputRun zs w xs (false, none))
      simpa [List.append_assoc, Nat.add_assoc] using r
  | cons b cs ih =>
      have tail := ih (b :: zs) (w + 1) (false, some b)
      have r := counterPrepend
        (counter_toScratch_cons v b xs cs zs (List.replicate w true))
        (by simpa only [List.replicate_succ] using tail)
      apply counterWeaken
        (by simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using r)
      simp only [List.length_cons]
      omega

def binaryCounterEncoder : FinTM2 where
  K := CounterStack
  k₀ := .input
  k₁ := .input
  Γ _ := Bool
  Λ := CounterLabel
  main := .tick
  σ := FrameControl
  initialState := (false, none)
  m := counterCode

theorem binaryCounterEncoder_init (bits : List Bool) :
    initList binaryCounterEncoder bits = counterCfg (some .tick) (false, none) bits [] [] [] := by
  change (⟨some .tick, (false, none), _⟩ : CounterCfg) =
    ⟨some .tick, (false, none), counterStacks bits [] [] []⟩
  congr 1
  funext k; cases k <;> simp [initList, binaryCounterEncoder, counterStacks]

theorem binaryCounterEncoder_halt (bits : List Bool) :
    haltList binaryCounterEncoder bits = counterHalt bits := by
  change (⟨none, (false, none), _⟩ : CounterCfg) =
    ⟨none, (false, none), counterStacks bits [] [] []⟩
  congr 1
  funext k; cases k <;> simp [haltList, binaryCounterEncoder, counterStacks]

def binaryCounterEncoderRun (bits : List Bool) :
    EvalsToInTime counterStep
      (counterCfg (some .tick) (false, none) bits [] [] [])
      (some (counterHalt (binaryNatFrame bits.length)))
      (2 * bits.length ^ 2 + 10 * bits.length + 10) := by
  have ticks := counterTickRun bits 0 (false, none)
  have finish := counterFinishRun bits.length.bits [] 0 [] (false, none)
  have r := counterChain (by simpa using ticks) finish
  apply counterWeaken
    (by simpa [binaryNatFrame, List.append_assoc] using r)
  have hlen := binaryBits_length_le bits.length
  simp only [counterTickBudget, List.length_nil, Nat.zero_add, Nat.add_zero]
  nlinarith

/-- Supplied concrete all-input source term for this serializer primitive.
    It counts ALL input bits; the intended unary counters are a special case. -/
def binaryCounterEncoderPoly :
    TM2ComputableInPolyTime (fun bits : List Bool => bits)
      (fun bits : List Bool => bits) (fun bits => binaryNatFrame bits.length) where
  tm := binaryCounterEncoder
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X ^ 2 + 10 * Polynomial.X + 10
  outputsFun bits := by
    simpa [TM2OutputsInTime, binaryCounterEncoder_init, binaryCounterEncoder_halt,
      counterStep, FinTM2.step, binaryCounterEncoder] using binaryCounterEncoderRun bits

theorem binaryCounterEncoder_unary (n : ℕ) :
    (fun bits : List Bool => binaryNatFrame bits.length) (List.replicate n true) =
      binaryNatFrame n := by simp

theorem full_direct_interface_with_binary_encoder (input : List Bool) (lambda : ℝ) :
    (directBoundedConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (directBoundedConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (directBoundedConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (directBoundedConstructor input).length ∧
          boundedEncodedTarget (directBoundedConstructor input) cert = true) ∧
      Nonempty (TM2ComputableInPolyTime (fun bits : List Bool => bits)
        (fun bits : List Bool => bits) (fun bits => binaryNatFrame bits.length)) := by
  have h := full_direct_constructor_interface input lambda
  exact ⟨h.1, h.2.1, h.2.2, ⟨binaryCounterEncoderPoly⟩⟩

/- No claim of a complete ConstructorMachineWitness follows from this
primitive alone. Caller composition, concrete row/membership programs and
the full independent checker, their total bounds/cleanup, compatible
upstream encoded hardness and all kernel checks remain open.
-/

end PolytomyReductionModel
