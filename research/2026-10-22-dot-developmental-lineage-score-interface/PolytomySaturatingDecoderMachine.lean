/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No runtime or kernel certificate.

Uniform finite-stack bounded binary decoding. The cap is a physical unary
input, never an unbounded finite-control value. The payload is MSB-first,
as returned by the original raw frame parser's reversed output. The whole
original constructor/reduction remains the downstream obligation.
-/
import PolytomyRawRowConstructor

namespace PolytomyReductionModel

open Turing StateTransition

def cappedMSBFold (cap : ℕ) : ℕ → List Bool → ℕ
  | a, [] => a
  | a, b :: bits => cappedMSBFold cap (min (Nat.bit b a) cap) bits

theorem cappedMSBFold_le (cap a : ℕ) (bits : List Bool) (ha : a ≤ cap) :
    cappedMSBFold cap a bits ≤ cap := by
  induction bits generalizing a with
  | nil => exact ha
  | cons b bits ih => exact ih _ (min_le_right _ _)

theorem cappedMSBFold_append (cap a : ℕ) (xs ys : List Bool) :
    cappedMSBFold cap a (xs ++ ys) = cappedMSBFold cap (cappedMSBFold cap a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => exact ih _

theorem cappedMSBFold_reverse (cap : ℕ) (bits : List Bool) :
    cappedMSBFold cap 0 bits.reverse = saturatedBinaryValue cap bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      rw [List.reverse_cons, cappedMSBFold_append, ih]
      rfl

inductive SaturatingStack where
  | payload | cap | count | temp | restore
  deriving DecidableEq, Fintype

inductive SaturatingLabel where
  | setup | read | double | clip | discard | restore | clear
  deriving DecidableEq, Fintype

abbrev SaturatingCfg := TM2.Cfg (fun _ : SaturatingStack => Bool) SaturatingLabel FrameControl

def saturatingStacks (xs cs ns ts rs : List Bool) : SaturatingStack → List Bool
  | .payload => xs
  | .cap => cs
  | .count => ns
  | .temp => ts
  | .restore => rs

theorem saturatingStacks_payload (xs cs ns ts rs ys : List Bool) :
    Function.update (saturatingStacks xs cs ns ts rs) .payload ys =
      saturatingStacks ys cs ns ts rs := by
  funext k; cases k <;> simp [saturatingStacks]
theorem saturatingStacks_cap (xs cs ns ts rs ds : List Bool) :
    Function.update (saturatingStacks xs cs ns ts rs) .cap ds =
      saturatingStacks xs ds ns ts rs := by
  funext k; cases k <;> simp [saturatingStacks]
theorem saturatingStacks_count (xs cs ns ts rs ms : List Bool) :
    Function.update (saturatingStacks xs cs ns ts rs) .count ms =
      saturatingStacks xs cs ms ts rs := by
  funext k; cases k <;> simp [saturatingStacks]
theorem saturatingStacks_temp (xs cs ns ts rs us : List Bool) :
    Function.update (saturatingStacks xs cs ns ts rs) .temp us =
      saturatingStacks xs cs ns us rs := by
  funext k; cases k <;> simp [saturatingStacks]
theorem saturatingStacks_restore (xs cs ns ts rs ss : List Bool) :
    Function.update (saturatingStacks xs cs ns ts rs) .restore ss =
      saturatingStacks xs cs ns ts ss := by
  funext k; cases k <;> simp [saturatingStacks]

def saturatingCfg (l : Option SaturatingLabel) (v : FrameControl)
    (xs cs ns ts rs : List Bool) : SaturatingCfg := ⟨l, v, saturatingStacks xs cs ns ts rs⟩

def saturatingHalt (ns : List Bool) : SaturatingCfg :=
  saturatingCfg none (false, none) [] [] ns [] []

def saturatingCode : SaturatingLabel →
    TM2.Stmt (fun _ : SaturatingStack => Bool) SaturatingLabel FrameControl
  | .setup => .pop .payload (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome)
        (.branch (fun v => v.2.getD false)
          (.push .cap (fun _ => true) (.goto (fun _ => .setup)))
          (.load (fun _ => (false, none)) (.goto (fun _ => .read))))
        (.goto (fun _ => .clear)))
  | .read => .pop .payload (fun _ h => (h.getD false, h))
      (.branch (fun v => v.2.isSome)
        (.goto (fun _ => .double)) (.goto (fun _ => .clear)))
  | .double => .pop .count (fun v h => (v.1, h))
      (.branch (fun v => v.2.isSome)
        (.push .temp (fun _ => true)
          (.push .temp (fun _ => true) (.goto (fun _ => .double))))
        (.branch Prod.fst
          (.push .temp (fun _ => true) (.goto (fun _ => .clip)))
          (.goto (fun _ => .clip))))
  | .clip => .pop .cap (fun v h => (v.1, h))
      (.branch (fun v => v.2.isSome)
        (.push .restore (fun _ => true)
          (.pop .temp (fun v h => (v.1, h))
            (.branch (fun v => v.2.isSome)
              (.push .count (fun _ => true) (.goto (fun _ => .clip)))
              (.goto (fun _ => .restore)))))
        (.goto (fun _ => .discard)))
  | .discard => .pop .temp (fun v h => (v.1, h))
      (.branch (fun v => v.2.isSome)
        (.goto (fun _ => .discard)) (.goto (fun _ => .restore)))
  | .restore => .pop .restore (fun v h => (v.1, h))
      (.branch (fun v => v.2.isSome)
        (.push .cap (fun _ => true) (.goto (fun _ => .restore)))
        (.load (fun _ => (false, none)) (.goto (fun _ => .read))))
  | .clear => .pop .cap (fun _ h => (false, h))
      (.branch (fun v => v.2.isSome)
        (.goto (fun _ => .clear)) (.load (fun _ => (false, none)) .halt))

def saturatingStep : SaturatingCfg → Option SaturatingCfg := TM2.step saturatingCode

def saturatingPrepend {a b c : SaturatingCfg} {n : ℕ}
    (h : saturatingStep a = some b) (run : EvalsToInTime saturatingStep b (some c) n) :
    EvalsToInTime saturatingStep a (some c) (n + 1) :=
  EvalsToInTime.trans saturatingStep 1 n a b (some c) (evalsOneStep _ _ _ h) run

def saturatingChain {a b c : SaturatingCfg} {n m : ℕ}
    (r : EvalsToInTime saturatingStep a (some b) n)
    (s : EvalsToInTime saturatingStep b (some c) m) :
    EvalsToInTime saturatingStep a (some c) (n + m) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans saturatingStep n m a b (some c) r s

def saturatingWeaken {a b : SaturatingCfg} {n m : ℕ}
    (r : EvalsToInTime saturatingStep a (some b) n) (h : n ≤ m) :
    EvalsToInTime saturatingStep a (some b) m := { r with steps_le_m := r.steps_le_m.trans h }

theorem saturating_restore_nil (v : FrameControl) (xs cs ns : List Bool) :
    saturatingStep (saturatingCfg (some .restore) v xs cs ns [] []) =
      some (saturatingCfg (some .read) (false, none) xs cs ns [] []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_restore, saturatingStacks]
theorem saturating_restore_cons (v : FrameControl) (xs cs ns rs : List Bool) :
    saturatingStep (saturatingCfg (some .restore) v xs cs ns [] (true :: rs)) =
      some (saturatingCfg (some .restore) (v.1, some true) xs (true :: cs) ns [] rs) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_restore, saturatingStacks_cap, saturatingStacks]
theorem saturating_discard_nil (v : FrameControl) (xs cs ns rs : List Bool) :
    saturatingStep (saturatingCfg (some .discard) v xs cs ns [] rs) =
      some (saturatingCfg (some .restore) (v.1, none) xs cs ns [] rs) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_temp, saturatingStacks]
theorem saturating_discard_cons (v : FrameControl) (xs cs ns ts rs : List Bool) :
    saturatingStep (saturatingCfg (some .discard) v xs cs ns (true :: ts) rs) =
      some (saturatingCfg (some .discard) (v.1, some true) xs cs ns ts rs) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_temp, saturatingStacks]
theorem saturating_clip_cap_nil (v : FrameControl) (xs ns ts rs : List Bool) :
    saturatingStep (saturatingCfg (some .clip) v xs [] ns ts rs) =
      some (saturatingCfg (some .discard) (v.1, none) xs [] ns ts rs) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_cap, saturatingStacks]
theorem saturating_clip_temp_nil (v : FrameControl) (xs cs ns rs : List Bool) :
    saturatingStep (saturatingCfg (some .clip) v xs (true :: cs) ns [] rs) =
      some (saturatingCfg (some .restore) (v.1, none) xs cs ns [] (true :: rs)) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_cap, saturatingStacks_restore, saturatingStacks_temp, saturatingStacks]
theorem saturating_clip_cons (v : FrameControl) (xs cs ns ts rs : List Bool) :
    saturatingStep (saturatingCfg (some .clip) v xs (true :: cs) ns (true :: ts) rs) =
      some (saturatingCfg (some .clip) (v.1, some true) xs cs (true :: ns) ts (true :: rs)) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_cap, saturatingStacks_restore, saturatingStacks_temp,
    saturatingStacks_count, saturatingStacks]

def saturatingRestoreRun (u c : ℕ) (xs ns : List Bool) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .restore) v xs (List.replicate c true) ns [] (List.replicate u true))
      (some (saturatingCfg (some .read) (false, none) xs (List.replicate (c + u) true) ns [] []))
      (u + 1) := by
  induction u generalizing c v with
  | zero => simpa using evalsOneStep _ _ _ (saturating_restore_nil v xs (List.replicate c true) ns)
  | succ u ih =>
      have r := saturatingPrepend
        (saturating_restore_cons v xs (List.replicate c true) ns (List.replicate u true))
        (by simpa only [List.replicate_succ] using ih (c + 1) (v.1, some true))
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

def saturatingDiscardRun (t u c : ℕ) (xs ns : List Bool) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .discard) v xs (List.replicate c true) ns
        (List.replicate t true) (List.replicate u true))
      (some (saturatingCfg (some .read) (false, none) xs (List.replicate (c + u) true) ns [] []))
      (t + u + 2) := by
  induction t generalizing v with
  | zero =>
      have r := saturatingPrepend
        (saturating_discard_nil v xs (List.replicate c true) ns (List.replicate u true))
        (saturatingRestoreRun u c xs ns (v.1, none))
      simpa [Nat.add_assoc] using r
  | succ t ih =>
      have r := saturatingPrepend
        (saturating_discard_cons v xs (List.replicate c true) ns
          (List.replicate t true) (List.replicate u true)) (ih (v.1, some true))
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

def saturatingClipRun (c t u d : ℕ) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .clip) v xs (List.replicate c true) (List.replicate d true)
        (List.replicate t true) (List.replicate u true))
      (some (saturatingCfg (some .read) (false, none) xs (List.replicate (c + u) true)
        (List.replicate (d + min c t) true) [] []))
      (3 * c + t + u + 3) := by
  induction c generalizing t u d v with
  | zero =>
      have r := saturatingPrepend
        (saturating_clip_cap_nil v xs (List.replicate d true)
          (List.replicate t true) (List.replicate u true))
        (saturatingDiscardRun t u 0 xs (List.replicate d true) (v.1, none))
      simpa [Nat.add_assoc] using r
  | succ c ih =>
      cases t with
      | zero =>
          have r := saturatingPrepend
            (saturating_clip_temp_nil v xs (List.replicate c true)
              (List.replicate d true) (List.replicate u true))
            (by simpa only [List.replicate_succ] using
              saturatingRestoreRun (u + 1) c xs (List.replicate d true) (v.1, none))
          apply saturatingWeaken
            (by simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r)
          omega
      | succ t =>
          have r := saturatingPrepend
            (saturating_clip_cons v xs (List.replicate c true) (List.replicate d true)
              (List.replicate t true) (List.replicate u true))
            (by simpa only [List.replicate_succ] using ih t (u + 1) (d + 1) (v.1, some true))
          have hmin : min (c + 1) (t + 1) = min c t + 1 := by omega
          apply saturatingWeaken
            (by simpa [List.replicate_succ, hmin, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r)
          omega

theorem saturating_double_nil (b : Bool) (o : Option Bool) (xs cs : List Bool) (t : ℕ) :
    saturatingStep (saturatingCfg (some .double) (b, o) xs cs [] (List.replicate t true) []) =
      some (saturatingCfg (some .clip) (b, none) xs cs []
        (List.replicate (Nat.bit b 0 + t) true) []) := by
  cases b <;>
    simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
      saturatingStacks_count, saturatingStacks_temp, saturatingStacks, Nat.bit, List.replicate_succ]
theorem saturating_double_cons (b : Bool) (o : Option Bool) (xs cs ns ts : List Bool) :
    saturatingStep (saturatingCfg (some .double) (b, o) xs cs (true :: ns) ts []) =
      some (saturatingCfg (some .double) (b, some true) xs cs ns (true :: true :: ts) []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_count, saturatingStacks_temp, saturatingStacks]

def saturatingDoubleRun (a t : ℕ) (b : Bool) (o : Option Bool) (xs cs : List Bool) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .double) (b, o) xs cs (List.replicate a true)
        (List.replicate t true) [])
      (some (saturatingCfg (some .clip) (b, none) xs cs []
        (List.replicate (Nat.bit b a + t) true) [])) (a + 1) := by
  induction a generalizing t o with
  | zero => exact evalsOneStep _ _ _ (saturating_double_nil b o xs cs t)
  | succ a ih =>
      have r := saturatingPrepend
        (saturating_double_cons b o xs cs (List.replicate a true) (List.replicate t true))
        (by simpa only [List.replicate_succ] using ih (t + 2) (some true))
      have hb : Nat.bit b a + (t + 2) = Nat.bit b (a + 1) + t := by
        cases b <;> simp only [Nat.bit] <;> omega
      rw [hb] at r
      simpa only [List.replicate_succ] using r

theorem saturating_read_cons (v : FrameControl) (b : Bool) (xs cs ns : List Bool) :
    saturatingStep (saturatingCfg (some .read) v (b :: xs) cs ns [] []) =
      some (saturatingCfg (some .double) (b, some b) xs cs ns [] []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_payload, saturatingStacks]
theorem saturating_read_nil (v : FrameControl) (cs ns : List Bool) :
    saturatingStep (saturatingCfg (some .read) v [] cs ns [] []) =
      some (saturatingCfg (some .clear) (false, none) [] cs ns [] []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_payload, saturatingStacks]

def saturatingAdvanceRun (C a : ℕ) (ha : a ≤ C) (b : Bool) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .read) v (b :: xs) (List.replicate C true) (List.replicate a true) [] [])
      (some (saturatingCfg (some .read) (false, none) xs (List.replicate C true)
        (List.replicate (min (Nat.bit b a) C) true) [] [])) (6 * C + 6) := by
  have double := saturatingDoubleRun a 0 b (some b) xs (List.replicate C true)
  have clip := saturatingClipRun C (Nat.bit b a) 0 0 xs (b, none)
  have r := saturatingPrepend
    (saturating_read_cons v b xs (List.replicate C true) (List.replicate a true))
    (saturatingChain (by simpa using double) (by simpa using clip))
  apply saturatingWeaken (by simpa only [min_comm] using r)
  cases b <;> simp only [Nat.bit] <;> omega

def saturatingReadRun (C a : ℕ) (ha : a ≤ C) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .read) v xs (List.replicate C true) (List.replicate a true) [] [])
      (some (saturatingCfg (some .clear) (false, none) [] (List.replicate C true)
        (List.replicate (cappedMSBFold C a xs) true) [] []))
      (xs.length * (6 * C + 6) + 1) := by
  induction xs generalizing a v with
  | nil => simpa [cappedMSBFold] using
      evalsOneStep _ _ _ (saturating_read_nil v (List.replicate C true) (List.replicate a true))
  | cons b xs ih =>
      have r := saturatingChain (saturatingAdvanceRun C a ha b xs v)
        (ih (min (Nat.bit b a) C) (min_le_right _ _) (false, none))
      convert r using 1 <;> simp only [cappedMSBFold, List.length_cons] <;> ring

theorem saturating_clear_nil (v : FrameControl) (ns : List Bool) :
    saturatingStep (saturatingCfg (some .clear) v [] [] ns [] []) = some (saturatingHalt ns) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_cap, saturatingStacks, saturatingHalt]
theorem saturating_clear_cons (v : FrameControl) (cs ns : List Bool) :
    saturatingStep (saturatingCfg (some .clear) v [] (true :: cs) ns [] []) =
      some (saturatingCfg (some .clear) (false, some true) [] cs ns [] []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_cap, saturatingStacks]

def saturatingClearRun (C : ℕ) (ns : List Bool) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .clear) v [] (List.replicate C true) ns [] [])
      (some (saturatingHalt ns)) (C + 1) := by
  induction C generalizing v with
  | zero => exact evalsOneStep _ _ _ (saturating_clear_nil v ns)
  | succ C ih =>
      have r := saturatingPrepend (saturating_clear_cons v (List.replicate C true) ns)
        (ih (false, some true))
      simpa only [List.replicate_succ] using r

theorem saturating_setup_true (v : FrameControl) (xs cs : List Bool) :
    saturatingStep (saturatingCfg (some .setup) v (true :: xs) cs [] [] []) =
      some (saturatingCfg (some .setup) (false, some true) xs (true :: cs) [] [] []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_payload, saturatingStacks_cap, saturatingStacks]
theorem saturating_setup_false (v : FrameControl) (xs cs : List Bool) :
    saturatingStep (saturatingCfg (some .setup) v (false :: xs) cs [] [] []) =
      some (saturatingCfg (some .read) (false, none) xs cs [] [] []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_payload, saturatingStacks]
theorem saturating_setup_nil (v : FrameControl) (cs : List Bool) :
    saturatingStep (saturatingCfg (some .setup) v [] cs [] [] []) =
      some (saturatingCfg (some .clear) (false, none) [] cs [] [] []) := by
  simp [saturatingStep, saturatingCfg, saturatingCode, TM2.step, TM2.stepAux,
    saturatingStacks_payload, saturatingStacks]

def saturatingSetupRun (C k : ℕ) (xs : List Bool) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .setup) v (unaryFrame C ++ xs) (List.replicate k true) [] [] [])
      (some (saturatingCfg (some .read) (false, none) xs (List.replicate (k + C) true) [] [] []))
      (C + 1) := by
  induction C generalizing k v with
  | zero => simpa [unaryFrame] using
      evalsOneStep _ _ _ (saturating_setup_false v xs (List.replicate k true))
  | succ C ih =>
      have r := saturatingPrepend
        (saturating_setup_true v (unaryFrame C ++ xs) (List.replicate k true))
        (by simpa only [List.replicate_succ] using ih (k + 1) (false, some true))
      simpa [unaryFrame, List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

def saturatingSetupMissingRun (C k : ℕ) (v : FrameControl) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .setup) v (List.replicate C true) (List.replicate k true) [] [] [])
      (some (saturatingCfg (some .clear) (false, none) []
        (List.replicate (k + C) true) [] [] [])) (C + 1) := by
  induction C generalizing k v with
  | zero => simpa using evalsOneStep _ _ _ (saturating_setup_nil v (List.replicate k true))
  | succ C ih =>
      have r := saturatingPrepend
        (saturating_setup_true v (List.replicate C true) (List.replicate k true))
        (by simpa only [List.replicate_succ] using ih (k + 1) (false, some true))
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem readUnaryFrame_decomposition (bits : List Bool) (n : ℕ) (rest : List Bool)
    (h : readUnaryFrame bits = some (n, rest)) : bits = unaryFrame n ++ rest := by
  induction bits generalizing n rest with
  | nil => simp [readUnaryFrame] at h
  | cons b bits ih =>
      cases b with
      | false =>
          have he : (0, bits) = (n, rest) := by simpa only [readUnaryFrame, Option.some.injEq] using h
          cases he
          simp [unaryFrame]
      | true =>
          cases hp : readUnaryFrame bits with
          | none => simp [readUnaryFrame, hp] at h
          | some p =>
              rcases p with ⟨k, after⟩
              have he : (k + 1, after) = (n, rest) := by
                simpa only [readUnaryFrame, hp, Option.some.injEq] using h
              cases he
              rw [ih k after hp]
              simp [unaryFrame, List.replicate_succ]

theorem readUnaryFrame_missing (bits : List Bool) (h : readUnaryFrame bits = none) :
    bits = List.replicate bits.length true := by
  revert h
  induction bits with
  | nil => intro h; rfl
  | cons b bits ih =>
      intro h
      cases b with
      | false => simp [readUnaryFrame] at h
      | true =>
          cases hp : readUnaryFrame bits with
          | none => simpa only [List.length_cons, List.replicate_succ] using
              congrArg (List.cons true) (ih hp)
          | some p => simp [readUnaryFrame, hp] at h

/-- Total word interface. The physical unary cap precedes its delimiter;
    all remaining bits are interpreted MOST-significant first. A missing
    cap delimiter returns the empty unary word. This zero/failure convention
    is deliberate, not an Option decoder or the full source grammar. -/
def cappedUnaryWord (bits : List Bool) : List Bool :=
  match readUnaryFrame bits with
  | none => []
  | some (C, xs) => List.replicate (cappedMSBFold C 0 xs) true

theorem cappedUnaryWord_original_payload (cap : ℕ) (bits : List Bool) :
    cappedUnaryWord (unaryFrame cap ++ bits.reverse) =
      List.replicate (saturatedBinaryValue cap bits) true := by
  simp only [cappedUnaryWord, readUnaryFrame_encode, cappedMSBFold_reverse]

/-- The original raw frame's failure flag and suffix are retained. The
    numeric primitive is called ONLY after a successful raw split, with
    exactly its reversed payload, so failure is never conflated with zero. -/
def readSaturatedViaPrimitive (cap : ℕ) (bits : List Bool) : Option (ℕ × List Bool) :=
  (readRawBinaryFrame bits).map (fun p =>
    ((cappedUnaryWord (unaryFrame cap ++ p.1.reverse)).length, p.2))

theorem readSaturatedViaPrimitive_eq (cap : ℕ) (bits : List Bool) :
    readSaturatedViaPrimitive cap bits = readSaturatedBinaryNatFrame cap bits := by
  unfold readSaturatedViaPrimitive readRawBinaryFrame readSaturatedBinaryNatFrame
  cases hp : readUnaryFrame bits with
  | none => rfl
  | some p =>
      rcases p with ⟨n, rest⟩
      by_cases hn : n ≤ rest.length <;>
        simp [hn, cappedUnaryWord_original_payload]

def saturatingDecoder : FinTM2 where
  K := SaturatingStack
  k₀ := .payload
  k₁ := .count
  Γ _ := Bool
  Λ := SaturatingLabel
  main := .setup
  σ := FrameControl
  initialState := (false, none)
  m := saturatingCode

theorem saturatingDecoder_init (bits : List Bool) :
    initList saturatingDecoder bits = saturatingCfg (some .setup) (false, none) bits [] [] [] [] := by
  change (⟨some .setup, (false, none), _⟩ : SaturatingCfg) =
    ⟨some .setup, (false, none), saturatingStacks bits [] [] [] []⟩
  congr 1
  funext k; cases k <;> simp [initList, saturatingDecoder, saturatingStacks]

theorem saturatingDecoder_halt (bits : List Bool) :
    haltList saturatingDecoder bits = saturatingHalt bits := by
  change (⟨none, (false, none), _⟩ : SaturatingCfg) =
    ⟨none, (false, none), saturatingStacks [] [] bits [] []⟩
  congr 1
  funext k; cases k <;> simp [haltList, saturatingDecoder, saturatingStacks]

def saturatingDecoderRun (bits : List Bool) :
    EvalsToInTime saturatingStep
      (saturatingCfg (some .setup) (false, none) bits [] [] [] [])
      (some (saturatingHalt (cappedUnaryWord bits)))
      (10 * bits.length ^ 2 + 20 * bits.length + 20) := by
  cases hp : readUnaryFrame bits with
  | none =>
      have he := readUnaryFrame_missing bits hp
      have setup := saturatingSetupMissingRun bits.length 0 (false, none)
      have clear := saturatingClearRun bits.length [] (false, none)
      have r := saturatingChain (by simpa only [Nat.zero_add, List.replicate_zero] using setup) clear
      apply saturatingWeaken
        (by simpa only [← he, cappedUnaryWord, hp] using r)
      nlinarith
  | some p =>
      rcases p with ⟨C, xs⟩
      have he := readUnaryFrame_decomposition bits C xs hp
      have hlen : bits.length = C + 1 + xs.length := by
        rw [he]
        simp [unaryFrame, Nat.add_assoc]
      have setup := saturatingSetupRun C 0 xs (false, none)
      have body := saturatingReadRun C 0 (Nat.zero_le _) xs (false, none)
      have clear := saturatingClearRun C (List.replicate (cappedMSBFold C 0 xs) true) (false, none)
      have r := saturatingChain
        (by simpa only [Nat.zero_add, List.replicate_zero] using setup)
        (saturatingChain body clear)
      apply saturatingWeaken (by simpa only [← he, cappedUnaryWord, hp] using r)
      have hc : C ≤ bits.length := by omega
      have hx : xs.length ≤ bits.length := by omega
      have hp' := Nat.mul_le_mul hx (show 6 * C + 6 ≤ 6 * bits.length + 6 by omega)
      nlinarith

/-- Supplied source witness for the exact total capped numeric primitive.
    All cap, carry and cleanup storage is finite-alphabet stack data. -/
def saturatingDecoderPoly :
    TM2ComputableInPolyTime (fun bits : List Bool => bits)
      (fun bits : List Bool => bits) cappedUnaryWord where
  tm := saturatingDecoder
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 10 * Polynomial.X ^ 2 + 20 * Polynomial.X + 20
  outputsFun bits := by
    simpa [TM2OutputsInTime, saturatingDecoder_init, saturatingDecoder_halt,
      saturatingStep, FinTM2.step, saturatingDecoder] using saturatingDecoderRun bits

theorem full_raw_constructor_with_numeric_decoder (input : List Bool) (lambda : ℝ) :
    (rawRowConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔ EncodedTargetCartaDecision (rawRowConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (rawRowConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (rawRowConstructor input).length ∧
          boundedEncodedTarget (rawRowConstructor input) cert = true) ∧
      Nonempty (TM2ComputableInPolyTime (fun bits : List Bool => bits)
        (fun bits : List Bool => bits) cappedUnaryWord) := by
  have h := full_raw_row_constructor_interface input lambda
  exact ⟨h.1, h.2.1, h.2.2, ⟨saturatingDecoderPoly⟩⟩

/- This is not the complete numeric-frame parser: its cap is a unary
parameter and its remaining input is the already extracted reversed
payload. Framing/suffix/failure flags and caller preservation must still
be composed explicitly. Whole nested source parsing, raw-row arithmetic,
constructor and independent checker programs, compatible closed upstream
hardness and every kernel check remain open. No new biological assumptions.
-/

end PolytomyReductionModel
