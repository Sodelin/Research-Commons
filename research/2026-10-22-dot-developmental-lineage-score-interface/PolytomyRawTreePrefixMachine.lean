/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Concrete fixed two-stack parser for the original arbitrary-binary-tree
token grammar. Pending child slots are unary DATA, never finite-control
naturals. The two unary leaf fields are consumed, not range-validated.
This is a syntax/prefix component of the ORIGINAL independent verifier.
-/
import PolytomyRawForestGrammar

namespace PolytomyReductionModel

open Turing StateTransition

inductive TreeSkipStack where
  | input | pending
  deriving DecidableEq, Fintype

inductive TreeSkipLabel where
  | start | read | block | type | clear
  deriving DecidableEq, Fintype

abbrev TreeSkipCfg := TM2.Cfg (fun _ : TreeSkipStack => Bool) TreeSkipLabel FrameControl

def treeSkipStacks (xs ps : List Bool) : TreeSkipStack → List Bool
  | .input => xs
  | .pending => ps

theorem treeSkipStacks_input (xs ps ys : List Bool) :
    Function.update (treeSkipStacks xs ps) .input ys = treeSkipStacks ys ps := by
  funext k; cases k <;> simp [treeSkipStacks]

theorem treeSkipStacks_pending (xs ps qs : List Bool) :
    Function.update (treeSkipStacks xs ps) .pending qs = treeSkipStacks xs qs := by
  funext k; cases k <;> simp [treeSkipStacks]

def treeSkipCfg (l : Option TreeSkipLabel) (v : FrameControl) (xs ps : List Bool) : TreeSkipCfg :=
  ⟨l, v, treeSkipStacks xs ps⟩

def treeSkipCode : TreeSkipLabel →
    TM2.Stmt (fun _ : TreeSkipStack => Bool) TreeSkipLabel FrameControl
  | .start => .load (fun _ => (false, none))
      (.push .pending (fun _ => true) (.goto (fun _ => .read)))
  | .read =>
      .pop .pending (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.pop .input (fun _ h => (false, h))
            (.branch (fun v => v.2.isSome)
              (.branch (fun v => v.2.getD false)
                (.goto (fun _ => .block))
                (.push .pending (fun _ => true)
                  (.push .pending (fun _ => true) (.goto (fun _ => .read)))))
              (.goto (fun _ => .clear))))
          (.load (fun _ => (true, none)) .halt))
  | .block =>
      .pop .input (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2.getD false)
            (.goto (fun _ => .block)) (.goto (fun _ => .type)))
          (.goto (fun _ => .clear)))
  | .type =>
      .pop .input (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2.getD false)
            (.goto (fun _ => .type)) (.goto (fun _ => .read)))
          (.goto (fun _ => .clear)))
  | .clear =>
      .pop .pending (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.goto (fun _ => .clear)) (.load (fun _ => (false, none)) .halt))

def treeSkipStep : TreeSkipCfg → Option TreeSkipCfg := TM2.step treeSkipCode

def treeSkipEnd : Option (List Bool) → TreeSkipCfg
  | none => treeSkipCfg none (false, none) [] []
  | some rest => treeSkipCfg none (true, none) rest []

def treeSkipPrepend {a b c : TreeSkipCfg} {n : ℕ}
    (h : treeSkipStep a = some b) (run : EvalsToInTime treeSkipStep b (some c) n) :
    EvalsToInTime treeSkipStep a (some c) (n + 1) :=
  EvalsToInTime.trans treeSkipStep 1 n a b (some c) (evalsOneStep _ _ _ h) run

def treeSkipThen {a b c : TreeSkipCfg} {m n : ℕ}
    (h : EvalsToInTime treeSkipStep a (some b) m)
    (run : EvalsToInTime treeSkipStep b (some c) n) :
    EvalsToInTime treeSkipStep a (some c) (m + n) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans treeSkipStep m n a b (some c) h run

def treeSkipWeaken {a b : TreeSkipCfg} {n m : ℕ}
    (run : EvalsToInTime treeSkipStep a (some b) n) (h : n ≤ m) :
    EvalsToInTime treeSkipStep a (some b) m :=
  { run with steps_le_m := run.steps_le_m.trans h }

theorem treeSkip_start (v : FrameControl) (bits : List Bool) :
    treeSkipStep (treeSkipCfg (some .start) v bits []) =
      some (treeSkipCfg (some .read) (false, none) bits [true]) := by
  simp [treeSkipStep, treeSkipCfg, treeSkipCode, TM2.step, TM2.stepAux,
    treeSkipStacks_pending, treeSkipStacks]

theorem treeSkip_read_done (v : FrameControl) (bits : List Bool) :
    treeSkipStep (treeSkipCfg (some .read) v bits []) = some (treeSkipEnd (some bits)) := by
  simp [treeSkipStep, treeSkipCfg, treeSkipCode, TM2.step, TM2.stepAux,
    treeSkipStacks_pending, treeSkipStacks, treeSkipEnd]

theorem treeSkip_read_internal (v : FrameControl) (bits ps : List Bool) :
    treeSkipStep (treeSkipCfg (some .read) v (false :: bits) (true :: ps)) =
      some (treeSkipCfg (some .read) (false, some false) bits (true :: true :: ps)) := by
  simp [treeSkipStep, treeSkipCfg, treeSkipCode, TM2.step, TM2.stepAux,
    treeSkipStacks_input, treeSkipStacks_pending, treeSkipStacks]

theorem treeSkip_read_leaf (v : FrameControl) (bits ps : List Bool) :
    treeSkipStep (treeSkipCfg (some .read) v (true :: bits) (true :: ps)) =
      some (treeSkipCfg (some .block) (false, some true) bits ps) := by
  simp [treeSkipStep, treeSkipCfg, treeSkipCode, TM2.step, TM2.stepAux,
    treeSkipStacks_input, treeSkipStacks_pending, treeSkipStacks]

theorem treeSkip_read_missing (v : FrameControl) (ps : List Bool) :
    treeSkipStep (treeSkipCfg (some .read) v [] (true :: ps)) =
      some (treeSkipCfg (some .clear) (false, none) [] ps) := by
  simp [treeSkipStep, treeSkipCfg, treeSkipCode, TM2.step, TM2.stepAux,
    treeSkipStacks_input, treeSkipStacks_pending, treeSkipStacks]

def treeFieldLabel (second : Bool) : TreeSkipLabel := if second then .type else .block
def treeFieldNext (second : Bool) : TreeSkipLabel := if second then .read else .type

theorem treeSkip_field_true (second : Bool) (v : FrameControl) (bits ps : List Bool) :
    treeSkipStep (treeSkipCfg (some (treeFieldLabel second)) v (true :: bits) ps) =
      some (treeSkipCfg (some (treeFieldLabel second)) (false, some true) bits ps) := by
  cases second <;> simp [treeFieldLabel, treeSkipStep, treeSkipCfg, treeSkipCode,
    TM2.step, TM2.stepAux, treeSkipStacks_input, treeSkipStacks]

theorem treeSkip_field_false (second : Bool) (v : FrameControl) (bits ps : List Bool) :
    treeSkipStep (treeSkipCfg (some (treeFieldLabel second)) v (false :: bits) ps) =
      some (treeSkipCfg (some (treeFieldNext second)) (false, some false) bits ps) := by
  cases second <;> simp [treeFieldLabel, treeFieldNext, treeSkipStep, treeSkipCfg,
    treeSkipCode, TM2.step, TM2.stepAux, treeSkipStacks_input, treeSkipStacks]

theorem treeSkip_field_missing (second : Bool) (v : FrameControl) (ps : List Bool) :
    treeSkipStep (treeSkipCfg (some (treeFieldLabel second)) v [] ps) =
      some (treeSkipCfg (some .clear) (false, none) [] ps) := by
  cases second <;> simp [treeFieldLabel, treeSkipStep, treeSkipCfg, treeSkipCode,
    TM2.step, TM2.stepAux, treeSkipStacks_input, treeSkipStacks]

theorem treeSkip_clear_cons (v : FrameControl) (p : Bool) (ps : List Bool) :
    treeSkipStep (treeSkipCfg (some .clear) v [] (p :: ps)) =
      some (treeSkipCfg (some .clear) (false, some p) [] ps) := by
  simp [treeSkipStep, treeSkipCfg, treeSkipCode, TM2.step, TM2.stepAux,
    treeSkipStacks_pending, treeSkipStacks]

theorem treeSkip_clear_nil (v : FrameControl) :
    treeSkipStep (treeSkipCfg (some .clear) v [] []) = some (treeSkipEnd none) := by
  simp [treeSkipStep, treeSkipCfg, treeSkipCode, TM2.step, TM2.stepAux,
    treeSkipStacks_pending, treeSkipStacks, treeSkipEnd]

def treeSkipClearRun (ps : List Bool) (v : FrameControl) :
    EvalsToInTime treeSkipStep (treeSkipCfg (some .clear) v [] ps)
      (some (treeSkipEnd none)) (ps.length + 1) := by
  induction ps generalizing v with
  | nil => exact evalsOneStep _ _ _ (treeSkip_clear_nil v)
  | cons p ps ih =>
      simpa only [List.length_cons, Nat.add_assoc] using
        treeSkipPrepend (treeSkip_clear_cons v p ps) (ih (false, some p))

def treeSkipFieldRun (second : Bool) (a : ℕ) (rest ps : List Bool) (v : FrameControl) :
    EvalsToInTime treeSkipStep
      (treeSkipCfg (some (treeFieldLabel second)) v (unaryFrame a ++ rest) ps)
      (some (treeSkipCfg (some (treeFieldNext second)) (false, some false) rest ps))
      (a + 1) := by
  induction a generalizing v with
  | zero => simpa [unaryFrame] using evalsOneStep _ _ _ (treeSkip_field_false second v rest ps)
  | succ a ih =>
      simpa [unaryFrame, List.replicate_succ, Nat.add_assoc] using
        treeSkipPrepend (treeSkip_field_true second v (unaryFrame a ++ rest) ps)
          (ih (false, some true))

def treeSkipFieldMissingRun (second : Bool) (a q : ℕ) (v : FrameControl) :
    EvalsToInTime treeSkipStep
      (treeSkipCfg (some (treeFieldLabel second)) v
        (List.replicate a true) (List.replicate q true))
      (some (treeSkipEnd none)) (a + q + 2) := by
  induction a generalizing v with
  | zero =>
      simpa using treeSkipPrepend (treeSkip_field_missing second v (List.replicate q true))
        (treeSkipClearRun (List.replicate q true) (false, none))
  | succ a ih =>
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        treeSkipPrepend (treeSkip_field_true second v
          (List.replicate a true) (List.replicate q true)) (ih (false, some true))

def treeSkipReadMissingRun (q : ℕ) (v : FrameControl) :
    EvalsToInTime treeSkipStep
      (treeSkipCfg (some .read) v [] (List.replicate (q + 1) true))
      (some (treeSkipEnd none)) (q + 2) := by
  simpa [List.replicate_succ] using treeSkipPrepend
    (treeSkip_read_missing v (List.replicate q true))
    (treeSkipClearRun (List.replicate q true) (false, none))

/-- ALL input words and every physical pending count. Failure cleans the
    pending stack and exhausted input; success preserves the exact suffix.
    The supplied fuel only indexes the specification in this proof. -/
def treeSkipReadRun (fuel : ℕ) :
    ∀ (q : ℕ) (bits : List Bool) (v : FrameControl), bits.length ≤ fuel →
      EvalsToInTime treeSkipStep
        (treeSkipCfg (some .read) v bits (List.replicate q true))
        (some (treeSkipEnd (rawForestSkip fuel q bits))) (2 * bits.length + q + 2) := by
  induction fuel with
  | zero =>
      intro q bits v hlen
      have hb : bits = [] := List.length_eq_zero.mp (by omega)
      subst bits
      cases q with
      | zero =>
          exact treeSkipWeaken (evalsOneStep _ _ _ (treeSkip_read_done v [])) (by simp)
      | succ q =>
          exact treeSkipWeaken (treeSkipReadMissingRun q v) (by simp; omega)
  | succ fuel ih =>
      intro q bits v hlen
      cases q with
      | zero =>
          exact treeSkipWeaken (evalsOneStep _ _ _ (treeSkip_read_done v bits)) (by omega)
      | succ q =>
          cases bits with
          | nil =>
              exact treeSkipWeaken (treeSkipReadMissingRun q v) (by simp; omega)
          | cons b bits =>
              have hsmall : bits.length ≤ fuel := by simp only [List.length_cons] at hlen; omega
              cases b with
              | false =>
                  have hr := treeSkipPrepend
                    (treeSkip_read_internal v bits (List.replicate q true))
                    (by simpa only [List.replicate_succ] using
                      ih (q + 2) bits (false, some false) hsmall)
                  exact treeSkipWeaken
                    (by simpa only [List.replicate_succ, rawForestSkip] using hr)
                    (by simp only [List.length_cons]; omega)
              | true =>
                  cases hb : readUnaryFrame bits with
                  | none =>
                      have hf := treeSkipFieldMissingRun false bits.length q (false, some true)
                      rw [← readUnaryFrame_missing bits hb] at hf
                      have hr := treeSkipPrepend (treeSkip_read_leaf v bits (List.replicate q true)) hf
                      exact treeSkipWeaken
                        (by simpa [rawForestSkip, hb, List.replicate_succ, treeFieldLabel] using hr)
                        (by simp only [List.length_cons]; omega)
                  | some pb =>
                      rcases pb with ⟨a, afterBlock⟩
                      have hba := readUnaryFrame_consumption bits a afterBlock hb
                      have hfirst := treeSkipFieldRun false a afterBlock
                        (List.replicate q true) (false, some true)
                      rw [← readUnaryFrame_decomposition bits a afterBlock hb] at hfirst
                      cases ht : readUnaryFrame afterBlock with
                      | none =>
                          have hsecond := treeSkipFieldMissingRun true afterBlock.length q
                            (false, some false)
                          rw [← readUnaryFrame_missing afterBlock ht] at hsecond
                          have hr := treeSkipPrepend
                            (treeSkip_read_leaf v bits (List.replicate q true))
                            (treeSkipThen hfirst hsecond)
                          exact treeSkipWeaken
                            (by simpa [rawForestSkip, hb, ht, List.replicate_succ,
                              treeFieldLabel, treeFieldNext] using hr)
                            (by simp only [List.length_cons]; omega)
                      | some pt =>
                          rcases pt with ⟨b, afterType⟩
                          have htb := readUnaryFrame_consumption afterBlock b afterType ht
                          have hrest : afterType.length ≤ fuel := by omega
                          have hsecond := treeSkipFieldRun true b afterType
                            (List.replicate q true) (false, some false)
                          rw [← readUnaryFrame_decomposition afterBlock b afterType ht] at hsecond
                          have htail := ih q afterType (false, some false) hrest
                          have hr := treeSkipPrepend
                            (treeSkip_read_leaf v bits (List.replicate q true))
                            (treeSkipThen hfirst (treeSkipThen hsecond htail))
                          exact treeSkipWeaken
                            (by simpa [rawForestSkip, hb, ht, List.replicate_succ,
                              treeFieldLabel, treeFieldNext] using hr)
                            (by simp only [List.length_cons]; omega)

def treeSkipPrefixRun (bits : List Bool) (v : FrameControl) :
    EvalsToInTime treeSkipStep (treeSkipCfg (some .start) v bits [])
      (some (treeSkipEnd (rawForestSkip bits.length 1 bits))) (2 * bits.length + 4) := by
  simpa only [List.replicate_one, Nat.add_assoc] using
    treeSkipPrepend (treeSkip_start v bits)
      (treeSkipReadRun bits.length 1 bits (false, none) (le_refl _))

/- No typed-cell range, clade membership, score or complete verifier claim
   is made by this syntax machine. No alternate target promise is added. -/

end PolytomyReductionModel
