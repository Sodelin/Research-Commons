/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original-tree syntax walk with one physical Boolean mask bit per
consumed input bit: true at node tokens, false inside both unary fields.
The mask is accumulated reversed. Failure clears all three owned stacks.
-/
import PolytomyRawTreeNodeMask
import PolytomyRawTreePrefixMachine

namespace PolytomyReductionModel

open Turing StateTransition

inductive TreeMaskStack where
  | input | pending | mask
  deriving DecidableEq, Fintype

abbrev TreeMaskCfg := TM2.Cfg (fun _ : TreeMaskStack => Bool) TreeSkipLabel FrameControl

def treeMaskStacks (xs ps os : List Bool) : TreeMaskStack → List Bool
  | .input => xs
  | .pending => ps
  | .mask => os

theorem treeMaskStacks_input (xs ps os ys : List Bool) :
    Function.update (treeMaskStacks xs ps os) .input ys = treeMaskStacks ys ps os := by
  funext k; cases k <;> simp [treeMaskStacks]

theorem treeMaskStacks_pending (xs ps os qs : List Bool) :
    Function.update (treeMaskStacks xs ps os) .pending qs = treeMaskStacks xs qs os := by
  funext k; cases k <;> simp [treeMaskStacks]

theorem treeMaskStacks_mask (xs ps os rs : List Bool) :
    Function.update (treeMaskStacks xs ps os) .mask rs = treeMaskStacks xs ps rs := by
  funext k; cases k <;> simp [treeMaskStacks]

def treeMaskCfg (l : Option TreeSkipLabel) (v : FrameControl)
    (xs ps os : List Bool) : TreeMaskCfg := ⟨l, v, treeMaskStacks xs ps os⟩

def treeMaskCode : TreeSkipLabel →
    TM2.Stmt (fun _ : TreeMaskStack => Bool) TreeSkipLabel FrameControl
  | .start => .load (fun _ => (false, none))
      (.push .pending (fun _ => true) (.goto (fun _ => .read)))
  | .read =>
      .pop .pending (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.pop .input (fun _ h => (false, h))
            (.branch (fun v => v.2.isSome)
              (.push .mask (fun _ => true)
                (.branch (fun v => v.2.getD false)
                  (.goto (fun _ => .block))
                  (.push .pending (fun _ => true)
                    (.push .pending (fun _ => true) (.goto (fun _ => .read))))))
              (.goto (fun _ => .clear))))
          (.load (fun _ => (true, none)) .halt))
  | .block =>
      .pop .input (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.push .mask (fun _ => false)
            (.branch (fun v => v.2.getD false)
              (.goto (fun _ => .block)) (.goto (fun _ => .type))))
          (.goto (fun _ => .clear)))
  | .type =>
      .pop .input (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.push .mask (fun _ => false)
            (.branch (fun v => v.2.getD false)
              (.goto (fun _ => .type)) (.goto (fun _ => .read))))
          (.goto (fun _ => .clear)))
  | .clear =>
      .pop .pending (fun _ h => (false, h))
        (.branch (fun v => v.2.isSome)
          (.goto (fun _ => .clear))
          (.pop .mask (fun _ h => (false, h))
            (.branch (fun v => v.2.isSome)
              (.goto (fun _ => .clear)) (.load (fun _ => (false, none)) .halt))))

def treeMaskStep : TreeMaskCfg → Option TreeMaskCfg := TM2.step treeMaskCode

def treeMaskEnd (result : Option (List Bool × List Bool)) (os : List Bool) : TreeMaskCfg :=
  match result with
  | none => treeMaskCfg none (false, none) [] [] []
  | some (rest, mask) => treeMaskCfg none (true, none) rest [] (mask.reverse ++ os)

theorem treeMaskEnd_prefix («prefix» os : List Bool) (r : Option (List Bool × List Bool)) :
    treeMaskEnd (rawMaskPrefix «prefix» r) os = treeMaskEnd r (prefix.reverse ++ os) := by
  cases r with
  | none => rfl
  | some p => rcases p with ⟨rest, mask⟩; simp [rawMaskPrefix, treeMaskEnd, List.reverse_append, List.append_assoc]

theorem treeMaskLeafLog (a b : ℕ) (os : List Bool) :
    List.replicate (b + 1) false ++ (List.replicate (a + 1) false ++ true :: os) =
      (true :: List.replicate (a + b + 2) false).reverse ++ os := by
  have hc : (b + 1) + (a + 1) = a + b + 2 := by omega
  calc
    _ = List.replicate ((b + 1) + (a + 1)) false ++ true :: os := by
      rw [← List.append_assoc, List.replicate_append_replicate]
    _ = List.replicate (a + b + 2) false ++ true :: os := by rw [hc]
    _ = _ := by simp [List.reverse_cons, List.reverse_replicate, List.append_assoc]

def treeMaskPrepend {a b c : TreeMaskCfg} {n : ℕ}
    (h : treeMaskStep a = some b) (run : EvalsToInTime treeMaskStep b (some c) n) :
    EvalsToInTime treeMaskStep a (some c) (n + 1) :=
  EvalsToInTime.trans treeMaskStep 1 n a b (some c) (evalsOneStep _ _ _ h) run

def treeMaskThen {a b c : TreeMaskCfg} {m n : ℕ}
    (h : EvalsToInTime treeMaskStep a (some b) m)
    (run : EvalsToInTime treeMaskStep b (some c) n) :
    EvalsToInTime treeMaskStep a (some c) (m + n) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans treeMaskStep m n a b (some c) h run

def treeMaskWeaken {a b : TreeMaskCfg} {n m : ℕ}
    (run : EvalsToInTime treeMaskStep a (some b) n) (h : n ≤ m) :
    EvalsToInTime treeMaskStep a (some b) m :=
  { run with steps_le_m := run.steps_le_m.trans h }

theorem treeMask_start (v : FrameControl) (bits os : List Bool) :
    treeMaskStep (treeMaskCfg (some .start) v bits [] os) =
      some (treeMaskCfg (some .read) (false, none) bits [true] os) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_pending, treeMaskStacks]

theorem treeMask_read_done (v : FrameControl) (bits os : List Bool) :
    treeMaskStep (treeMaskCfg (some .read) v bits [] os) =
      some (treeMaskEnd (some (bits, [])) os) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_pending, treeMaskStacks, treeMaskEnd]

theorem treeMask_read_internal (v : FrameControl) (bits ps os : List Bool) :
    treeMaskStep (treeMaskCfg (some .read) v (false :: bits) (true :: ps) os) =
      some (treeMaskCfg (some .read) (false, some false) bits
        (true :: true :: ps) (true :: os)) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_input, treeMaskStacks_pending, treeMaskStacks_mask, treeMaskStacks]

theorem treeMask_read_leaf (v : FrameControl) (bits ps os : List Bool) :
    treeMaskStep (treeMaskCfg (some .read) v (true :: bits) (true :: ps) os) =
      some (treeMaskCfg (some .block) (false, some true) bits ps (true :: os)) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_input, treeMaskStacks_pending, treeMaskStacks_mask, treeMaskStacks]

theorem treeMask_read_missing (v : FrameControl) (ps os : List Bool) :
    treeMaskStep (treeMaskCfg (some .read) v [] (true :: ps) os) =
      some (treeMaskCfg (some .clear) (false, none) [] ps os) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_input, treeMaskStacks_pending, treeMaskStacks]

theorem treeMask_field_true (second : Bool) (v : FrameControl) (bits ps os : List Bool) :
    treeMaskStep (treeMaskCfg (some (treeFieldLabel second)) v (true :: bits) ps os) =
      some (treeMaskCfg (some (treeFieldLabel second)) (false, some true) bits ps (false :: os)) := by
  cases second <;> simp [treeFieldLabel, treeMaskStep, treeMaskCfg, treeMaskCode,
    TM2.step, TM2.stepAux, treeMaskStacks_input, treeMaskStacks_mask, treeMaskStacks]

theorem treeMask_field_false (second : Bool) (v : FrameControl) (bits ps os : List Bool) :
    treeMaskStep (treeMaskCfg (some (treeFieldLabel second)) v (false :: bits) ps os) =
      some (treeMaskCfg (some (treeFieldNext second)) (false, some false) bits ps (false :: os)) := by
  cases second <;> simp [treeFieldLabel, treeFieldNext, treeMaskStep, treeMaskCfg,
    treeMaskCode, TM2.step, TM2.stepAux, treeMaskStacks_input, treeMaskStacks_mask, treeMaskStacks]

theorem treeMask_field_missing (second : Bool) (v : FrameControl) (ps os : List Bool) :
    treeMaskStep (treeMaskCfg (some (treeFieldLabel second)) v [] ps os) =
      some (treeMaskCfg (some .clear) (false, none) [] ps os) := by
  cases second <;> simp [treeFieldLabel, treeMaskStep, treeMaskCfg, treeMaskCode,
    TM2.step, TM2.stepAux, treeMaskStacks_input, treeMaskStacks]

theorem treeMask_clear_pending (v : FrameControl) (p : Bool) (ps os : List Bool) :
    treeMaskStep (treeMaskCfg (some .clear) v [] (p :: ps) os) =
      some (treeMaskCfg (some .clear) (false, some p) [] ps os) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_pending, treeMaskStacks]

theorem treeMask_clear_mask (v : FrameControl) (b : Bool) (os : List Bool) :
    treeMaskStep (treeMaskCfg (some .clear) v [] [] (b :: os)) =
      some (treeMaskCfg (some .clear) (false, some b) [] [] os) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_pending, treeMaskStacks_mask, treeMaskStacks]

theorem treeMask_clear_done (v : FrameControl) :
    treeMaskStep (treeMaskCfg (some .clear) v [] [] []) = some (treeMaskEnd none []) := by
  simp [treeMaskStep, treeMaskCfg, treeMaskCode, TM2.step, TM2.stepAux,
    treeMaskStacks_pending, treeMaskStacks_mask, treeMaskStacks, treeMaskEnd]

def treeMaskClearRun (ps os : List Bool) (v : FrameControl) :
    EvalsToInTime treeMaskStep (treeMaskCfg (some .clear) v [] ps os)
      (some (treeMaskEnd none [])) (ps.length + os.length + 1) := by
  induction ps generalizing os v with
  | nil =>
      induction os generalizing v with
      | nil => exact evalsOneStep _ _ _ (treeMask_clear_done v)
      | cons b os ih =>
          simpa [Nat.add_assoc] using treeMaskPrepend
            (treeMask_clear_mask v b os) (ih (false, some b))
  | cons p ps ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using treeMaskPrepend
        (treeMask_clear_pending v p ps os) (ih os (false, some p))

def treeMaskFieldRun (second : Bool) (a : ℕ) (rest ps os : List Bool) (v : FrameControl) :
    EvalsToInTime treeMaskStep
      (treeMaskCfg (some (treeFieldLabel second)) v (unaryFrame a ++ rest) ps os)
      (some (treeMaskCfg (some (treeFieldNext second)) (false, some false) rest ps
        (List.replicate (a + 1) false ++ os))) (a + 1) := by
  induction a generalizing os v with
  | zero =>
      simpa [unaryFrame] using evalsOneStep _ _ _ (treeMask_field_false second v rest ps os)
  | succ a ih =>
      have hr := treeMaskPrepend
        (treeMask_field_true second v (unaryFrame a ++ rest) ps os)
        (ih (false :: os) (false, some true))
      have ho : List.replicate (a + 1) false ++ false :: os =
          List.replicate (a + 1 + 1) false ++ os := by
        rw [show List.replicate (a + 1 + 1) false =
          List.replicate (a + 1) false ++ [false] from List.replicate_succ', List.append_assoc]
        rfl
      rw [ho] at hr
      simpa [unaryFrame, List.replicate_succ, Nat.add_assoc] using hr

def treeMaskFieldMissingRun (second : Bool) (a q : ℕ) (os : List Bool) (v : FrameControl) :
    EvalsToInTime treeMaskStep
      (treeMaskCfg (some (treeFieldLabel second)) v
        (List.replicate a true) (List.replicate q true) os)
      (some (treeMaskEnd none [])) (2 * a + q + os.length + 2) := by
  induction a generalizing os v with
  | zero =>
      simpa [Nat.add_assoc] using treeMaskPrepend
        (treeMask_field_missing second v (List.replicate q true) os)
        (treeMaskClearRun (List.replicate q true) os (false, none))
  | succ a ih =>
      have hr := treeMaskPrepend
        (treeMask_field_true second v (List.replicate a true) (List.replicate q true) os)
        (ih (false :: os) (false, some true))
      convert hr using 1 <;> simp only [List.replicate_succ, List.length_cons] <;> omega

def treeMaskReadMissingRun (q : ℕ) (os : List Bool) (v : FrameControl) :
    EvalsToInTime treeMaskStep
      (treeMaskCfg (some .read) v [] (List.replicate (q + 1) true) os)
      (some (treeMaskEnd none [])) (q + os.length + 2) := by
  simpa [List.replicate_succ, Nat.add_assoc] using treeMaskPrepend
    (treeMask_read_missing v (List.replicate q true) os)
    (treeMaskClearRun (List.replicate q true) os (false, none))

/-- ALL input words and arbitrary physical pending/mask accumulators.
    Failure cleanup includes the entire supplied accumulator length. -/
def treeMaskReadRun (fuel : ℕ) :
    ∀ (q : ℕ) (bits os : List Bool) (v : FrameControl), bits.length ≤ fuel →
      EvalsToInTime treeMaskStep
        (treeMaskCfg (some .read) v bits (List.replicate q true) os)
        (some (treeMaskEnd (rawForestMaskParse fuel q bits) os))
        (3 * bits.length + q + os.length + 3) := by
  induction fuel with
  | zero =>
      intro q bits os v hlen
      have hb : bits = [] := List.length_eq_zero.mp (by omega)
      subst bits
      cases q with
      | zero => exact treeMaskWeaken (evalsOneStep _ _ _ (treeMask_read_done v [] os)) (by simp)
      | succ q => exact treeMaskWeaken (treeMaskReadMissingRun q os v) (by simp; omega)
  | succ fuel ih =>
      intro q bits os v hlen
      cases q with
      | zero => exact treeMaskWeaken (evalsOneStep _ _ _ (treeMask_read_done v bits os)) (by omega)
      | succ q =>
          cases bits with
          | nil => exact treeMaskWeaken (treeMaskReadMissingRun q os v) (by simp; omega)
          | cons b bits =>
              have hsmall : bits.length ≤ fuel := by simp only [List.length_cons] at hlen; omega
              cases b with
              | false =>
                  have hr := treeMaskPrepend
                    (treeMask_read_internal v bits (List.replicate q true) os)
                    (by simpa only [List.replicate_succ] using
                      ih (q + 2) bits (true :: os) (false, some false) hsmall)
                  exact treeMaskWeaken
                    (by simpa [rawForestMaskParse, treeMaskEnd_prefix, List.replicate_succ] using hr)
                    (by simp only [List.length_cons]; omega)
              | true =>
                  cases hb : readUnaryFrame bits with
                  | none =>
                      have hf := treeMaskFieldMissingRun false bits.length q (true :: os) (false, some true)
                      rw [← readUnaryFrame_missing bits hb] at hf
                      have hr := treeMaskPrepend
                        (treeMask_read_leaf v bits (List.replicate q true) os) hf
                      exact treeMaskWeaken
                        (by simpa [rawForestMaskParse, hb, treeMaskEnd, List.replicate_succ,
                          treeFieldLabel] using hr)
                        (by simp only [List.length_cons]; omega)
                  | some pb =>
                      rcases pb with ⟨a, afterBlock⟩
                      have hba := readUnaryFrame_consumption bits a afterBlock hb
                      have hfirst := treeMaskFieldRun false a afterBlock
                        (List.replicate q true) (true :: os) (false, some true)
                      rw [← readUnaryFrame_decomposition bits a afterBlock hb] at hfirst
                      cases ht : readUnaryFrame afterBlock with
                      | none =>
                          have hsecond := treeMaskFieldMissingRun true afterBlock.length q
                            (List.replicate (a + 1) false ++ true :: os) (false, some false)
                          rw [← readUnaryFrame_missing afterBlock ht] at hsecond
                          have hr := treeMaskPrepend
                            (treeMask_read_leaf v bits (List.replicate q true) os)
                            (treeMaskThen hfirst hsecond)
                          exact treeMaskWeaken
                            (by simpa [rawForestMaskParse, hb, ht, treeMaskEnd,
                              List.replicate_succ, treeFieldLabel, treeFieldNext] using hr)
                            (by simp only [List.length_cons, List.length_append, List.length_replicate]; omega)
                      | some pt =>
                          rcases pt with ⟨b, afterType⟩
                          have htb := readUnaryFrame_consumption afterBlock b afterType ht
                          have hrest : afterType.length ≤ fuel := by omega
                          let os' := List.replicate (a + 1) false ++ true :: os
                          let os'' := List.replicate (b + 1) false ++ os'
                          have hsecond := treeMaskFieldRun true b afterType
                            (List.replicate q true) os' (false, some false)
                          rw [← readUnaryFrame_decomposition afterBlock b afterType ht] at hsecond
                          have htail := ih q afterType os'' (false, some false) hrest
                          have hr := treeMaskPrepend
                            (treeMask_read_leaf v bits (List.replicate q true) os)
                            (treeMaskThen hfirst (treeMaskThen hsecond htail))
                          have he : treeMaskEnd (rawForestMaskParse fuel q afterType) os'' =
                              treeMaskEnd (rawMaskPrefix (true :: List.replicate (a + b + 2) false)
                                (rawForestMaskParse fuel q afterType)) os := by
                            rw [treeMaskEnd_prefix]
                            unfold os'' os'
                            rw [treeMaskLeafLog]
                          rw [he] at hr
                          exact treeMaskWeaken
                            (by simpa [rawForestMaskParse, hb, ht, List.replicate_succ,
                              treeFieldLabel, treeFieldNext] using hr)
                            (by simp only [os'', os', List.length_cons, List.length_append,
                              List.length_replicate]; omega)

def treeMaskPrefixRun (bits : List Bool) (v : FrameControl) :
    EvalsToInTime treeMaskStep (treeMaskCfg (some .start) v bits [] [])
      (some (treeMaskEnd (rawForestMaskParse bits.length 1 bits) [])) (3 * bits.length + 5) := by
  simpa only [List.replicate_one, List.length_nil, Nat.add_zero, Nat.add_assoc] using
    treeMaskPrepend (treeMask_start v bits [])
      (treeMaskReadRun bits.length 1 bits [] (false, none) (le_refl _))

/- The mask is physically constructed, but exact forward-order restoration,
   caller integration and complete range/clade/score checker remain next.
   This machine alone does not inhabit VerifierMachineWitness. -/

end PolytomyReductionModel
