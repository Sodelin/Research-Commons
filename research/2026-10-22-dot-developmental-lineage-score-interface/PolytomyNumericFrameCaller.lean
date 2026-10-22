/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual caller-safe composition for the ORIGINAL capped numeric frame:
raw framing, restoring unary-cap copy, then the concrete bounded decoder.
The caller flag, suffix, original cap and every outside stack/control frame
are preserved. Uses the already inspected licensed proof-side Lax218471
embedding/composition pin, not concept-side theorem axioms. Not installed.
-/
import PolytomySaturatingDecoderMachine
import PolytomyFrameCallerAdapter

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

inductive NumericPort where
  | source | payload | cap | work | output
  deriving DecidableEq, Fintype

abbrev NumericStack (K : Type) := NumericPort ⊕ K

variable {K F : Type} [DecidableEq K]

def numericStacks (base : K → List Bool) (xs ps cs ws os : List Bool) : NumericStack K → List Bool
  | .inl .source => xs
  | .inl .payload => ps
  | .inl .cap => cs
  | .inl .work => ws
  | .inl .output => os
  | .inr k => base k

def numericStore (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps cs ws os : List Bool) : Store (fun _ : NumericStack K => Bool) (F × Bool) :=
  ⟨(frame, flag), numericStacks base xs ps cs ws os⟩

/-! ## Concrete restoring unary-cap copier -/

def capCopyStacks (base : K → List Bool) (xs ps cs ws os rs : List Bool) :
    ∀ j : NumericStack K ⊕ Unit,
      List ((Sum.elim (fun _ : NumericStack K => Bool) (fun _ : Unit => Bool)) j)
  | .inl k => numericStacks base xs ps cs ws os k
  | .inr _ => rs

theorem capCopyStacks_cap (base : K → List Bool) (xs ps cs ws os rs ds : List Bool) :
    Function.update (capCopyStacks base xs ps cs ws os rs) (.inl (.inl .cap)) ds =
      capCopyStacks base xs ps ds ws os rs := by
  funext j
  cases j with
  | inl k => cases k with
    | inl p => cases p <;> simp [capCopyStacks, numericStacks]
    | inr k => simp [capCopyStacks, numericStacks]
  | inr u => cases u; simp [capCopyStacks]
theorem capCopyStacks_work (base : K → List Bool) (xs ps cs ws os rs ds : List Bool) :
    Function.update (capCopyStacks base xs ps cs ws os rs) (.inl (.inl .work)) ds =
      capCopyStacks base xs ps cs ds os rs := by
  funext j
  cases j with
  | inl k => cases k with
    | inl p => cases p <;> simp [capCopyStacks, numericStacks]
    | inr k => simp [capCopyStacks, numericStacks]
  | inr u => cases u; simp [capCopyStacks]
theorem capCopyStacks_restore (base : K → List Bool) (xs ps cs ws os rs ds : List Bool) :
    Function.update (capCopyStacks base xs ps cs ws os rs) (.inr ()) ds =
      capCopyStacks base xs ps cs ws os ds := by
  funext j
  cases j with
  | inl k => simp [capCopyStacks]
  | inr u => cases u; simp [capCopyStacks]

def capCopyRoutine : Routine (fun _ : NumericStack K => Bool) (F × Bool) where
  W := Unit
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Bool
  entry := false
  code
    | false => .pop (.inl (.inl .cap)) (fun v h => (v.1, h))
        (.branch (fun v => v.2.isSome)
          (.push (.inl (.inl .work)) (fun _ => true)
            (.push (.inr ()) (fun _ => true) (.goto (fun _ => false))))
          (.goto (fun _ => true)))
    | true => .pop (.inr ()) (fun v h => (v.1, h))
        (.branch (fun v => v.2.isSome)
          (.push (.inl (.inl .cap)) (fun _ => true) (.goto (fun _ => true)))
          (.load (fun v => (v.1, none)) .halt))

def capCopyCfg (l : Option Bool) (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ps cs ws os rs : List Bool) :
    TM2.Cfg (Sum.elim (fun _ : NumericStack K => Bool) (fun _ : Unit => Bool))
      Bool ((F × Bool) × Option Bool) :=
  ⟨l, ((frame, flag), o), capCopyStacks base xs ps cs ws os rs⟩

theorem capCopy_boundary (l : Option Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ps cs ws os : List Bool) :
    capCopyCfg l none base frame flag xs ps cs ws os [] =
      (capCopyRoutine (K := K) (F := F)).boundary l (numericStore base frame flag xs ps cs ws os) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext j; cases j <;> rfl

theorem capCopy_copy_nil (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps ws os rs : List Bool) :
    TM2.step (capCopyRoutine (K := K) (F := F)).code
      (capCopyCfg (some false) o base frame flag xs ps [] ws os rs) =
      some (capCopyCfg (some true) none base frame flag xs ps [] ws os rs) := by
  simp [capCopyRoutine, capCopyCfg, TM2.step, TM2.stepAux,
    capCopyStacks_cap, capCopyStacks, numericStacks]
theorem capCopy_copy_cons (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps cs ws os rs : List Bool) :
    TM2.step (capCopyRoutine (K := K) (F := F)).code
      (capCopyCfg (some false) o base frame flag xs ps (true :: cs) ws os rs) =
      some (capCopyCfg (some false) (some true) base frame flag xs ps cs
        (true :: ws) os (true :: rs)) := by
  simp [capCopyRoutine, capCopyCfg, TM2.step, TM2.stepAux,
    capCopyStacks_cap, capCopyStacks_work, capCopyStacks_restore, capCopyStacks, numericStacks]
theorem capCopy_restore_nil (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps cs ws os : List Bool) :
    TM2.step (capCopyRoutine (K := K) (F := F)).code
      (capCopyCfg (some true) o base frame flag xs ps cs ws os []) =
      some (capCopyCfg none none base frame flag xs ps cs ws os []) := by
  simp [capCopyRoutine, capCopyCfg, TM2.step, TM2.stepAux,
    capCopyStacks_restore, capCopyStacks]
theorem capCopy_restore_cons (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps cs ws os rs : List Bool) :
    TM2.step (capCopyRoutine (K := K) (F := F)).code
      (capCopyCfg (some true) o base frame flag xs ps cs ws os (true :: rs)) =
      some (capCopyCfg (some true) (some true) base frame flag xs ps (true :: cs) ws os rs) := by
  simp [capCopyRoutine, capCopyCfg, TM2.step, TM2.stepAux,
    capCopyStacks_restore, capCopyStacks_cap, capCopyStacks, numericStacks]

theorem capCopyRestoreRun (u c : ℕ) (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ps ws os : List Bool) :
    Runs (TM2.step (capCopyRoutine (K := K) (F := F)).code)
      (capCopyCfg (some true) o base frame flag xs ps (List.replicate c true) ws os (List.replicate u true))
      (capCopyCfg none none base frame flag xs ps (List.replicate (c + u) true) ws os []) (u + 1) := by
  induction u generalizing c o with
  | zero => simpa using Runs.one (capCopy_restore_nil o base frame flag xs ps (List.replicate c true) ws os)
  | succ u ih =>
      have r := Runs.cons
        (capCopy_restore_cons o base frame flag xs ps (List.replicate c true) ws os (List.replicate u true))
        (by simpa only [List.replicate_succ] using ih (c + 1) (some true))
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem capCopyRun (c u w : ℕ) (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ps os : List Bool) :
    Runs (TM2.step (capCopyRoutine (K := K) (F := F)).code)
      (capCopyCfg (some false) o base frame flag xs ps (List.replicate c true)
        (List.replicate w true) os (List.replicate u true))
      (capCopyCfg none none base frame flag xs ps (List.replicate (c + u) true)
        (List.replicate (w + c) true) os []) (2 * c + u + 2) := by
  induction c generalizing u w o with
  | zero =>
      have r := Runs.cons (capCopy_copy_nil o base frame flag xs ps (List.replicate w true) os
        (List.replicate u true)) (capCopyRestoreRun u 0 none base frame flag xs ps (List.replicate w true) os)
      simpa [Nat.add_assoc] using r
  | succ c ih =>
      have r := Runs.cons
        (capCopy_copy_cons o base frame flag xs ps (List.replicate c true)
          (List.replicate w true) os (List.replicate u true))
        (by simpa only [List.replicate_succ] using ih (u + 1) (w + 1) (some true))
      convert r using 1 <;> simp [List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.mul_add]

theorem capCopy_executes (C : ℕ) (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps os : List Bool) :
    (capCopyRoutine (K := K) (F := F)).Executes
      (numericStore base frame flag xs ps (List.replicate C true) [] os)
      (numericStore base frame flag xs ps (List.replicate C true) (List.replicate C true) os)
      (2 * C + 2) := by
  have r := capCopyRun C 0 0 none base frame flag xs ps os
  simp only [Nat.add_zero, Nat.zero_add, List.replicate_zero] at r
  rw [capCopy_boundary, capCopy_boundary] at r
  exact r.iterate

/-! ## Actual decoder core as a caller-preserving routine -/

def numericDecoderPorts : SaturatingStack ↪ (NumericStack K ⊕ Bool) where
  toFun
    | .payload => .inl (.inl .payload)
    | .cap => .inl (.inl .work)
    | .count => .inl (.inl .output)
    | .temp => .inr false
    | .restore => .inr true
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def numericDecoderEmbedding :
    Embedding (fun _ : SaturatingStack => Bool)
      (Sum.elim (fun _ : NumericStack K => Bool) (fun _ : Bool => Bool))
      FrameControl ((F × Bool) × FrameControl) (F × Bool) where
  stack := numericDecoderPorts
  symbol k := by cases k <;> exact Equiv.refl Bool
  state := Equiv.prodComm _ _

def numericDecoderRoutine : Routine (fun _ : NumericStack K => Bool) (F × Bool) where
  W := Bool
  Δ _ := Bool
  τ := FrameControl
  initial := (false, none)
  Label := SaturatingLabel
  entry := .read
  code l := (numericDecoderEmbedding (K := K) (F := F)).stmt id none (saturatingCode l)

def numericDecoderBase (base : K → List Bool) (xs cs : List Bool) :
    ∀ j : NumericStack K ⊕ Bool,
      List ((Sum.elim (fun _ : NumericStack K => Bool) (fun _ : Bool => Bool)) j)
  | .inl k => numericStacks base xs [] cs [] [] k
  | .inr _ => []

theorem numericDecoder_boundary (l : Option SaturatingLabel)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ps cs ws os : List Bool) :
    (numericDecoderEmbedding (K := K) (F := F)).cfg id none (frame, flag)
      (numericDecoderBase base xs cs) (saturatingCfg l (false, none) ps ws os [] []) =
    (numericDecoderRoutine (K := K) (F := F)).boundary l
      (numericStore base frame flag xs ps cs ws os) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  apply Embedding.liftStacks_eq
  · intro k
    cases k <;> simp [Routine.boundary, numericDecoderRoutine, numericDecoderEmbedding,
      numericDecoderPorts, numericStore, numericStacks, saturatingCfg, saturatingStacks]
  · intro j hj
    cases j with
    | inl k =>
        cases k with
        | inl p =>
            cases p with
            | source => rfl
            | cap => rfl
            | payload => exact False.elim (hj .payload rfl)
            | work => exact False.elim (hj .cap rfl)
            | output => exact False.elim (hj .count rfl)
        | inr k => rfl
    | inr b => cases b with
      | false => exact False.elim (hj .temp rfl)
      | true => exact False.elim (hj .restore rfl)

theorem numericDecoder_executes (C : ℕ) (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps cs : List Bool) :
    ∃ n ≤ ps.length * (6 * C + 6) + C + 2,
      (numericDecoderRoutine (K := K) (F := F)).Executes
        (numericStore base frame flag xs ps cs (List.replicate C true) [])
        (numericStore base frame flag xs [] cs [] (List.replicate (cappedMSBFold C 0 ps) true)) n := by
  let h := saturatingChain (saturatingReadRun C 0 (Nat.zero_le _) ps (false, none))
    (saturatingClearRun C (List.replicate (cappedMSBFold C 0 ps) true) (false, none))
  have run : Runs (TM2.step saturatingCode)
      (saturatingCfg (some .read) (false, none) ps (List.replicate C true) [] [] [])
      (saturatingHalt (List.replicate (cappedMSBFold C 0 ps) true)) h.steps :=
    Runs.of_iterate h.evals_in_steps
  have lifted := (numericDecoderEmbedding (K := K) (F := F)).runs id none (frame, flag)
    (numericDecoderBase base xs cs) saturatingCode (numericDecoderRoutine (K := K) (F := F)).code
    (fun _ => rfl) run
  simp only [saturatingHalt] at lifted
  rw [numericDecoder_boundary, numericDecoder_boundary] at lifted
  exact ⟨h.steps, by have hb := h.steps_le_m; omega, lifted.iterate⟩

/-! ## Full raw-frame/copy/decoder composition -/

theorem numericFrame_store (base : K → List Bool) (frame : F) (flag : Bool)
    (xs ps cs : List Bool) :
    frameCallerStore (.inl .source : NumericStack K) (.inl .payload)
      (numericStacks base [] [] cs [] []) frame flag xs ps =
      numericStore base frame flag xs ps cs [] [] := by
  unfold frameCallerStore numericStore
  congr 1
  funext k
  cases k with
  | inl p => cases p <;> simp [numericStacks]
  | inr k => simp [numericStacks]

def numericRawResult (base : K → List Bool) (frame : F) (cs : List Bool) :
    Option (List Bool × List Bool) → Store (fun _ : NumericStack K => Bool) (F × Bool)
  | none => numericStore base frame false [] [] cs [] []
  | some (word, rest) => numericStore base frame true rest word.reverse cs [] []

theorem numericFrame_raw_result (base : K → List Bool) (frame : F) (cs : List Bool)
    (result : Option (List Bool × List Bool)) :
    frameCallerResult (.inl .source : NumericStack K) (.inl .payload)
      (numericStacks base [] [] cs [] []) frame result = numericRawResult base frame cs result := by
  cases result with
  | none => exact numericFrame_store base frame false [] [] cs
  | some p => rcases p with ⟨word, rest⟩; exact numericFrame_store base frame true rest word.reverse cs

/-- The code is independent of C. C is carried by the public cap stack;
    the copy and decoder private control/workspaces are clean at boundaries. -/
def numericFrameRoutine : Routine (fun _ : NumericStack K => Bool) (F × Bool) :=
  RoutineComposition.seq
    (frameCallerRoutine (.inl .source : NumericStack K) (.inl .payload) (by simp))
    (RoutineComposition.seq capCopyRoutine numericDecoderRoutine)

def numericFrameResult (base : K → List Bool) (frame : F) (C : ℕ) :
    Option (List Bool × List Bool) → Store (fun _ : NumericStack K => Bool) (F × Bool)
  | none => numericStore base frame false [] [] (List.replicate C true) [] []
  | some (word, rest) => numericStore base frame true rest [] (List.replicate C true) []
      (List.replicate (saturatedBinaryValue C word) true)

def numericFrameStepBound (L C : ℕ) : ℕ := 6 * L * C + 8 * L + 3 * C + 8

theorem numericFrame_executes (C : ℕ) (bits : List Bool) (base : K → List Bool) (frame : F) :
    ∃ n ≤ numericFrameStepBound bits.length C,
      (numericFrameRoutine (K := K) (F := F)).Executes
        (numericStore base frame false bits [] (List.replicate C true) [] [])
        (numericFrameResult base frame C (readRawBinaryFrame bits)) n := by
  obtain ⟨nf, hnf, hf⟩ := frameCaller_executes
    (.inl .source : NumericStack K) (.inl .payload) (by simp)
    (numericStacks base [] [] (List.replicate C true) [] []) frame bits
  rw [numericFrame_store, numericFrame_raw_result] at hf
  cases hp : readRawBinaryFrame bits with
  | none =>
      have hc := capCopy_executes C base frame false [] [] []
      obtain ⟨nd, hnd, hd⟩ := numericDecoder_executes C base frame false [] [] (List.replicate C true)
      have hcd := RoutineComposition.seq_executes capCopyRoutine numericDecoderRoutine hc hd
      have hfull := RoutineComposition.seq_executes
        (frameCallerRoutine (.inl .source : NumericStack K) (.inl .payload) (by simp))
        (RoutineComposition.seq capCopyRoutine numericDecoderRoutine)
        (by simpa only [hp, numericRawResult] using hf) hcd
      refine ⟨nf + (2 * C + 2 + nd), ?_, ?_⟩
      · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hnd
        unfold numericFrameStepBound
        nlinarith
      · simpa only [numericFrameRoutine, hp, numericFrameResult, cappedMSBFold,
          List.replicate_zero] using hfull
  | some p =>
      rcases p with ⟨word, rest⟩
      have hw := readRawBinaryFrame_payload_bound bits word rest hp
      have hc := capCopy_executes C base frame true rest word.reverse []
      obtain ⟨nd, hnd, hd⟩ := numericDecoder_executes C base frame true rest word.reverse
        (List.replicate C true)
      have hcd := RoutineComposition.seq_executes capCopyRoutine numericDecoderRoutine hc hd
      have hfull := RoutineComposition.seq_executes
        (frameCallerRoutine (.inl .source : NumericStack K) (.inl .payload) (by simp))
        (RoutineComposition.seq capCopyRoutine numericDecoderRoutine)
        (by simpa only [hp, numericRawResult] using hf) hcd
      refine ⟨nf + (2 * C + 2 + nd), ?_, ?_⟩
      · simp only [List.length_reverse] at hnd
        have hprod := Nat.mul_le_mul_right (6 * C + 6) hw
        unfold numericFrameStepBound
        nlinarith
      · simpa only [numericFrameRoutine, hp, numericFrameResult, cappedMSBFold_reverse] using hfull

def observeNumericFrame (s : Store (fun _ : NumericStack K => Bool) (F × Bool)) :
    Option (ℕ × List Bool) :=
  if s.state.2 then some ((s.stk (.inl .output)).length, s.stk (.inl .source)) else none

theorem numericFrame_observe (C : ℕ) (bits : List Bool) (base : K → List Bool) (frame : F) :
    observeNumericFrame (numericFrameResult base frame C (readRawBinaryFrame bits)) =
      readSaturatedBinaryNatFrame C bits := by
  rw [← readSaturatedViaPrimitive_eq]
  unfold readSaturatedViaPrimitive
  cases hp : readRawBinaryFrame bits with
  | none => rfl
  | some p =>
      rcases p with ⟨word, rest⟩
      simp [observeNumericFrame, numericFrameResult, numericStore, numericStacks,
        cappedUnaryWord_original_payload]

theorem numericFrame_preserves (C : ℕ) (base : K → List Bool) (frame : F)
    (result : Option (List Bool × List Bool)) :
    (numericFrameResult base frame C result).state.1 = frame ∧
      (numericFrameResult base frame C result).stk (.inl .cap) = List.replicate C true ∧
      (numericFrameResult base frame C result).stk (.inl .payload) = [] ∧
      (numericFrameResult base frame C result).stk (.inl .work) = [] ∧
      ∀ k, (numericFrameResult base frame C result).stk (.inr k) = base k := by
  cases result with
  | none => exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | some p => rcases p with ⟨word, rest⟩; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem numericFrame_output_bound (C : ℕ) (base : K → List Bool) (frame : F)
    (result : Option (List Bool × List Bool)) :
    ((numericFrameResult base frame C result).stk (.inl .output)).length ≤ C := by
  cases result with
  | none => exact Nat.zero_le _
  | some p =>
      rcases p with ⟨word, rest⟩
      simpa only [numericFrameResult, numericStore, numericStacks, List.length_replicate] using
        saturatedBinaryValue_le C word

/-- C is a physical unary operand. For the previously justified polynomial
    caps C<=(L+1)^2, this particular complete frame routine is polynomial
    in the ORIGINAL input L as well. This is not a new small-header promise. -/
theorem numericFrame_bound_for_source_caps (L C : ℕ) (hC : C ≤ (L + 1) ^ 2) :
    numericFrameStepBound L C ≤ 6 * L * (L + 1) ^ 2 + 8 * L + 3 * (L + 1) ^ 2 + 8 := by
  have hmul := Nat.mul_le_mul_left (6 * L) hC
  unfold numericFrameStepBound
  nlinarith

/-- Nested calls may have a shorter remaining frame tape while their cap
    is still chosen from the ORIGINAL outer input length. No shrinking-cap
    assumption is made. -/
theorem numericFrame_bound_under_outer_length (outer inner C : ℕ)
    (hi : inner ≤ outer) (hC : C ≤ (outer + 1) ^ 2) :
    numericFrameStepBound inner C ≤
      6 * outer * (outer + 1) ^ 2 + 8 * outer + 3 * (outer + 1) ^ 2 + 8 := by
  have hprod := Nat.mul_le_mul hi hC
  unfold numericFrameStepBound
  nlinarith

theorem full_reduction_with_numeric_frame (input : List Bool) (lambda : ℝ)
    (base : K → List Bool) (frame : F) :
    (rawRowConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔ EncodedTargetCartaDecision (rawRowConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (rawRowConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (rawRowConstructor input).length ∧
          boundedEncodedTarget (rawRowConstructor input) cert = true) ∧
      ∀ (C : ℕ) (bits : List Bool), ∃ n ≤ numericFrameStepBound bits.length C,
        (numericFrameRoutine (K := K) (F := F)).Executes
          (numericStore base frame false bits [] (List.replicate C true) [] [])
          (numericFrameResult base frame C (readRawBinaryFrame bits)) n ∧
        observeNumericFrame (numericFrameResult base frame C (readRawBinaryFrame bits)) =
          readSaturatedBinaryNatFrame C bits := by
  have h := full_raw_row_constructor_interface input lambda
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  intro C bits
  obtain ⟨n, hn, he⟩ := numericFrame_executes C bits base frame
  exact ⟨n, hn, he, numericFrame_observe C bits base frame⟩

/- All routine code, control/workspace and operational composition terms
are supplied as source. A full finite caller must have finite K and F;
its code then has finite labels/control and Boolean stack alphabets. The
routine has five named disjoint ports and initially empty payload/work/
output buffers. It does not promise preservation of occupied buffers.

This completes only the original capped numeric-frame subroutine at the
hand/source-proposal level. Nested source/target parsers, validators,
row/arithmetic/output assembly and the independent clade checker, total
whole-program bounds, compatible closed encoded hardness and every kernel
check remain open. The external licensed dependency is not installed; no
concept theorem axiom, runtime, new model or closure claim is introduced.
-/

end PolytomyReductionModel
