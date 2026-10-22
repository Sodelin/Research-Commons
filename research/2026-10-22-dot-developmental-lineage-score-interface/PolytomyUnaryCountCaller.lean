/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Concrete caller-safe unary LIST-COUNT reader for the ORIGINAL source
grammar. This is not the binary-payload frame reader: it stops at the
first false delimiter and returns a physical unary tally. All-input
failure cleanup and exact Option/suffix semantics are included.
-/
import PolytomySourceReaderCallBound

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def unaryCallerStacks (source output : K) (base : K → List Bool) (xs ys : List Bool) :
    ∀ j : K ⊕ Empty, List ((Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool)) j)
  | .inl k => Function.update (Function.update base source xs) output ys k
  | .inr e => nomatch e

theorem unaryCallerStacks_source (source output : K) (hne : source ≠ output)
    (base : K → List Bool) (xs ys zs : List Bool) :
    Function.update (unaryCallerStacks source output base xs ys) (.inl source) zs =
      unaryCallerStacks source output base zs ys := by
  funext j
  cases j with
  | inr e => nomatch e
  | inl k =>
      by_cases ho : k = output
      · subst k; simp [unaryCallerStacks, hne, Ne.symm hne]
      · by_cases hs : k = source
        · subst k; simp [unaryCallerStacks, hne]
        · simp [unaryCallerStacks, ho, hs]

theorem unaryCallerStacks_output (source output : K) (base : K → List Bool)
    (xs ys zs : List Bool) :
    Function.update (unaryCallerStacks source output base xs ys) (.inl output) zs =
      unaryCallerStacks source output base xs zs := by
  funext j
  cases j with
  | inr e => nomatch e
  | inl k => by_cases ho : k = output <;> simp [unaryCallerStacks, ho]

def unaryCountRoutine (source output : K) : Routine (fun _ : K => Bool) (F × Bool) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Bool
  entry := false
  code
    | false => .pop (.inl source) (fun v h => ((v.1.1, false), h))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2.getD false)
            (.push (.inl output) (fun _ => true) (.goto (fun _ => false)))
            (.load (fun v => ((v.1.1, true), none)) .halt))
          (.goto (fun _ => true)))
    | true => .pop (.inl output) (fun v h => ((v.1.1, false), h))
        (.branch (fun v => v.2.isSome) (.goto (fun _ => true))
          (.load (fun v => ((v.1.1, false), none)) .halt))

def unaryCallerCfg (source output : K) (l : Option Bool) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    TM2.Cfg (Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool))
      Bool ((F × Bool) × Option Bool) :=
  ⟨l, ((frame, flag), o), unaryCallerStacks source output base xs ys⟩

theorem unaryCaller_boundary (source output : K) (l : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    unaryCallerCfg source output l none base frame flag xs ys =
      (unaryCountRoutine source output).boundary l
        (frameCallerStore source output base frame flag xs ys) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext j; cases j with
    | inl k => rfl
    | inr e => nomatch e

theorem unary_prefix_true (source output : K) (hne : source ≠ output)
    (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    TM2.step (unaryCountRoutine source output).code
      (unaryCallerCfg source output (some false) o base frame flag (true :: xs) ys) =
      some (unaryCallerCfg source output (some false) (some true) base frame false xs (true :: ys)) := by
  simp [unaryCountRoutine, unaryCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_source, unaryCallerStacks_output, unaryCallerStacks, hne]
theorem unary_prefix_false (source output : K) (hne : source ≠ output)
    (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    TM2.step (unaryCountRoutine source output).code
      (unaryCallerCfg source output (some false) o base frame flag (false :: xs) ys) =
      some (unaryCallerCfg source output none none base frame true xs ys) := by
  simp [unaryCountRoutine, unaryCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_source, unaryCallerStacks, hne]
theorem unary_prefix_nil (source output : K) (hne : source ≠ output)
    (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool) (ys : List Bool) :
    TM2.step (unaryCountRoutine source output).code
      (unaryCallerCfg source output (some false) o base frame flag [] ys) =
      some (unaryCallerCfg source output (some true) none base frame false [] ys) := by
  simp [unaryCountRoutine, unaryCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_source, unaryCallerStacks, hne]
theorem unary_clear_cons (source output : K) (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag b : Bool) (xs ys : List Bool) :
    TM2.step (unaryCountRoutine source output).code
      (unaryCallerCfg source output (some true) o base frame flag xs (b :: ys)) =
      some (unaryCallerCfg source output (some true) (some b) base frame false xs ys) := by
  simp [unaryCountRoutine, unaryCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_output, unaryCallerStacks]
theorem unary_clear_nil (source output : K) (o : Option Bool) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs : List Bool) :
    TM2.step (unaryCountRoutine source output).code
      (unaryCallerCfg source output (some true) o base frame flag xs []) =
      some (unaryCallerCfg source output none none base frame false xs []) := by
  simp [unaryCountRoutine, unaryCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_output, unaryCallerStacks]

theorem unaryClearRun (source output : K) (ys : List Bool) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs : List Bool) :
    Runs (TM2.step (unaryCountRoutine source output).code)
      (unaryCallerCfg source output (some true) o base frame flag xs ys)
      (unaryCallerCfg source output none none base frame false xs []) (ys.length + 1) := by
  induction ys generalizing o flag with
  | nil => exact Runs.one (unary_clear_nil source output o base frame flag xs)
  | cons b ys ih => exact Runs.cons (unary_clear_cons source output o base frame flag b xs ys)
      (ih (some b) false)

theorem unarySuccessRun (source output : K) (hne : source ≠ output) (n : ℕ)
    (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool) (rest ys : List Bool) :
    Runs (TM2.step (unaryCountRoutine source output).code)
      (unaryCallerCfg source output (some false) o base frame flag (unaryFrame n ++ rest) ys)
      (unaryCallerCfg source output none none base frame true rest (List.replicate n true ++ ys))
      (n + 1) := by
  induction n generalizing o flag ys with
  | zero => simpa [unaryFrame] using Runs.one (unary_prefix_false source output hne o base frame flag rest ys)
  | succ n ih =>
      have r := Runs.cons
        (unary_prefix_true source output hne o base frame flag (unaryFrame n ++ rest) ys)
        (ih (some true) false (true :: ys))
      have hout : List.replicate n true ++ true :: ys = List.replicate (n + 1) true ++ ys := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [hout] at r
      simpa [unaryFrame, List.replicate_succ] using r

theorem unaryMissingRun (source output : K) (hne : source ≠ output) (n : ℕ)
    (o : Option Bool) (base : K → List Bool) (frame : F) (flag : Bool) (ys : List Bool) :
    Runs (TM2.step (unaryCountRoutine source output).code)
      (unaryCallerCfg source output (some false) o base frame flag (List.replicate n true) ys)
      (unaryCallerCfg source output none none base frame false [] [])
      (2 * n + ys.length + 2) := by
  induction n generalizing o flag ys with
  | zero =>
      have r := Runs.cons (unary_prefix_nil source output hne o base frame flag ys)
        (unaryClearRun source output ys none base frame false [])
      simpa [Nat.add_assoc] using r
  | succ n ih =>
      have r := Runs.cons
        (unary_prefix_true source output hne o base frame flag (List.replicate n true) ys)
        (ih (some true) false (true :: ys))
      convert r using 1 <;> simp [List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

def unaryCallerResult (source output : K) (base : K → List Bool) (frame : F) :
    Option (ℕ × List Bool) → Store (fun _ : K => Bool) (F × Bool)
  | none => frameCallerStore source output base frame false [] []
  | some (n, rest) => frameCallerStore source output base frame true rest (List.replicate n true)

theorem unaryCount_executes (source output : K) (hne : source ≠ output)
    (base : K → List Bool) (frame : F) (bits : List Bool) :
    ∃ n ≤ 2 * bits.length + 2,
      (unaryCountRoutine source output).Executes
        (frameCallerStore source output base frame false bits [])
        (unaryCallerResult source output base frame (readUnaryFrame bits)) n := by
  cases hp : readUnaryFrame bits with
  | none =>
      have he := readUnaryFrame_missing bits hp
      have r := unaryMissingRun source output hne bits.length none base frame false []
      simp only [List.length_nil, Nat.add_zero, ← he] at r
      rw [unaryCaller_boundary, unaryCaller_boundary] at r
      exact ⟨2 * bits.length + 2, le_refl _, by simpa only [hp, unaryCallerResult] using r.iterate⟩
  | some p =>
      rcases p with ⟨n, rest⟩
      have he := readUnaryFrame_decomposition bits n rest hp
      have hlen : bits.length = n + 1 + rest.length := by rw [he]; simp [unaryFrame, Nat.add_assoc]
      have r := unarySuccessRun source output hne n none base frame false rest []
      simp only [List.append_nil, ← he] at r
      rw [unaryCaller_boundary, unaryCaller_boundary] at r
      exact ⟨n + 1, by omega, by simpa only [hp, unaryCallerResult] using r.iterate⟩

def observeUnaryCaller (source output : K) (s : Store (fun _ : K => Bool) (F × Bool)) :
    Option (ℕ × List Bool) :=
  if s.state.2 then some ((s.stk output).length, s.stk source) else none

theorem unaryCaller_observe (source output : K) (hne : source ≠ output)
    (base : K → List Bool) (frame : F) (result : Option (ℕ × List Bool)) :
    observeUnaryCaller source output (unaryCallerResult source output base frame result) = result := by
  cases result with
  | none => rfl
  | some p =>
      rcases p with ⟨n, rest⟩
      simp [observeUnaryCaller, unaryCallerResult, frameCallerStore, hne]

theorem unaryCaller_preserves (source output k : K) (hs : k ≠ source) (ho : k ≠ output)
    (base : K → List Bool) (frame : F) (result : Option (ℕ × List Bool)) :
    (unaryCallerResult source output base frame result).state.1 = frame ∧
      (unaryCallerResult source output base frame result).stk k = base k := by
  cases result with
  | none => simp [unaryCallerResult, frameCallerStore, hs, ho]
  | some p => rcases p with ⟨n, rest⟩; simp [unaryCallerResult, frameCallerStore, hs, ho]

theorem full_reduction_with_unary_count_reader (input : List Bool) (lambda : ℝ)
    (source output : K) (hne : source ≠ output) (base : K → List Bool) (frame : F) :
    (rawRowConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔ EncodedTargetCartaDecision (rawRowConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (rawRowConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (rawRowConstructor input).length ∧
          boundedEncodedTarget (rawRowConstructor input) cert = true) ∧
      (countedSaturatedSource input).1 = parseSaturatedSource input ∧
      (countedSaturatedSource input).2 ≤ input.length + 1 ∧
      ∀ bits : List Bool, ∃ n ≤ 2 * bits.length + 2,
        (unaryCountRoutine source output).Executes
          (frameCallerStore source output base frame false bits [])
          (unaryCallerResult source output base frame (readUnaryFrame bits)) n := by
  have h := full_raw_row_constructor_interface input lambda
  exact ⟨h.1, h.2.1, h.2.2, countedSaturatedSource_erase input, countedSaturatedSource_calls input,
    unaryCount_executes source output hne base frame⟩

/- Both primitive reader types in the full source grammar now have actual
caller-level source proposals, but the nested loops/counter/output-storage
program and its full operational proof are still required. The charge in
countedSaturatedSource is NOT reinterpreted as a transition count. Finite
caller K/F, fresh empty output, port inequality, exact failure flags and
all cleanup remain explicit. No whole constructor/verifier, upstream
hardness or kernel closure is inferred. No execution or new model.
-/

end PolytomyReductionModel
