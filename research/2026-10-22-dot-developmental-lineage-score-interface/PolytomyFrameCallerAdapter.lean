/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No package installed or executed.

Caller-preserving realization of the actual all-input frame transducer.
Uses Szymon Toruńczyk and GPT's Apache-2.0 proof-side embedding/composition,
commit 7fadbfd005b359a66ccc1165b2d1becddb2906b8. See the pinned compiler audit.
The external dependency is not present in this project's build manifest.
No concept-side theorem axiom is invoked. All compatibility/kernel checks
and complete constructor/verifier integration remain open.
-/
import PolytomyBinaryFrameMachine
import Lax218471Proofs.RoutineComposition
import Lax218471Proofs.Transfer

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

/-- The source and reverse-payload ports must be DISTINCT. The tally is
    private, not an alias for an arbitrary existing caller stack. -/
def framePortInjection (source payload : K) (hne : source ≠ payload) :
    FrameStack ↪ (K ⊕ Unit) where
  toFun
    | .input => .inl source
    | .count => .inr ()
    | .payload => .inl payload
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

/-- Arbitrary caller data F is preserved. For a COMPLETE finite machine,
    that caller control must separately have a Fintype instance. -/
def frameCallerEmbedding (source payload : K) (hne : source ≠ payload) :
    Embedding (fun _ : FrameStack => Bool)
      (Sum.elim (fun _ : K => Bool) (fun _ : Unit => Bool))
      FrameControl ((F × Bool) × Option Bool) F where
  stack := framePortInjection source payload hne
  symbol k := by cases k <;> exact Equiv.refl Bool
  state :=
    { toFun := fun v => ((v.1.2, v.2), v.1.1)
      invFun := fun v => ((v.2, v.1.1), v.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def frameCallerRoutine (source payload : K) (hne : source ≠ payload) :
    Routine (fun _ : K => Bool) (F × Bool) where
  W := Unit
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := FrameLabel
  entry := .prefix
  code l := (frameCallerEmbedding source payload hne).stmt id none (frameCode l)

def frameCallerBase (base : K → List Bool) :
    ∀ j : K ⊕ Unit, List ((Sum.elim (fun _ : K => Bool) (fun _ : Unit => Bool)) j)
  | .inl k => base k
  | .inr _ => []

def frameCallerStore (source payload : K) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs ps : List Bool) :
    Store (fun _ : K => Bool) (F × Bool) :=
  ⟨(frame, flag), Function.update (Function.update base source xs) payload ps⟩

theorem frameCallerStore_source (source payload : K) (hne : source ≠ payload)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ps : List Bool) :
    (frameCallerStore source payload base frame flag xs ps).stk source = xs := by
  simp [frameCallerStore, hne]

theorem frameCallerStore_payload (source payload : K)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ps : List Bool) :
    (frameCallerStore source payload base frame flag xs ps).stk payload = ps := by
  simp [frameCallerStore]

theorem frameCallerStore_outside (source payload k : K)
    (hs : k ≠ source) (hp : k ≠ payload)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ps : List Bool) :
    (frameCallerStore source payload base frame flag xs ps).stk k = base k := by
  simp [frameCallerStore, hs, hp]

/-- Exact entry/return boundary, including every untouched caller stack,
    the private empty tally, caller control and reset head scratch. -/
theorem frameCaller_boundary (source payload : K) (hne : source ≠ payload)
    (base : K → List Bool) (frame : F) (flag : Bool)
    (l : Option FrameLabel) (xs ps : List Bool) :
    (frameCallerEmbedding source payload hne).cfg id none frame (frameCallerBase base)
      (frameCfg l (flag, none) xs [] ps) =
    (frameCallerRoutine source payload hne).boundary l
      (frameCallerStore source payload base frame flag xs ps) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  apply Embedding.liftStacks_eq
  · intro k
    cases k with
    | input =>
        simp [Routine.boundary, frameCallerRoutine, frameCallerEmbedding,
          framePortInjection, frameCallerStore, frameCfg, frameStacks, hne]
    | count => rfl
    | payload =>
        simp [Routine.boundary, frameCallerRoutine, frameCallerEmbedding,
          framePortInjection, frameCallerStore, frameCfg, frameStacks]
  · intro j hj
    cases j with
    | inl k =>
        have hs : k ≠ source := by
          intro h; subst k; exact hj .input rfl
        have hp : k ≠ payload := by
          intro h; subst k; exact hj .payload rfl
        simp [Routine.boundary, frameCallerRoutine, frameCallerStore,
          frameCallerBase, hs, hp]
    | inr u => cases u; exact False.elim (hj .count rfl)

def frameCallerResult (source payload : K) (base : K → List Bool) (frame : F) :
    Option (List Bool × List Bool) → Store (fun _ : K => Bool) (F × Bool)
  | none => frameCallerStore source payload base frame false [] []
  | some (word, rest) => frameCallerStore source payload base frame true rest word.reverse

theorem frameCaller_result_boundary (source payload : K) (hne : source ≠ payload)
    (base : K → List Bool) (frame : F) (result : Option (List Bool × List Bool)) :
    (frameCallerEmbedding source payload hne).cfg id none frame (frameCallerBase base)
      (rawFrameOutput result) =
    (frameCallerRoutine source payload hne).boundary none
      (frameCallerResult source payload base frame result) := by
  cases result with
  | none => exact frameCaller_boundary source payload hne base frame false none [] []
  | some pair =>
      rcases pair with ⟨word, rest⟩
      exact frameCaller_boundary source payload hne base frame true none rest word.reverse

/-- An actual routine and exact operational execution, not an assumed
    abstract contract. It covers ALL framed or malformed Boolean inputs.
    Only the two named caller ports change; the tally is private and clean. -/
theorem frameCaller_executes (source payload : K) (hne : source ≠ payload)
    (base : K → List Bool) (frame : F) (bits : List Bool) :
    ∃ n ≤ 2 * bits.length + 4,
      (frameCallerRoutine source payload hne).Executes
        (frameCallerStore source payload base frame false bits [])
        (frameCallerResult source payload base frame (readRawBinaryFrame bits)) n := by
  let h := binaryFrameTransducerRun bits
  have hs : Runs (TM2.step frameCode)
      (frameCfg (some .prefix) (false, none) bits [] [])
      (rawFrameOutput (readRawBinaryFrame bits)) h.steps :=
    Runs.of_iterate h.evals_in_steps
  have lifted := (frameCallerEmbedding source payload hne).runs
    id none frame (frameCallerBase base) frameCode
    (frameCallerRoutine source payload hne).code (fun _ => rfl) hs
  rw [frameCaller_boundary, frameCaller_result_boundary] at lifted
  exact ⟨h.steps, h.steps_le_m, lifted.iterate⟩

/-- The compiler's actual continuation transformation replaces a halt by
    a jump. No extra implicit execution of the next instruction is claimed.
    A later routine may begin at the exact returned boundary. -/
theorem frameCaller_then (source payload : K) (hne : source ≠ payload)
    (base : K → List Bool) (frame : F) (bits : List Bool)
    («next» : Routine (fun _ : K => Bool) (F × Bool))
    (finalStore : Store (fun _ : K => Bool) (F × Bool)) (nextSteps : ℕ)
    (hnext : next.Executes
      (frameCallerResult source payload base frame (readRawBinaryFrame bits))
      finalStore nextSteps) :
    ∃ n ≤ 2 * bits.length + 4 + nextSteps,
      (RoutineComposition.seq (frameCallerRoutine source payload hne) «next»).Executes
        (frameCallerStore source payload base frame false bits []) finalStore n := by
  obtain ⟨n, hn, h⟩ := frameCaller_executes source payload hne base frame bits
  exact ⟨n + nextSteps, Nat.add_le_add_right hn nextSteps,
    RoutineComposition.seq_executes _ _ h hnext⟩

/-! ## Actual payload-order restoration, not an assumed continuation -/

def frameReverseBase (base : K → List Bool) :
    ∀ j : K ⊕ Empty, List ((Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool)) j)
  | .inl k => base k
  | .inr e => nomatch e

def frameReverseRoutine (source output : K) :
    Routine (fun _ : K => Bool) (F × Bool) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Unit
  entry := ()
  code _ := Transfer.stmt (Equiv.refl ((F × Bool) × Option Bool))
    (.inl source) (.inl output) id id () none

theorem frameReverse_boundary (source output : K) (base : K → List Bool)
    (frame : F) (flag : Bool) (l : Option Unit) (xs ys : List Bool) :
    Transfer.cfg (Equiv.refl ((F × Bool) × Option Bool))
      (Sum.inl source) (Sum.inl output) (frameReverseBase base)
      l (frame, flag) none xs ys =
    (frameReverseRoutine source output).boundary l
      (frameCallerStore source output base frame flag xs ys) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext j
    cases j with
    | inl k =>
        simp [Transfer.cfg, Transfer.data, Routine.boundary, frameReverseRoutine,
          frameReverseBase, frameCallerStore, Function.update_apply]
    | inr e => nomatch e

/-- A real one-pass reversing routine, preserving caller control/other
    stacks and resetting private scratch. Source and output must differ. -/
theorem frameReverse_executes (source output : K) (hne : source ≠ output)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    (frameReverseRoutine source output).Executes
      (frameCallerStore source output base frame flag xs ys)
      (frameCallerStore source output base frame flag [] (xs.reverse ++ ys))
      (xs.length + 1) := by
  have hn : (Sum.inl source : K ⊕ Empty) ≠ Sum.inl output := by
    intro h; exact hne (Sum.inl.inj h)
  have h := Transfer.runs (Equiv.refl ((F × Bool) × Option Bool))
    (.inl source) (.inl output) hn id id () none
    (frameReverseRoutine source output).code (by rfl)
    (frameReverseBase base) (frame, flag) none xs ys
  change Runs (TM2.step (frameReverseRoutine source output).code)
    (Transfer.cfg (Equiv.refl ((F × Bool) × Option Bool))
      (.inl source) (.inl output) (frameReverseBase base)
      (some ()) (frame, flag) none xs ys)
    (Transfer.cfg (Equiv.refl ((F × Bool) × Option Bool))
      (.inl source) (.inl output) (frameReverseBase base)
      none (frame, flag) none [] ((xs.map id).reverse ++ ys)) (xs.length + 1) at h
  rw [List.map_id, frameReverse_boundary, frameReverse_boundary] at h
  exact h.iterate

/-- Re-express the same caller configuration before and after changing
    which pair of ports is active. No hidden data is copied or erased. -/
theorem frameCallerStore_rotate (source reverse output : K)
    (hso : source ≠ output) (hro : reverse ≠ output)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ps : List Bool) :
    frameCallerStore source reverse (Function.update base output []) frame flag xs ps =
    frameCallerStore reverse output (Function.update base source xs) frame flag ps [] := by
  unfold frameCallerStore
  congr 1
  funext k
  by_cases ho : k = output
  · subst k; simp [Ne.symm hso, Ne.symm hro]
  · by_cases hr : k = reverse
    · subst k; simp [hro]
    · simp [ho, hr]

def frameForwardResult (source reverse output : K) (base : K → List Bool) (frame : F) :
    Option (List Bool × List Bool) → Store (fun _ : K => Bool) (F × Bool)
  | none =>
      frameCallerStore reverse output (Function.update base source []) frame false [] []
  | some (word, rest) =>
      frameCallerStore reverse output (Function.update base source rest) frame true [] word

def frameForwardRoutine (source reverse output : K) (hsr : source ≠ reverse) :
    Routine (fun _ : K => Bool) (F × Bool) :=
  RoutineComposition.seq (frameCallerRoutine source reverse hsr)
    (frameReverseRoutine reverse output)

theorem readRawBinaryFrame_payload_bound (bits word rest : List Bool)
    (h : readRawBinaryFrame bits = some (word, rest)) : word.length ≤ bits.length := by
  cases hp : readUnaryFrame bits with
  | none => simp [readRawBinaryFrame, hp] at h
  | some pair =>
      rcases pair with ⟨width, tail⟩
      have hc := readUnaryFrame_consumption bits width tail hp
      by_cases hw : width ≤ tail.length
      · simp only [readRawBinaryFrame, hp, if_pos hw, Option.some.injEq,
          Prod.mk.injEq] at h
        have ht := List.length_take_le width tail
        rw [h.1] at ht
        omega
      · simp [readRawBinaryFrame, hp, hw] at h

/-- ALL input strings, exact forward-order payload, suffix and success
    flag, private cleanup and arbitrary caller-frame preservation. The
    reverse scratch port is empty on BOTH exits. All three ports differ. -/
theorem frameForward_executes (source reverse output : K)
    (hsr : source ≠ reverse) (hso : source ≠ output) (hro : reverse ≠ output)
    (base : K → List Bool) (frame : F) (bits : List Bool) :
    ∃ n ≤ 3 * bits.length + 5,
      (frameForwardRoutine source reverse output hsr).Executes
        (frameCallerStore source reverse (Function.update base output [])
          frame false bits [])
        (frameForwardResult source reverse output base frame (readRawBinaryFrame bits)) n := by
  obtain ⟨n, hn, hparse⟩ := frameCaller_executes source reverse hsr
    (Function.update base output []) frame bits
  cases hp : readRawBinaryFrame bits with
  | none =>
      have hreverse := frameReverse_executes reverse output hro
        (Function.update base source []) frame false [] []
      have hjoin := RoutineComposition.seq_executes
        (frameCallerRoutine source reverse hsr) (frameReverseRoutine reverse output)
        (by simpa [hp, frameCallerResult, frameCallerStore_rotate source reverse output hso hro]
          using hparse) hreverse
      refine ⟨n + 1, by omega, ?_⟩
      simpa [frameForwardRoutine, frameForwardResult, List.length_nil] using hjoin
  | some pair =>
      rcases pair with ⟨word, rest⟩
      have hw := readRawBinaryFrame_payload_bound bits word rest hp
      have hreverse := frameReverse_executes reverse output hro
        (Function.update base source rest) frame true word.reverse []
      have hjoin := RoutineComposition.seq_executes
        (frameCallerRoutine source reverse hsr) (frameReverseRoutine reverse output)
        (by simpa [hp, frameCallerResult, frameCallerStore_rotate source reverse output hso hro]
          using hparse) hreverse
      refine ⟨n + (word.length + 1), by omega, ?_⟩
      simpa [frameForwardRoutine, frameForwardResult] using hjoin

theorem frameForwardResult_outside (source reverse output k : K)
    (hs : k ≠ source) (hr : k ≠ reverse) (ho : k ≠ output)
    (base : K → List Bool) (frame : F) (result : Option (List Bool × List Bool)) :
    (frameForwardResult source reverse output base frame result).stk k = base k := by
  cases result with
  | none => simp [frameForwardResult, frameCallerStore, hs, hr, ho]
  | some pair =>
      rcases pair with ⟨word, rest⟩
      simp [frameForwardResult, frameCallerStore, hs, hr, ho]

theorem frameForwardResult_preserves_frame (source reverse output : K)
    (base : K → List Bool) (frame : F) (result : Option (List Bool × List Bool)) :
    (frameForwardResult source reverse output base frame result).state.1 = frame := by
  cases result with
  | none => rfl
  | some pair => rcases pair with ⟨word, rest⟩; rfl

def observeForwardCaller (source output : K)
    (s : Store (fun _ : K => Bool) (F × Bool)) : Option (List Bool × List Bool) :=
  if s.state.2 then some (s.stk output, s.stk source) else none

theorem frameForwardResult_observe (source reverse output : K)
    (hsr : source ≠ reverse) (hso : source ≠ output)
    (base : K → List Bool) (frame : F) (result : Option (List Bool × List Bool)) :
    observeForwardCaller source output
      (frameForwardResult source reverse output base frame result) = result := by
  cases result with
  | none => rfl
  | some pair =>
      rcases pair with ⟨word, rest⟩
      simp [observeForwardCaller, frameForwardResult, frameCallerStore, hsr, hso]

theorem frameForwardResult_reverse_empty (source reverse output : K)
    (hro : reverse ≠ output) (base : K → List Bool) (frame : F)
    (result : Option (List Bool × List Bool)) :
    (frameForwardResult source reverse output base frame result).stk reverse = [] := by
  cases result with
  | none => simp [frameForwardResult, frameCallerStore, hro]
  | some pair =>
      rcases pair with ⟨word, rest⟩
      simp [frameForwardResult, frameCallerStore, hro]

/-- Same complete target, augmented by the actually supplied caller-safe
    frame front end. This is NOT a complete polynomial reduction witness. -/
theorem full_reduction_with_caller_frame (input : List Bool) (lambda : ℝ)
    (source reverse output : K)
    (hsr : source ≠ reverse) (hso : source ≠ output) (hro : reverse ≠ output)
    (base : K → List Bool) (frame : F) :
    (SourceBitMSSCDecision input ↔
      EncodedTargetCartaDecision (scanEncodedConstructor input) lambda) ∧
    (EncodedTargetCartaDecision (scanEncodedConstructor input) lambda ↔
      ∃ cert : List Bool,
        cert.length ≤ targetBitCertificateBound (scanEncodedConstructor input).length ∧
        scanPairVerifier (verifierPairBits (scanEncodedConstructor input) cert) = true) ∧
    ∀ bits : List Bool, ∃ n ≤ 3 * bits.length + 5,
      (frameForwardRoutine source reverse output hsr).Executes
        (frameCallerStore source reverse (Function.update base output []) frame false bits [])
        (frameForwardResult source reverse output base frame (readVerifierPair bits)) n := by
  have h := full_explicit_pair_interface input lambda
  refine ⟨h.2.1, h.2.2, ?_⟩
  intro bits
  simpa only [readRawBinaryFrame_eq_readVerifierPair] using
    frameForward_executes source reverse output hsr hso hro base frame bits

/- No complete constructor or verifier is postulated by an unconditional
complexity theorem. This module supplies the parser's actual caller-safe
forward-order front end, not either whole clean-output machine witness.
Nested frame/list/tree parsing, bounded binary arithmetic, checking and
serialization still need actual code/time proofs. Kernel acceptance,
external dependency compatibility and upstream formal hardness remain open.
-/

end PolytomyReductionModel
