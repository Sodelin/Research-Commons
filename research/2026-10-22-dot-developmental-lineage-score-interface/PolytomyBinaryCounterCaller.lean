/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Genuine caller-preserving one-port embedding of the existing CONCRETE
binary counter encoder. Three work tapes and all encoder control are
private and return reset. All arbitrary caller data/control survive.
Uses the pinned proof-side Embedding.runs, not a black-box axiom.
-/
import PolytomyCompleteOriginalBlockGeneration
import PolytomyBinaryCounterEncoder

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

variable {K σ : Type} [DecidableEq K]

inductive BinaryCounterWork where
  | counter | scratch | width
  deriving DecidableEq, Fintype

def binaryCounterPortInjection (port : K) : CounterStack ↪ (K ⊕ BinaryCounterWork) where
  toFun
    | .input => .inl port
    | .counter => .inr .counter
    | .scratch => .inr .scratch
    | .width => .inr .width
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def binaryCounterCallerEmbedding (port : K) :
    Embedding (fun _ : CounterStack => Bool)
      (Sum.elim (fun _ : K => Bool) (fun _ : BinaryCounterWork => Bool))
      FrameControl (σ × FrameControl) σ where
  stack := binaryCounterPortInjection port
  symbol k := by cases k <;> exact Equiv.refl Bool
  state :=
    { toFun := fun v => (v.2, v.1)
      invFun := fun v => (v.2, v.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def binaryCounterCallerRoutine (port : K) : Routine (fun _ : K => Bool) σ where
  W := BinaryCounterWork
  Δ _ := Bool
  τ := FrameControl
  initial := (false, none)
  Label := CounterLabel
  entry := .tick
  code l := (binaryCounterCallerEmbedding port).stmt id none (counterCode l)

def binaryCounterCallerBase (base : K → List Bool) :
    ∀ j : K ⊕ BinaryCounterWork, List ((Sum.elim (fun _ : K => Bool) (fun _ : BinaryCounterWork => Bool)) j)
  | .inl k => base k
  | .inr _ => []

def binaryCounterCallerStore (port : K) (s : Store (fun _ : K => Bool) σ) (bits : List Bool) :
    Store (fun _ : K => Bool) σ := ⟨s.state, Function.update s.stk port bits⟩

theorem binaryCounterCallerStore_self (port : K) (s : Store (fun _ : K => Bool) σ) :
    binaryCounterCallerStore port s (s.stk port) = s := by
  cases s with
  | mk state stk =>
      change (⟨state, Function.update stk port (stk port)⟩ : Store (fun _ : K => Bool) σ) = ⟨state, stk⟩
      congr 1
      funext k
      by_cases h : k = port <;> simp [h]

theorem binaryCounterCaller_boundary (port : K) (s : Store (fun _ : K => Bool) σ)
    (l : Option CounterLabel) (bits : List Bool) :
    (binaryCounterCallerEmbedding port).cfg id none s.state (binaryCounterCallerBase s.stk)
      (counterCfg l (false, none) bits [] [] []) =
      (binaryCounterCallerRoutine port).boundary l (binaryCounterCallerStore port s bits) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  apply Embedding.liftStacks_eq
  · intro k
    cases k with
    | input => simp [Routine.boundary, binaryCounterCallerRoutine, binaryCounterCallerEmbedding,
        binaryCounterPortInjection, binaryCounterCallerStore, counterCfg, counterStacks]
    | counter => rfl
    | scratch => rfl
    | width => rfl
  · intro j hj
    cases j with
    | inl k =>
        have hk : k ≠ port := by
          intro h; subst k; exact hj .input rfl
        simp [Routine.boundary, binaryCounterCallerRoutine, binaryCounterCallerStore,
          binaryCounterCallerBase, hk]
    | inr w =>
        cases w with
        | counter => exact False.elim (hj .counter rfl)
        | scratch => exact False.elim (hj .scratch rfl)
        | width => exact False.elim (hj .width rfl)

def binaryCounterCallerEval (port : K) (s : Store (fun _ : K => Bool) σ) :=
  binaryCounterCallerStore port s (binaryNatFrame (s.stk port).length)

theorem binaryCounterCaller_executes (port : K) (s : Store (fun _ : K => Bool) σ) :
    ∃ n ≤ 2 * (s.stk port).length ^ 2 + 10 * (s.stk port).length + 10,
      (binaryCounterCallerRoutine port).Executes s (binaryCounterCallerEval port s) n := by
  let h := binaryCounterEncoderRun (s.stk port)
  have hr : Runs (TM2.step counterCode)
      (counterCfg (some .tick) (false, none) (s.stk port) [] [] [])
      (counterCfg none (false, none) (binaryNatFrame (s.stk port).length) [] [] []) h.steps :=
    Runs.of_iterate h.evals_in_steps
  have lifted := (binaryCounterCallerEmbedding port).runs id none s.state
    (binaryCounterCallerBase s.stk) counterCode (binaryCounterCallerRoutine port).code (fun _ => rfl) hr
  rw [binaryCounterCaller_boundary, binaryCounterCaller_boundary, binaryCounterCallerStore_self] at lifted
  exact ⟨h.steps, h.steps_le_m, lifted.iterate⟩

theorem binaryCounterCaller_value (port : K) (s : Store (fun _ : K => Bool) σ) :
    (binaryCounterCallerEval port s).stk port = binaryNatFrame (s.stk port).length := by
  simp [binaryCounterCallerEval, binaryCounterCallerStore]

theorem binaryCounterCaller_state (port : K) (s : Store (fun _ : K => Bool) σ) :
    (binaryCounterCallerEval port s).state = s.state := rfl

theorem binaryCounterCaller_extra (port k : K) (hk : k ≠ port) (s : Store (fun _ : K => Bool) σ) :
    (binaryCounterCallerEval port s).stk k = s.stk k := by
  simp [binaryCounterCallerEval, binaryCounterCallerStore, hk]

/- This is legitimately a SINGLE-port computation: input length becomes
the ORIGINAL binaryNatFrame on that same port. No row/parameter channels
are smuggled through a single-port call. Full original header sequence,
budget/cases/cleanup/standalone constructor and independent verifier/
encoded-hardness/kernel checks still require their own composition.
-/

end PolytomyReductionModel
