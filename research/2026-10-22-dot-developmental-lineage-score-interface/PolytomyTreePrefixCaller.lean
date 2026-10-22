/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual embedding of the arbitrary-tree syntax machine into a caller.
The pending counter is a distinct physical public scratch stack, clean
on both exits. All other caller stacks and caller control are preserved.
-/
import PolytomyRawTreePrefixMachine
import PolytomyFrameCallerAdapter

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def treeSkipPortInjection (source pending : K) (hne : source ≠ pending) :
    TreeSkipStack ↪ (K ⊕ Empty) where
  toFun
    | .input => .inl source
    | .pending => .inl pending
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def treeSkipCallerEmbedding (source pending : K) (hne : source ≠ pending) :
    Embedding (fun _ : TreeSkipStack => Bool)
      (Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool))
      FrameControl ((F × Bool) × Option Bool) F where
  stack := treeSkipPortInjection source pending hne
  symbol k := by cases k <;> exact Equiv.refl Bool
  state :=
    { toFun := fun v => ((v.1.2, v.2), v.1.1)
      invFun := fun v => ((v.2, v.1.1), v.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def treeSkipCallerRoutine (source pending : K) (hne : source ≠ pending)
    (entry : TreeSkipLabel) : Routine (fun _ : K => Bool) (F × Bool) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := TreeSkipLabel
  entry := entry
  code l := (treeSkipCallerEmbedding source pending hne).stmt id none (treeSkipCode l)

theorem treeSkipCaller_boundary (source pending : K) (hne : source ≠ pending)
    (entry : TreeSkipLabel) (base : K → List Bool) (frame : F) (flag : Bool)
    (l : Option TreeSkipLabel) (bits ps : List Bool) :
    (treeSkipCallerEmbedding source pending hne).cfg id none frame (frameReverseBase base)
      (treeSkipCfg l (flag, none) bits ps) =
    (treeSkipCallerRoutine source pending hne entry).boundary l
      (frameCallerStore source pending base frame flag bits ps) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  apply Embedding.liftStacks_eq
  · intro k
    cases k with
    | input =>
        simp [Routine.boundary, treeSkipCallerRoutine, treeSkipCallerEmbedding,
          treeSkipPortInjection, treeSkipCfg, treeSkipStacks, frameCallerStore, hne]
    | pending =>
        simp [Routine.boundary, treeSkipCallerRoutine, treeSkipCallerEmbedding,
          treeSkipPortInjection, treeSkipCfg, treeSkipStacks, frameCallerStore]
  · intro j hj
    cases j with
    | inl k =>
        have hs : k ≠ source := by intro h; subst k; exact hj .input rfl
        have hp : k ≠ pending := by intro h; subst k; exact hj .pending rfl
        simp [Routine.boundary, treeSkipCallerRoutine, frameCallerStore,
          frameReverseBase, hs, hp]
    | inr e => nomatch e

def treeSkipCallerResult (source pending : K) (base : K → List Bool) (frame : F) :
    Option (List Bool) → Store (fun _ : K => Bool) (F × Bool)
  | none => frameCallerStore source pending base frame false [] []
  | some rest => frameCallerStore source pending base frame true rest []

theorem treeSkipCaller_result_boundary (source pending : K) (hne : source ≠ pending)
    (entry : TreeSkipLabel) (base : K → List Bool) (frame : F) (result : Option (List Bool)) :
    (treeSkipCallerEmbedding source pending hne).cfg id none frame (frameReverseBase base)
      (treeSkipEnd result) =
    (treeSkipCallerRoutine source pending hne entry).boundary none
      (treeSkipCallerResult source pending base frame result) := by
  cases result with
  | none => exact treeSkipCaller_boundary source pending hne entry base frame false none [] []
  | some rest => exact treeSkipCaller_boundary source pending hne entry base frame true none rest []

theorem treeSkipCaller_forest_executes (source pending : K) (hne : source ≠ pending)
    (base : K → List Bool) (frame : F) (flag : Bool) (bits : List Bool) (q : ℕ) :
    ∃ n ≤ 2 * bits.length + q + 2,
      (treeSkipCallerRoutine source pending hne .read).Executes
        (frameCallerStore source pending base frame flag bits (List.replicate q true))
        (treeSkipCallerResult source pending base frame (rawForestSkip bits.length q bits)) n := by
  let h := treeSkipReadRun bits.length q bits (flag, none) (le_refl _)
  have hs := Runs.of_iterate h.evals_in_steps
  have lifted := (treeSkipCallerEmbedding source pending hne).runs
    id none frame (frameReverseBase base) treeSkipCode
    (treeSkipCallerRoutine source pending hne .read).code (fun _ => rfl) hs
  rw [treeSkipCaller_boundary source pending hne .read,
    treeSkipCaller_result_boundary source pending hne .read] at lifted
  exact ⟨h.steps, h.steps_le_m, lifted.iterate⟩

theorem treeSkipCaller_prefix_executes (source pending : K) (hne : source ≠ pending)
    (base : K → List Bool) (frame : F) (flag : Bool) (bits : List Bool) :
    ∃ n ≤ 2 * bits.length + 4,
      (treeSkipCallerRoutine source pending hne .start).Executes
        (frameCallerStore source pending base frame flag bits [])
        (treeSkipCallerResult source pending base frame (rawForestSkip bits.length 1 bits)) n := by
  let h := treeSkipPrefixRun bits (flag, none)
  have hs := Runs.of_iterate h.evals_in_steps
  have lifted := (treeSkipCallerEmbedding source pending hne).runs
    id none frame (frameReverseBase base) treeSkipCode
    (treeSkipCallerRoutine source pending hne .start).code (fun _ => rfl) hs
  rw [treeSkipCaller_boundary source pending hne .start,
    treeSkipCaller_result_boundary source pending hne .start] at lifted
  exact ⟨h.steps, h.steps_le_m, lifted.iterate⟩

theorem treeSkipCaller_observation (source pending : K) (hne : source ≠ pending)
    (base : K → List Bool) (frame : F) (result : Option (List Bool)) :
    (if (treeSkipCallerResult source pending base frame result).state.2 then
      some ((treeSkipCallerResult source pending base frame result).stk source) else none) = result := by
  cases result <;> simp [treeSkipCallerResult, frameCallerStore, hne]

theorem treeSkipCaller_preserves (source pending k : K) (hs : k ≠ source) (hp : k ≠ pending)
    (base : K → List Bool) (frame : F) (result : Option (List Bool)) :
    (treeSkipCallerResult source pending base frame result).state.1 = frame ∧
      (treeSkipCallerResult source pending base frame result).stk pending = [] ∧
      (treeSkipCallerResult source pending base frame result).stk k = base k := by
  cases result <;> simp [treeSkipCallerResult, frameCallerStore, hs, hp]

end PolytomyReductionModel
