/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual caller embedding of the original legal-node mask logger. Its
pending and reverse-mask ports are DATA. All other caller tapes and the
caller frame survive; no natural value is hidden in finite control.
-/
import PolytomyTreeMaskMachine
import PolytomyFrameCallerAdapter

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

structure TreeMaskPorts (K : Type) where
  source : K
  pending : K
  reverse : K
  output : K
  hsp : source ≠ pending
  hsr : source ≠ reverse
  hso : source ≠ output
  hpr : pending ≠ reverse
  hpo : pending ≠ output
  hro : reverse ≠ output

def treeMaskPortInjection (p : TreeMaskPorts K) : TreeMaskStack ↪ (K ⊕ Empty) where
  toFun
    | .input => .inl p.source
    | .pending => .inl p.pending
    | .mask => .inl p.reverse
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [p.hsp, p.hsr, p.hpr, Ne.symm p.hsp,
      Ne.symm p.hsr, Ne.symm p.hpr]

def treeMaskCallerEmbedding (p : TreeMaskPorts K) :
    Embedding (fun _ : TreeMaskStack => Bool)
      (Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool))
      FrameControl ((F × Bool) × Option Bool) F where
  stack := treeMaskPortInjection p
  symbol k := by cases k <;> exact Equiv.refl Bool
  state :=
    { toFun := fun v => ((v.1.2, v.2), v.1.1)
      invFun := fun v => ((v.2, v.1.1), v.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def treeMaskCallerRoutine (p : TreeMaskPorts K) (entry : TreeSkipLabel) :
    Routine (fun _ : K => Bool) (F × Bool) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := TreeSkipLabel
  entry := entry
  code l := (treeMaskCallerEmbedding p).stmt id none (treeMaskCode l)

def treeMaskCallerStore (p : TreeMaskPorts K) (base : K → List Bool) (frame : F)
    (flag : Bool) (bits ps os : List Bool) : Store (fun _ : K => Bool) (F × Bool) :=
  frameCallerStore p.pending p.reverse (Function.update base p.source bits) frame flag ps os

theorem treeMaskCaller_boundary (p : TreeMaskPorts K) (entry : TreeSkipLabel)
    (base : K → List Bool) (frame : F) (flag : Bool) (l : Option TreeSkipLabel)
    (bits ps os : List Bool) :
    (treeMaskCallerEmbedding p).cfg id none frame (frameReverseBase base)
      (treeMaskCfg l (flag, none) bits ps os) =
      (treeMaskCallerRoutine p entry).boundary l
        (treeMaskCallerStore p base frame flag bits ps os) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  apply Embedding.liftStacks_eq
  · intro k
    cases k <;> simp [Routine.boundary, treeMaskCallerRoutine, treeMaskCallerEmbedding,
      treeMaskPortInjection, treeMaskCfg, treeMaskStacks, treeMaskCallerStore,
      frameCallerStore, p.hsp, p.hsr, p.hpr]
  · intro j hj
    cases j with
    | inl k =>
        have hs : k ≠ p.source := by intro h; subst k; exact hj .input rfl
        have hp : k ≠ p.pending := by intro h; subst k; exact hj .pending rfl
        have hr : k ≠ p.reverse := by intro h; subst k; exact hj .mask rfl
        simp [Routine.boundary, treeMaskCallerRoutine, treeMaskCallerStore,
          frameCallerStore, frameReverseBase, hs, hp, hr]
    | inr e => nomatch e

def treeMaskCallerResult (p : TreeMaskPorts K) (base : K → List Bool) (frame : F)
    (os : List Bool) : Option (List Bool × List Bool) → Store (fun _ : K => Bool) (F × Bool)
  | none => treeMaskCallerStore p base frame false [] [] []
  | some (rest, mask) => treeMaskCallerStore p base frame true rest [] (mask.reverse ++ os)

theorem treeMaskCaller_result_boundary (p : TreeMaskPorts K) (entry : TreeSkipLabel)
    (base : K → List Bool) (frame : F) (os : List Bool)
    (result : Option (List Bool × List Bool)) :
    (treeMaskCallerEmbedding p).cfg id none frame (frameReverseBase base)
      (treeMaskEnd result os) =
      (treeMaskCallerRoutine p entry).boundary none (treeMaskCallerResult p base frame os result) := by
  cases result with
  | none => exact treeMaskCaller_boundary p entry base frame false none [] [] []
  | some v =>
      rcases v with ⟨rest, mask⟩
      exact treeMaskCaller_boundary p entry base frame true none rest [] (mask.reverse ++ os)

theorem treeMaskCaller_forest_executes (p : TreeMaskPorts K) (base : K → List Bool)
    (frame : F) (flag : Bool) (bits os : List Bool) (q : ℕ) :
    ∃ n ≤ 3 * bits.length + q + os.length + 3,
      (treeMaskCallerRoutine p .read).Executes
        (treeMaskCallerStore p base frame flag bits (List.replicate q true) os)
        (treeMaskCallerResult p base frame os (rawForestMaskParse bits.length q bits)) n := by
  let h := treeMaskReadRun bits.length q bits os (flag, none) (le_refl _)
  have hs := Runs.of_iterate h.evals_in_steps
  have lifted := (treeMaskCallerEmbedding p).runs id none frame (frameReverseBase base)
    treeMaskCode (treeMaskCallerRoutine p .read).code (fun _ => rfl) hs
  rw [treeMaskCaller_boundary p .read, treeMaskCaller_result_boundary p .read] at lifted
  exact ⟨h.steps, h.steps_le_m, lifted.iterate⟩

theorem treeMaskCaller_prefix_executes (p : TreeMaskPorts K) (base : K → List Bool)
    (frame : F) (flag : Bool) (bits : List Bool) :
    ∃ n ≤ 3 * bits.length + 5,
      (treeMaskCallerRoutine p .start).Executes (treeMaskCallerStore p base frame flag bits [] [])
        (treeMaskCallerResult p base frame [] (rawForestMaskParse bits.length 1 bits)) n := by
  let h := treeMaskPrefixRun bits (flag, none)
  have hs := Runs.of_iterate h.evals_in_steps
  have lifted := (treeMaskCallerEmbedding p).runs id none frame (frameReverseBase base)
    treeMaskCode (treeMaskCallerRoutine p .start).code (fun _ => rfl) hs
  rw [treeMaskCaller_boundary p .start, treeMaskCaller_result_boundary p .start] at lifted
  exact ⟨h.steps, h.steps_le_m, lifted.iterate⟩

theorem treeMaskCaller_preserves (p : TreeMaskPorts K) (k : K)
    (hs : k ≠ p.source) (hp : k ≠ p.pending) (hr : k ≠ p.reverse)
    (base : K → List Bool) (frame : F) (os : List Bool)
    (result : Option (List Bool × List Bool)) :
    (treeMaskCallerResult p base frame os result).state.1 = frame ∧
      (treeMaskCallerResult p base frame os result).stk p.pending = [] ∧
      (treeMaskCallerResult p base frame os result).stk k = base k := by
  cases result <;> simp [treeMaskCallerResult, treeMaskCallerStore, frameCallerStore,
    p.hpr, hs, hp, hr]

theorem treeMaskCaller_observation (p : TreeMaskPorts K) (base : K → List Bool)
    (frame : F) (result : Option (List Bool × List Bool)) :
    (if (treeMaskCallerResult p base frame [] result).state.2 then
      some ((treeMaskCallerResult p base frame [] result).stk p.source,
        ((treeMaskCallerResult p base frame [] result).stk p.reverse).reverse)
      else none) = result := by
  cases result with
  | none => rfl
  | some v =>
      rcases v with ⟨rest, mask⟩
      simp [treeMaskCallerResult, treeMaskCallerStore, frameCallerStore, p.hsp, p.hsr]

end PolytomyReductionModel
