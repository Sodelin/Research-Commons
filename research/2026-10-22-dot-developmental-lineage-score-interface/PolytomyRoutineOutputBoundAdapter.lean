/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Reuse Szymon Torunczyk and GPT's actual arbitrary-configuration, arbitrary-
stack run-length theorem, rather than duplicate its generic push induction.
Exact source: szymtor/compositional-polytime at
7fadbfd005b359a66ccc1165b2d1becddb2906b8,
OutputBounds.lean blob e9a4fb8de36a17b85e17bf4c9ab9d06a598362a6;
RoutineMachine.lean blob f14467ef28d274dc8d5268881991e1716e8c5e9c.
OutputBounds itself credits Lax759944Proofs.TMToRam.Safety at registered
source 134e398cef46599371df99f10c9007bc34ba3868 for the push-count argument.

The actual restricted prefix has finite public stacks and finite control.
We need no extension to nonfinite caller inventories. The finite maximum
includes EVERY public and private stack of the same routine code. No
valid-input promise, success flag or designated-output restriction.
This does not resolve the recorded Lean/mathlib dependency-pin mismatch.
-/
import PolytomyRestrictedVerifierOriginalSemantics
import Lax218471Proofs.OutputBounds
import Lax218471Proofs.RoutineMachine

namespace PolytomyReductionModel.WholeVerifierController.LibraryRoutineSpace

open Turing Lax218471.Subroutine Lax218471Proofs

variable {K A σ : Type} [DecidableEq K] [Fintype K] [Fintype A] [Fintype σ]

/-- One constant for the entire fixed finite machine, including its
private stack inventory. Input/output/initial metadata do not alter code. -/
noncomputable def uniformPushBudget (p : Routine (fun _ : K => A) σ)
    (input output : K) (initial : σ) : ℕ := by
  let tm := RoutineMachine.machine p input output initial
  letI := tm.kFin
  exact (Finset.univ : Finset tm.K).sup (OutputBounds.machinePushBudget tm)

theorem budget_le_uniform (p : Routine (fun _ : K => A) σ)
    (input output : K) (initial : σ)
    (k : (RoutineMachine.machine p input output initial).K) :
    OutputBounds.machinePushBudget (RoutineMachine.machine p input output initial) k ≤
      uniformPushBudget p input output initial := by
  let tm := RoutineMachine.machine p input output initial
  letI := tm.kFin
  change OutputBounds.machinePushBudget tm k ≤
    (Finset.univ : Finset tm.K).sup (OutputBounds.machinePushBudget tm)
  exact Finset.le_sup (f := OutputBounds.machinePushBudget tm) (Finset.mem_univ k)

/-- Direct adapter of OutputBounds.run_length. That theorem already
counts all actual intermediate private-stack effects. Boundary reset
alone is NOT used as a time or intermediate-space estimate. -/
theorem routine_stack_bound (p : Routine (fun _ : K => A) σ)
    (input output : K) (initial : σ)
    (s t : Store (fun _ : K => A) σ) (n M : ℕ)
    (he : p.Executes s t n) (hs : ∀ k, (s.stk k).length ≤ M) :
    ∀ k, (t.stk k).length ≤ M + uniformPushBudget p input output initial * n := by
  let tm := RoutineMachine.machine p input output initial
  have hr : Runs tm.step (p.boundary (some p.entry) s) (p.boundary none t) n :=
    Runs.of_iterate he
  intro k
  have h := OutputBounds.run_length tm hr (.inl k)
  have hb := budget_le_uniform p input output initial (.inl k)
  have hm : n * OutputBounds.machinePushBudget tm (.inl k) ≤
      uniformPushBudget p input output initial * n := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n hb
  exact h.trans (Nat.add_le_add (hs k) hm)

theorem cleanupMass_uniform_bound {J F : Type} [DecidableEq J]
    (ks : List J) (s : CountdownStore J F) (M : ℕ)
    (hs : ∀ k, (s.stk k).length ≤ M) : cleanupMass ks s ≤ ks.length * M := by
  induction ks with
  | nil => simp [cleanupMass]
  | cons k ks ih =>
      have hk := hs k
      simp only [cleanupMass, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at *
      omega

end PolytomyReductionModel.WholeVerifierController.LibraryRoutineSpace
