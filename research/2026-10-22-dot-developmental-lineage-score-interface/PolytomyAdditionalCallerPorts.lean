/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual multiport extension WITHOUT changing the public control type.
This lets the original validator coexist with canonical-output tapes and
continue to use the existing CountdownState arithmetic interfaces.
-/
import PolytomyMultiportRoutineExtension

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K E σ : Type}

def extraPortsStore (s : Store (fun _ : K => Bool) σ) (extra : E → List Bool) :
    Store (fun _ : K ⊕ E => Bool) σ := ⟨s.state, Sum.elim s.stk extra⟩

def extraPortsEmbedding (p : Routine (fun _ : K => Bool) σ) :
    Embedding (Sum.elim (fun _ : K => Bool) p.Δ)
      (Sum.elim (fun _ : K ⊕ E => Bool) p.Δ) (σ × p.τ) (σ × p.τ) Unit where
  stack := (multiportEmbedding (E := E) (A := Unit) p).stack
  symbol := (multiportEmbedding (E := E) (A := Unit) p).symbol
  state :=
    { toFun := fun v => (v, ())
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨v, u⟩; cases u; rfl }

def extraPortsRoutine (p : Routine (fun _ : K => Bool) σ) :
    Routine (fun _ : K ⊕ E => Bool) σ where
  W := p.W
  Δ := p.Δ
  τ := p.τ
  initial := p.initial
  Label := p.Label
  entry := p.entry
  code l := (extraPortsEmbedding (E := E) p).stmt id none (p.code l)

theorem extraPorts_boundary (p : Routine (fun _ : K => Bool) σ)
    (l : Option p.Label) (s : Store (fun _ : K => Bool) σ) (extra : E → List Bool) :
    (extraPortsEmbedding p).cfg id none () (multiportBase p extra) (p.boundary l s) =
      (extraPortsRoutine p).boundary l (extraPortsStore s extra) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  · apply (extraPortsEmbedding (E := E) p).liftStacks_eq
    · intro k
      cases k with
      | inl k => simp [Routine.boundary, extraPortsRoutine, extraPortsEmbedding,
          multiportEmbedding, extraPortsStore]
      | inr w => simp [Routine.boundary, extraPortsRoutine, extraPortsEmbedding, multiportEmbedding]
    · intro j hj
      cases j with
      | inl q =>
          cases q with
          | inl k => exact False.elim (hj (.inl k) rfl)
          | inr e => rfl
      | inr w => exact False.elim (hj (.inr w) rfl)

theorem extraPorts_executes [DecidableEq K] [DecidableEq E]
    (p : Routine (fun _ : K => Bool) σ)
    (s t : Store (fun _ : K => Bool) σ) (extra : E → List Bool)
    (n : ℕ) (h : p.Executes s t n) :
    (extraPortsRoutine p).Executes (extraPortsStore s extra) (extraPortsStore t extra) n := by
  have hr : Runs (TM2.step p.code) (p.boundary (some p.entry) s) (p.boundary none t) n :=
    Runs.of_iterate h
  have lifted := (extraPortsEmbedding (E := E) p).runs id none ()
    (multiportBase p extra) p.code (extraPortsRoutine p).code (fun _ => rfl) hr
  rw [extraPorts_boundary, extraPorts_boundary] at lifted
  exact lifted.iterate

/-- Actual original validator call with arbitrary untouched caller tapes.
    No one-input/output Program.call is misused as this multiport interface. -/
theorem originalValidator_with_extra_ports [DecidableEq E] (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) (extra : E → List Bool) :
    ∃ n ≤ originalUnaryValidationBound L,
      (extraPortsRoutine (E := E) originalUnaryValidationRoutine).Executes
        (extraPortsStore s extra) (extraPortsStore (originalUnaryValidationEval s) extra) n ∧
      (extraPortsStore (originalUnaryValidationEval s) extra).state.2 =
        originalUnaryValidity (s.stk (.inr .original)) ∧
      ∀ e, (extraPortsStore (originalUnaryValidationEval s) extra).stk (.inr e) = extra e := by
  obtain ⟨n, hn, he, hready, hclean, hpres, hflag⟩ := originalUnaryValidation_executes L s hs hq
  exact ⟨n, hn, extraPorts_executes originalUnaryValidationRoutine s (originalUnaryValidationEval s) extra n he,
    hflag, fun _ => rfl⟩

/- Finite E gives a fixed finite extension when the complete constructor
is packaged. This type-level construction preserves arbitrary extra data,
including already emitted output, at the SAME actual transition count.
Canonical enumeration, arithmetic and output controller are not supplied
merely by this adapter; their full obligations remain explicit.
-/

end PolytomyReductionModel
