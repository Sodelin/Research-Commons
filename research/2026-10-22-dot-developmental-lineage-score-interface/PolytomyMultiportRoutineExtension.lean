/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual multiport Routine embedding for the original constructor caller.
Every old public port and private stack is injected explicitly; added
Boolean caller tapes and a finite caller frame are untouched. This is not
the single-input/output Program.call interface and does not pretend to be.
-/
import PolytomyOriginalUnaryValidation
import Lax218471Proofs.Embedding

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K E σ A : Type}

def multiportStore (s : Store (fun _ : K => Bool) σ) (extra : E → List Bool) (frame : A) :
    Store (fun _ : K ⊕ E => Bool) (σ × A) :=
  ⟨(s.state, frame), Sum.elim s.stk extra⟩

def multiportEmbedding (p : Routine (fun _ : K => Bool) σ) :
    Embedding (Sum.elim (fun _ : K => Bool) p.Δ)
      (Sum.elim (fun _ : K ⊕ E => Bool) p.Δ) (σ × p.τ) ((σ × A) × p.τ) A where
  stack :=
    { toFun := fun | .inl k => .inl (.inl k) | .inr w => .inr w
      inj' := by intro x y h; cases x <;> cases y <;> simp_all }
  symbol k := by cases k <;> exact Equiv.refl _
  state :=
    { toFun := fun v => ((v.1.1, v.2), v.1.2)
      invFun := fun v => ((v.1.1, v.2), v.1.2)
      left_inv := by rintro ⟨⟨s, a⟩, t⟩; rfl
      right_inv := by rintro ⟨⟨s, t⟩, a⟩; rfl }

def multiportRoutine (p : Routine (fun _ : K => Bool) σ) :
    Routine (fun _ : K ⊕ E => Bool) (σ × A) where
  W := p.W
  Δ := p.Δ
  τ := p.τ
  initial := p.initial
  Label := p.Label
  entry := p.entry
  code l := (multiportEmbedding (E := E) (A := A) p).stmt id none (p.code l)

def multiportBase (p : Routine (fun _ : K => Bool) σ) (extra : E → List Bool) :
    ∀ j : (K ⊕ E) ⊕ p.W, List ((Sum.elim (fun _ : K ⊕ E => Bool) p.Δ) j)
  | .inl (.inl _) => []
  | .inl (.inr e) => extra e
  | .inr _ => []

theorem multiport_boundary (p : Routine (fun _ : K => Bool) σ)
    (l : Option p.Label) (s : Store (fun _ : K => Bool) σ) (extra : E → List Bool) (frame : A) :
    (multiportEmbedding p).cfg id none frame (multiportBase p extra) (p.boundary l s) =
      (multiportRoutine p).boundary l (multiportStore s extra frame) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  · apply (multiportEmbedding (E := E) (A := A) p).liftStacks_eq
    · intro k
      cases k with
      | inl k => simp [Routine.boundary, multiportRoutine, multiportEmbedding, multiportStore]
      | inr w => simp [Routine.boundary, multiportRoutine, multiportEmbedding]
    · intro j hj
      cases j with
      | inl q =>
          cases q with
          | inl k => exact False.elim (hj (.inl k) rfl)
          | inr e => rfl
      | inr w => exact False.elim (hj (.inr w) rfl)

theorem multiport_executes [DecidableEq K] [DecidableEq E]
    (p : Routine (fun _ : K => Bool) σ)
    (s t : Store (fun _ : K => Bool) σ) (extra : E → List Bool) (frame : A)
    (n : ℕ) (h : p.Executes s t n) :
    (multiportRoutine p).Executes (multiportStore s extra frame) (multiportStore t extra frame) n := by
  have hr : Runs (TM2.step p.code) (p.boundary (some p.entry) s) (p.boundary none t) n :=
    Runs.of_iterate h
  have lifted := (multiportEmbedding (E := E) (A := A) p).runs id none frame
    (multiportBase p extra) p.code (multiportRoutine p).code (fun _ => rfl) hr
  rw [multiport_boundary, multiport_boundary] at lifted
  exact lifted.iterate

/- The statement is for arbitrary extra tape contents and caller frame,
not just initially empty extras. All old private stacks/control retain
their clean boundary contract, while the exact same transition count is
preserved by the inspected actual Embedding.runs theorem. Finite E/A give
a finite larger caller when packaged, but no compiler or machine build
has checked these terms. This adapter is intended for the actual original
canonical constructor and does not replace its unsupplied algorithm.
-/

end PolytomyReductionModel
