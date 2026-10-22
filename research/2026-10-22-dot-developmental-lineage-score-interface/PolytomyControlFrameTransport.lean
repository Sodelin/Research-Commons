/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual control-frame transport of an entire concrete multiport Routine.
The code is transformed instruction by instruction through the pinned
Embedding.stmt, and its SAME transition count follows from Embedding.runs.
This is not merely a logical transport of a stack invariant.
-/
import PolytomyAdditionalCallerPorts

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

variable {K σ V A : Type}

def controlTransportStore (e : V ≃ σ × A) (s : Store (fun _ : K => Bool) σ) (a : A) :
    Store (fun _ : K => Bool) V := ⟨e.symm (s.state, a), s.stk⟩

def controlTransportEmbedding (p : Routine (fun _ : K => Bool) σ) (e : V ≃ σ × A) :
    Embedding (Sum.elim (fun _ : K => Bool) p.Δ)
      (Sum.elim (fun _ : K => Bool) p.Δ) (σ × p.τ) (V × p.τ) A where
  stack := { toFun := id, inj' := fun _ _ h => h }
  symbol _ := Equiv.refl _
  state :=
    { toFun := fun v => (((e v.1).1, v.2), (e v.1).2)
      invFun := fun v => (e.symm (v.1.1, v.2), v.1.2)
      left_inv := by rintro ⟨v, t⟩; simp
      right_inv := by rintro ⟨⟨s, t⟩, a⟩; simp }

def controlTransportRoutine (p : Routine (fun _ : K => Bool) σ) (e : V ≃ σ × A) :
    Routine (fun _ : K => Bool) V where
  W := p.W
  Δ := p.Δ
  τ := p.τ
  initial := p.initial
  Label := p.Label
  entry := p.entry
  code l := (controlTransportEmbedding p e).stmt id none (p.code l)

theorem controlTransport_boundary (p : Routine (fun _ : K => Bool) σ) (e : V ≃ σ × A)
    (l : Option p.Label) (s : Store (fun _ : K => Bool) σ) (a : A) :
    (controlTransportEmbedding p e).cfg id none a (fun _ => []) (p.boundary l s) =
      (controlTransportRoutine p e).boundary l (controlTransportStore e s a) := by
  apply RoutineComposition.cfg_ext
  · cases l <;> rfl
  · rfl
  · apply (controlTransportEmbedding p e).liftStacks_eq
    · intro k
      cases k <;> simp [Routine.boundary, controlTransportRoutine,
        controlTransportEmbedding, controlTransportStore]
    · intro j hj
      exact False.elim (hj j rfl)

theorem controlTransport_executes [DecidableEq K]
    (p : Routine (fun _ : K => Bool) σ) (e : V ≃ σ × A)
    (s t : Store (fun _ : K => Bool) σ) (a : A) (n : ℕ) (h : p.Executes s t n) :
    (controlTransportRoutine p e).Executes
      (controlTransportStore e s a) (controlTransportStore e t a) n := by
  have hr : Runs (TM2.step p.code) (p.boundary (some p.entry) s) (p.boundary none t) n :=
    Runs.of_iterate h
  have lifted := (controlTransportEmbedding p e).runs id none a (fun _ => [])
    p.code (controlTransportRoutine p e).code (fun _ => rfl) hr
  rw [controlTransport_boundary, controlTransport_boundary] at lifted
  exact lifted.iterate

/- The generic equivalence changes no tapes, private work or transition
count. Its intended use below has fixed finite controls: the original
validator's three Boolean control bits plus two untouched Boolean bits
are exactly the constructor's five Boolean bits. Finite-state packaging
still needs its own explicit instance and all-input boundary proof.
-/

end PolytomyReductionModel
