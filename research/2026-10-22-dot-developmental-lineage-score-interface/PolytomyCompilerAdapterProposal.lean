/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No dependency installed or vendored,
no compiler/runtime execution, no verification or full machine certificate.

External attribution: Szymon Toruńczyk and GPT, compositional-polytime,
Apache-2.0, commit 7fadbfd005b359a66ccc1165b2d1becddb2906b8.
Their package pins Lean 4.33.0 / mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Our existing source pin is unchanged. Compatibility still needs checking.

IMPORTANT: use the actual Lax218471Proofs theorem namespace. The parallel
Lax concepts-only interface declares its theorem statements as axioms.
This file does not use those concept-side theorem declarations.

The wrappers below are CONDITIONAL proof obligations for the SAME exact
constructor/verifier functions. No complete structured program or source
execution proof for either is supplied by this file.
-/
import PolytomyConstantBranchMachine
import Lax218471Proofs.Combinators

namespace PolytomyReductionModel

open Lax218471.PolynomialTime Lax218471.Programs Lax218471.Substitution

/-- An existing explicit fixed-literal machine can supply a real contract.
    This does NOT make an arbitrary list function a polynomial subroutine. -/
theorem literal_contract_realizable (out : List Bool) :
    Nonempty (Implementation (Graph (fun xs : List Bool => xs)
      (fun xs : List Bool => xs) (fun _ : List Bool => out))) :=
  Lax218471Proofs.Combinators.graph_realizable ⟨constantBranchPoly out⟩

/-- A source program must cover ALL constructor inputs, including malformed
    records. Every call needs an actual implementation; all source steps
    and call argument/reply lengths must receive uniform polynomial bounds. -/
theorem structured_constructor_to_machine
    {K σ I : Type} [DecidableEq K] [Fintype K] [Fintype σ]
    (R : I → List Bool → List Bool → Prop)
    (library : ∀ i, Nonempty (Implementation (R i))) (p : Program K Bool σ I)
    (input output : K) (initial : σ) (steps size : Polynomial ℕ)
    (h : ∀ xs : List Bool, ∃ n ≤ steps.eval xs.length,
      Executes R (size.eval xs.length) p
        (ioStore input initial xs)
        (ioStore output initial (scanEncodedConstructor xs)) n) :
    Nonempty ConstructorMachineWitness := by
  exact Lax218471Proofs.Substitution.polytime R library p input output initial
    (fun xs : List Bool => xs) (fun xs : List Bool => xs)
    scanEncodedConstructor steps size h

/-- The independent verifier has its original total pair-tape interface
    and emits exactly one Boolean. It receives no MSSC source witness. -/
theorem structured_verifier_to_machine
    {K σ I : Type} [DecidableEq K] [Fintype K] [Fintype σ]
    (R : I → List Bool → List Bool → Prop)
    (library : ∀ i, Nonempty (Implementation (R i))) (p : Program K Bool σ I)
    (input output : K) (initial : σ) (steps size : Polynomial ℕ)
    (h : ∀ xs : List Bool, ∃ n ≤ steps.eval xs.length,
      Executes R (size.eval xs.length) p
        (ioStore input initial xs)
        (ioStore output initial [scanPairVerifier xs]) n) :
    Nonempty VerifierMachineWitness := by
  exact Lax218471Proofs.Substitution.polytime R library p input output initial
    (fun xs : List Bool => xs) (fun answer : Bool => [answer])
    scanPairVerifier steps size h

/-- Candidate external proof-side composition, with the SAME Boolean
    intermediate encoding on both sides. Not mathlib's proof_wanted. -/
theorem proposed_boolean_machine_composition (f g : List Bool → List Bool)
    (hf : Nonempty (Turing.TM2ComputableInPolyTime
      (fun xs : List Bool => xs) (fun xs : List Bool => xs) f))
    (hg : Nonempty (Turing.TM2ComputableInPolyTime
      (fun xs : List Bool => xs) (fun xs : List Bool => xs) g)) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun xs : List Bool => xs) (fun xs : List Bool => xs) (g ∘ f)) :=
  Lax218471Proofs.Combinators.comp hf hg

/- No theorem here inhabits ConcreteMachineObligation unconditionally.
The full semantic/all-refinement theorem remains the one in the existing
source chain. Explicit structured programs, actual subroutine witnesses,
all-input execution and polynomial bounds, upstream formal hardness,
dependency compatibility and kernel validation remain required.
-/

end PolytomyReductionModel
