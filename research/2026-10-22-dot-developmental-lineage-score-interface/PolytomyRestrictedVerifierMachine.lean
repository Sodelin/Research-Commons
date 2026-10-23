/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The SAME concrete restricted verifier, packaged at exact mathlib initList
and haltList boundaries. This is a proposed source inhabitant, NOT an
accepted VerifierMachineWitness or a successful Lean compilation.
EncodedSourceHardness remains an independent premise.
-/
import PolytomyRestrictedVerifierCleanHalt

namespace PolytomyReductionModel.WholeVerifierController

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

noncomputable def restrictedVerifierMachine : FinTM2 where
  K := RestrictedPort ⊕ restrictedVerifierRoutine.W
  k₀ := .inl (.inl .source)
  k₁ := .inl (.inr .answer)
  Γ := Sum.elim (fun _ : RestrictedPort => Bool) restrictedVerifierRoutine.Δ
  Λ := restrictedVerifierRoutine.Label
  main := restrictedVerifierRoutine.entry
  σ := CountdownState Unit × restrictedVerifierRoutine.τ
  initialState := ((((), false), false), restrictedVerifierRoutine.initial)
  m := restrictedVerifierRoutine.code

theorem restrictedVerifierMachine_init (bits : List Bool) :
    initList restrictedVerifierMachine bits =
      restrictedVerifierRoutine.boundary (some restrictedVerifierRoutine.entry) (restrictedInitialStore bits) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inr w => simp [initList, restrictedVerifierMachine, Routine.boundary]
    | inl k =>
        cases k with
        | inl n => cases n <;>
            simp [initList, restrictedVerifierMachine, Routine.boundary,
              restrictedInitialStore, numericStore, numericStacks]
        | inr j => simp [initList, restrictedVerifierMachine, Routine.boundary,
            restrictedInitialStore, numericStore, numericStacks]

theorem restrictedVerifierMachine_halt (answer : Bool) :
    haltList restrictedVerifierMachine [answer] =
      restrictedVerifierRoutine.boundary none (restrictedCleanStore answer) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inr w => simp [haltList, restrictedVerifierMachine, Routine.boundary]
    | inl k =>
        by_cases hk : k = (.inr .answer : RestrictedPort)
        · subst k
          simp [haltList, restrictedVerifierMachine, Routine.boundary, restrictedCleanStore]
        · simp [haltList, restrictedVerifierMachine, Routine.boundary, restrictedCleanStore, hk]

/-- SOURCE inhabitant of the exact original verifier interface. Every
private routine tape is empty and its private state reset at Executes'
return boundary; haltList additionally requires all public tapes empty
except the sole output bit and the full initial finite control. All those
equalities are explicit above. No new unit-cost or optimizer oracle.

Elaboration, pin compatibility, transitive-axiom audit and kernel checking
remain NOT PERFORMED. This declaration does not certify itself. -/
noncomputable def restrictedVerifierPoly : VerifierMachineWitness where
  tm := restrictedVerifierMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := restrictedVerifierPolynomial
  outputsFun bits := by
    obtain ⟨n, hn, he⟩ := restrictedVerifier_all_words bits
    refine { steps := n, evals_in_steps := ?_, steps_le_m := hn }
    simpa [TM2OutputsInTime, restrictedVerifierMachine_init, restrictedVerifierMachine_halt,
      FinTM2.step, restrictedVerifierMachine] using he

/- Whole source proposal is now written; acceptance is not established.
This remains ONLY the restricted marked-star decision language with its
original target guards and original root-inclusive D_lambda score.
Independent encoded-source hardness is not supplied by any verifier.
No broader biological inference, statistical identification, historical
novelty, Lean execution or complete NP-completeness acceptance is claimed.
-/

end PolytomyReductionModel.WholeVerifierController
