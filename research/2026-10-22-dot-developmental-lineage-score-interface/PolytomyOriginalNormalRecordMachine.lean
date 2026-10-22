/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Standalone finite TM2 for the SAME all-input normalRecordConstructor.
Entry is exactly one input word; halt has exactly the original output
word, all work empty and every finite-control component reset.
-/
import PolytomyOriginalAllInputRoutine

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

def originalNormalRecordMachine : FinTM2 where
  K := CanonicalGlobalStack ⊕ originalNormalRecordRoutine.W
  k₀ := .inl (globalScanPort (.inr .original))
  k₁ := .inl (globalFilterPort .output)
  Γ := Sum.elim (fun _ : CanonicalGlobalStack => Bool) originalNormalRecordRoutine.Δ
  Λ := originalNormalRecordRoutine.Label
  main := originalNormalRecordRoutine.entry
  σ := CountdownState SelectedRowFrame × originalNormalRecordRoutine.τ
  initialState := (canonicalCleanState, originalNormalRecordRoutine.initial)
  m := originalNormalRecordRoutine.code

theorem originalNormalRecordMachine_init (bits : List Bool) :
    initList originalNormalRecordMachine bits =
      originalNormalRecordRoutine.boundary (some originalNormalRecordRoutine.entry) (originalConstructorInput bits) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inr w => simp [initList, originalNormalRecordMachine, Routine.boundary]
    | inl k =>
        rcases k with k | g
        · rcases k with k | f
          · rcases k with n | u
            · cases n <;> simp [initList, originalNormalRecordMachine, Routine.boundary,
                originalConstructorInput, globalScanPort, globalFilterPort]
            · cases u <;> simp [initList, originalNormalRecordMachine, Routine.boundary,
                originalConstructorInput, globalScanPort, globalFilterPort]
          · cases f <;> simp [initList, originalNormalRecordMachine, Routine.boundary,
              originalConstructorInput, globalScanPort, globalFilterPort]
        · cases g <;> simp [initList, originalNormalRecordMachine, Routine.boundary,
            originalConstructorInput, globalScanPort, globalFilterPort]

theorem originalNormalRecordMachine_halt (out : List Bool) :
    haltList originalNormalRecordMachine out = originalNormalRecordRoutine.boundary none (canonicalCleanStore out) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inr w => simp [haltList, originalNormalRecordMachine, Routine.boundary]
    | inl k =>
        rcases k with k | g
        · rcases k with k | f
          · rcases k with n | u
            · cases n <;> simp [haltList, originalNormalRecordMachine, Routine.boundary,
                canonicalCleanStore, globalScanPort, globalFilterPort]
            · cases u <;> simp [haltList, originalNormalRecordMachine, Routine.boundary,
                canonicalCleanStore, globalScanPort, globalFilterPort]
          · cases f <;> simp [haltList, originalNormalRecordMachine, Routine.boundary,
              canonicalCleanStore, globalScanPort, globalFilterPort]
        · cases g <;> simp [haltList, originalNormalRecordMachine, Routine.boundary,
            canonicalCleanStore, globalScanPort, globalFilterPort]

/-- Concrete source term for the SAME formerly open all-word downstream
machine obligation. This declaration is UNELABORATED, not a certificate. -/
def originalNormalRecordPoly : NormalRecordMachineWitness where
  tm := originalNormalRecordMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := originalNormalRecordPolynomial
  outputsFun bits := by
    obtain ⟨n, hn, he⟩ := originalNormalRecord_all_words bits
    refine { steps := n, evals_in_steps := ?_, steps_le_m := hn }
    simpa [TM2OutputsInTime, originalNormalRecordMachine_init, originalNormalRecordMachine_halt,
      FinTM2.step, originalNormalRecordMachine] using he

/- All stack indices, labels, alphabets and control states are fixed
finite types, inherited from the concrete finite routines. No arbitrary
natural is a control register. The all-input bound is in bits.length,
not a promised scalar magnitude. Optional dependency installation,
elaboration, transitive axiom/compatibility audits and kernel checking
remain on hold. No verified machine certificate is asserted.
-/

end PolytomyReductionModel
