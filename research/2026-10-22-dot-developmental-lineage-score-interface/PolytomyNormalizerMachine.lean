/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Finite standalone TM2 packaging of the ORIGINAL all-input normalizer.
An actual final atom resets public control, in addition to the preceding
private/owned-stack cleanup. The original downstream constructor is NOT
replaced by this component and still has its own machine obligation.
-/
import PolytomyOriginalNormalizerRoutine

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive NormalizerExtra where
  | record | inner | outer | cache | temp | result
  deriving DecidableEq, Fintype

def normalizerPorts : PrefixPorts NormalizerExtra where
  r := .record
  c := .inner
  d := .outer
  b := .cache
  t := .temp
  hrc := by decide
  hrd := by decide
  hrb := by decide
  hrt := by decide
  hcd := by decide
  hcb := by decide
  hct := by decide
  hdb := by decide
  hdt := by decide
  hbt := by decide

def normalizerInitial : CountdownState Unit := (((), false), false)

def normalizerResetOp : Op (NumericStack NormalizerExtra) Bool (CountdownState Unit) :=
  .load (fun _ => normalizerInitial)

def closedNormalizerRoutine : Routine (fun _ : NumericStack NormalizerExtra => Bool) (CountdownState Unit) :=
  RoutineComposition.seq (originalNormalizerRoutine normalizerPorts .result) (Atom.routine normalizerResetOp)

def normalizerEntry (bits : List Bool) : CountdownStore (NumericStack NormalizerExtra) Unit :=
  numericStore (fun _ => []) ((), false) false bits [] [] [] []

def normalizerExit (out : List Bool) : CountdownStore (NumericStack NormalizerExtra) Unit :=
  ⟨normalizerInitial, fun k => if k = .inr .result then out else []⟩

theorem normalizer_result_not_owned :
    (.inr NormalizerExtra.result : NumericStack NormalizerExtra) ∉ prefixOwned normalizerPorts := by
  simp [prefixOwned, normalizerPorts]

theorem normalizer_other_owned (k : NumericStack NormalizerExtra)
    (hk : k ≠ .inr .result) : k ∈ prefixOwned normalizerPorts := by
  cases k with
  | inl p => cases p <;> simp [prefixOwned, normalizerPorts]
  | inr e => cases e <;> simp_all [prefixOwned, normalizerPorts]

theorem closedNormalizer_executes (bits : List Bool) :
    ∃ n ≤ originalNormalizerStepBound bits.length + 1,
      closedNormalizerRoutine.Executes (normalizerEntry bits) (normalizerExit (normalizedSource bits)) n := by
  obtain ⟨n, hn, he, ho, hclear, hframe⟩ := originalNormalizer_executes normalizerPorts .result
    normalizer_result_not_owned bits (fun _ => []) rfl rfl rfl rfl rfl rfl () false false
  let s := originalNormalizerEval normalizerPorts .result bits (fun _ => []) ()
  have hreset : normalizerResetOp.apply s = normalizerExit (normalizedSource bits) := by
    apply countdownStore_ext
    · rfl
    · funext k
      by_cases hk : k = .inr .result
      · subst k
        simpa [normalizerResetOp, Op.apply, normalizerExit] using ho
      · have hc := hclear k (normalizer_other_owned k hk)
        simpa [normalizerResetOp, Op.apply, normalizerExit, hk] using hc
  have hlast := Atom.executes normalizerResetOp s
  rw [hreset] at hlast
  have hall := RoutineComposition.seq_executes (originalNormalizerRoutine normalizerPorts .result)
    (Atom.routine normalizerResetOp) he hlast
  exact ⟨n + 1, by omega, hall⟩

def originalNormalizerMachine : FinTM2 where
  K := NumericStack NormalizerExtra ⊕ closedNormalizerRoutine.W
  k₀ := .inl (.inl .source)
  k₁ := .inl (.inr .result)
  Γ := Sum.elim (fun _ : NumericStack NormalizerExtra => Bool) closedNormalizerRoutine.Δ
  Λ := closedNormalizerRoutine.Label
  main := closedNormalizerRoutine.entry
  σ := CountdownState Unit × closedNormalizerRoutine.τ
  initialState := (normalizerInitial, closedNormalizerRoutine.initial)
  m := closedNormalizerRoutine.code

theorem originalNormalizerMachine_init (bits : List Bool) :
    initList originalNormalizerMachine bits =
      closedNormalizerRoutine.boundary (some closedNormalizerRoutine.entry) (normalizerEntry bits) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inr w => simp [initList, originalNormalizerMachine, Routine.boundary]
    | inl k => cases k with
      | inl p => cases p <;> simp [initList, originalNormalizerMachine, Routine.boundary,
          normalizerEntry, numericStore, numericStacks]
      | inr e => cases e <;> simp [initList, originalNormalizerMachine, Routine.boundary,
          normalizerEntry, numericStore, numericStacks]

theorem originalNormalizerMachine_halt (out : List Bool) :
    haltList originalNormalizerMachine out = closedNormalizerRoutine.boundary none (normalizerExit out) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inr w => simp [haltList, originalNormalizerMachine, Routine.boundary]
    | inl k => cases k with
      | inl p => cases p <;> simp [haltList, originalNormalizerMachine, Routine.boundary, normalizerExit]
      | inr e => cases e <;> simp [haltList, originalNormalizerMachine, Routine.boundary, normalizerExit]

def originalNormalizerTime : Polynomial ℕ :=
  6 * Polynomial.X ^ 4 + 30 * Polynomial.X ^ 3 + 79 * Polynomial.X ^ 2 + 140 * Polynomial.X + 147

theorem originalNormalizerTime_eval (L : ℕ) :
    originalNormalizerTime.eval L = originalNormalizerStepBound L + 1 := by
  simp [originalNormalizerTime, originalNormalizerStepBound]
  ring

/-- A concrete source proposal for the SAME pinned TM2 polynomial-time
    evidence type. Unelaborated: this is not a verified certificate. -/
def originalNormalizerPoly :
    TM2ComputableInPolyTime (fun bits : List Bool => bits) (fun bits : List Bool => bits) normalizedSource where
  tm := originalNormalizerMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := originalNormalizerTime
  outputsFun bits := by
    obtain ⟨n, hn, he⟩ := closedNormalizer_executes bits
    refine { steps := n, evals_in_steps := ?_, steps_le_m := ?_ }
    · simpa [TM2OutputsInTime,
        originalNormalizerMachine_init, originalNormalizerMachine_halt,
        FinTM2.step, originalNormalizerMachine] using he
    · simpa [originalNormalizerTime_eval] using hn

/- The finite machine uses fixed stack/label/control types, resets all
public/private control at halt and leaves only the tagged output tape.
All input words receive the polynomial bound, including malformed data.
Its optional proof dependency remains uninstalled and unelaborated.
This is NOT ConstructorMachineWitness or VerifierMachineWitness. Whole
normalRecordConstructor/checker realization, closed encoded hardness,
compatibility/axiom audit and actual kernel execution remain open.
-/

end PolytomyReductionModel
