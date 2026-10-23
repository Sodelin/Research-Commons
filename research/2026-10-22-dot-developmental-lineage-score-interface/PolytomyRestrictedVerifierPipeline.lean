/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Compose the actual all-word prefix and all eight success-gated guards.
Operational time is bounded in the ORIGINAL input length, not free unary
header parameters. This is before the final cleanup/semantic/haltList
join and does not by itself supply VerifierMachineWitness.
-/
import PolytomyRestrictedVerifierGuardSequence

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def restrictedOperandBound (L : ℕ) : ℕ := (L + 2) ^ 2

def restrictedUniformStepBound (L : ℕ) (g : RestrictedGuardStep) : ℕ :=
  let Q := restrictedOperandBound L
  match g with
  | .markers => (Q + 1) *
      (((9 * L + 3 * Q + rowMarkerPairBound Q Q Q L + 27) + 4 * L + Q + 7) + 3) +
      4 * L + 4 * Q + 15
  | _ => restrictedStepBound Q Q Q L g

theorem restrictedStepBound_uniform (g : RestrictedGuardStep) (m A B L : ℕ)
    (hm : m ≤ restrictedOperandBound L) (hA : A ≤ restrictedOperandBound L)
    (hB : B ≤ restrictedOperandBound L) :
    restrictedStepBound m A B L g ≤ restrictedUniformStepBound L g := by
  have hsub : A - 2 ≤ restrictedOperandBound L := (Nat.sub_le A 2).trans hA
  cases g <;>
    dsimp [restrictedUniformStepBound, restrictedStepBound, uniqueAllBound, uniqueQueryBound,
      inclusionQueryBound, mixedAllBound, mixedRootBound, scopedTypeBound, typeCountBound,
      lastTypeQueryBound, typeAbsentBound, coverageBound, rowMarkersAllBound, rowMarkerStepBound,
      rowMarkerQueryBound, rowMarkerPairBound, typeMembershipBound, typeLeafBound,
      cellSubsetBound, allCladesBound, cladeFixedBound, cladeExistsBound, cladeCandidateBound,
      scoreBudgetBound, scoreAllBound, scoreNodeBound]
  all_goals
    repeat' first | exact hm | exact hA | exact hB | exact hsub | exact le_rfl |
      apply Nat.add_le_add | apply Nat.mul_le_mul

def restrictedUniformGuardsBound (L : ℕ) : ℕ :=
  (restrictedGuardSteps.map (fun g => restrictedUniformStepBound L g + 2)).sum + 1

theorem restrictedStepsBound_uniform (m A B L : ℕ)
    (hm : m ≤ restrictedOperandBound L) (hA : A ≤ restrictedOperandBound L)
    (hB : B ≤ restrictedOperandBound L) :
    restrictedStepsBound m A B L restrictedGuardSteps ≤ restrictedUniformGuardsBound L := by
  have hsum (gs : List RestrictedGuardStep) :
      (gs.map (fun g => restrictedStepBound m A B L g + 2)).sum ≤
        (gs.map (fun g => restrictedUniformStepBound L g + 2)).sum := by
    induction gs with
    | nil => exact le_rfl
    | cons g gs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (Nat.add_le_add_right (restrictedStepBound_uniform g m A B L hm hA hB) 2) ih
  exact Nat.add_le_add_right (hsum restrictedGuardSteps) 1

/-- Explicit polynomial, with only addition and multiplication. The
marker overestimate uses wanted type Q rather than Q-2, so no truncated
subtraction is silently called a polynomial. -/
def restrictedGuardPolynomial : Polynomial ℕ :=
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2
  let I := X * (34 * X + 8 * Q + 64) + 30 * X + 8 * Q + 56
  let U := X * (I + 8 * X + 20) + 12 * X + 17
  let T := X * (26 * X + 8 * Q + 54) + 30 * X + 8 * Q + 57
  let D := X * (T + 8 * X + 21) + 12 * X + 17
  let S := D + 11 * X + 27
  let M := X * (S + X + 14) + 12 * X + 17
  let C := D + 4 * Q + 5 * X + 12
  let RP := (X * (22 * X + 12 * Q + 54) + 12 * X + 18) +
    (X * (22 * X + 12 * Q + 58) + 12 * X + 18) + 2
  let R := (Q + 1) * (13 * X + 4 * Q + RP + 37) + 4 * X + 4 * Q + 15
  let SS := X * (I + 7) + 12 * X + 17
  let CE := X * (2 * SS + 11 * X + 35) + 12 * X + 18
  let CL := X * (CE + 11 * X + 33) + 12 * X + 17
  let SC := X * (S + 4 * Q + X + 16) + 12 * X + 17 + 4 * Q + X * Q + 7
  2 * U + M + C + R + (2 * SS + 1) + CL + SC + 17

theorem restrictedGuardPolynomial_eval (L : ℕ) :
    restrictedGuardPolynomial.eval L = restrictedUniformGuardsBound L := by
  simp [restrictedGuardPolynomial, restrictedUniformGuardsBound, restrictedGuardSteps,
    restrictedUniformStepBound, restrictedStepBound, restrictedOperandBound,
    uniqueAllBound, uniqueQueryBound, inclusionQueryBound, mixedAllBound, mixedRootBound,
    scopedTypeBound, typeCountBound, lastTypeQueryBound, typeAbsentBound, coverageBound,
    rowMarkerPairBound, typeMembershipBound, typeLeafBound, cellSubsetBound,
    allCladesBound, cladeFixedBound, cladeExistsBound, cladeCandidateBound,
    scoreBudgetBound, scoreAllBound, scoreNodeBound] <;> ring

theorem restrictedUniformGuardsBound_skip (L : ℕ) : 17 ≤ restrictedUniformGuardsBound L := by
  simp only [restrictedUniformGuardsBound, restrictedGuardSteps, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  omega

def restrictedPipelineResult (bits : List Bool) : RestrictedStore :=
  match readVerifierFront bits with
  | none => restrictedPrefixResult bits
  | some q => restrictedStepsEval q.2.1.2.1 (q.2.1.1 + q.2.1.2.1 * q.2.1.1 + 3)
      q.2.1.2.2 restrictedGuardSteps (restrictedPrefixResult bits)

def restrictedPipelinePolynomial : Polynomial ℕ :=
  14 * Polynomial.X ^ 3 + 110 * Polynomial.X ^ 2 + 447 * Polynomial.X + 603 + restrictedGuardPolynomial

theorem restrictedPipelinePolynomial_eval (L : ℕ) :
    restrictedPipelinePolynomial.eval L = restrictedPrefixBound L + restrictedUniformGuardsBound L := by
  simp [restrictedPipelinePolynomial, restrictedPrefixBound_expansion, restrictedGuardPolynomial_eval]

theorem restrictedPipelineResult_failed (bits : List Bool)
    (hf : (restrictedPrefixResult bits).state.2 = false) :
    restrictedPipelineResult bits = restrictedPrefixResult bits := by
  cases hr : readVerifierFront bits with
  | none => simp [restrictedPipelineResult, hr]
  | some q =>
      simpa only [restrictedPipelineResult, hr] using
        (restrictedSteps_failed restrictedGuardSteps q.2.1.2.1
          (q.2.1.1 + q.2.1.2.1 * q.2.1.1 + 3) q.2.1.2.2 (restrictedPrefixResult bits) hf).2

/-- All input words reach the actual pre-cleanup store in polynomial time.
This theorem does NOT identify the final bit with scanPairVerifier and
does not bound final cleanup mass or claim a compiled haltList witness. -/
theorem restrictedPipeline_executes (bits : List Bool) :
    ∃ n ≤ restrictedPipelinePolynomial.eval bits.length,
      restrictedPipeline.Executes (restrictedInitialStore bits) (restrictedPipelineResult bits) n ∧
      (restrictedPipelineResult bits).stk = (restrictedPrefixResult bits).stk := by
  obtain ⟨a, ha, hpref⟩ := restrictedPrefix_executes bits
  have hroutine : restrictedSeq (restrictedGuardPrograms.map restrictedGate) =
      restrictedStepsRoutine restrictedGuardSteps := rfl
  cases hf : (restrictedPrefixResult bits).state.2 with
  | false =>
      have hskip := (restrictedSteps_failed restrictedGuardSteps 0 0 0 (restrictedPrefixResult bits) hf).1
      have hlen : 2 * restrictedGuardSteps.length + 1 = 17 := rfl
      rw [hlen] at hskip
      have heq := restrictedPipelineResult_failed bits hf
      refine ⟨a + 17, ?_, ?_, by rw [heq]⟩
      · rw [restrictedPipelinePolynomial_eval]
        have hb := restrictedUniformGuardsBound_skip bits.length
        omega
      · simpa only [restrictedPipeline, hroutine, heq] using
          RoutineComposition.seq_executes _ _ hpref hskip
  | true =>
      cases hr : readVerifierFront bits with
      | none =>
          have ho := verifierFront_observation restrictedFrontPorts bits (fun _ => []) (by intro j; rfl) ()
          have hfalse : (restrictedFrontStore bits).state.2 = false :=
            (observeVerifierFront_none restrictedFrontPorts _).mp (by simpa [restrictedFrontStore, hr] using ho)
          simp [restrictedPrefixResult, hr, hfalse] at hf
      | some q =>
          rcases q with ⟨⟨input, cert⟩, ⟨⟨N, m, B⟩, rest⟩⟩
          obtain ⟨hpair, hheaders⟩ := (readVerifierFront_some bits input cert rest N m B).mp hr
          obtain ⟨hi, ho⟩ := restrictedPrefix_success_boundary bits input cert rest N m B hpair hheaders hf
          obtain ⟨b, hb, hrun, hstk, hinv⟩ := restrictedSteps_executes restrictedGuardSteps
            m (N + m * N + 3) B bits.length (restrictedPrefixResult bits) hi
          obtain ⟨hread, hNpos, hmpos⟩ :=
            (readDimensionedVerifierHeaders_some input.length (verifierBudgetCap input cert) input rest N m B).mp hheaders
          obtain ⟨hN, hm, hB, hA⟩ :=
            readVerifierHeaders_bounds input.length (verifierBudgetCap input cert) input rest N m B hread
          have hlen := readVerifierPair_payload_length bits input cert hpair
          have hcap := verifierBudgetCap_pair_bound bits input cert hpair
          have hinput : input.length ≤ bits.length := by omega
          have hprod := Nat.mul_le_mul hinput hinput
          have hmu : m ≤ restrictedOperandBound bits.length := by unfold restrictedOperandBound; nlinarith
          have hAu : N + m * N + 3 ≤ restrictedOperandBound bits.length := by unfold restrictedOperandBound; nlinarith
          have hBu : B ≤ restrictedOperandBound bits.length := by unfold restrictedOperandBound; nlinarith
          have hbound := restrictedStepsBound_uniform m (N + m * N + 3) B bits.length hmu hAu hBu
          refine ⟨a + b, ?_, ?_, ?_⟩
          · rw [restrictedPipelinePolynomial_eval]
            omega
          · simpa only [restrictedPipeline, hroutine, restrictedPipelineResult, hr] using
              RoutineComposition.seq_executes _ _ hpref hrun
          · simpa only [restrictedPipelineResult, hr] using hstk

/- The complete emitted PRE-CLEANUP pipeline now has proposed all-word
execution and an input-only polynomial. The actual final semantic bit,
all-path prefix tape-mass bound, exact cleaned haltList compilation and
independent EncodedSourceHardness are still unclosed. All source remains
UNELABORATED; no compiler/kernel or full complexity acceptance is claimed.
-/

end PolytomyReductionModel.WholeVerifierController
