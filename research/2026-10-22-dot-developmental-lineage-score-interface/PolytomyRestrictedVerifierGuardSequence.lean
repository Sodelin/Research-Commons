/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The EIGHT actual guard programs in the one fixed verifier, executed in
their declared order with absorbing rejection. No abstract query or
implementation premise is retained: the per-step contracts below are
instantiated from the existing concrete source routines and bank entry
proofs. The final semantic answer and global polynomial still require
their explicit joins; a source term is not compilation evidence.
-/
import PolytomyRestrictedVerifierGuardEntries

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive RestrictedGuardStep where
  | uniqueTarget | mixed | coverage | markers | uniqueCert | sets | clades | score
  deriving DecidableEq, Fintype

def restrictedGuardSteps : List RestrictedGuardStep :=
  [.uniqueTarget, .mixed, .coverage, .markers, .uniqueCert, .sets, .clades, .score]

def restrictedStepRoutine : RestrictedGuardStep → RestrictedRoutine
  | .uniqueTarget => uniqueAllRoutine restrictedUniqueTargetPorts
  | .mixed => mixedAllRoutine restrictedMixedPorts
  | .coverage => coverageRoutine restrictedCoveragePorts (.inr .coverageOutput) restrictedCoverageOutput_distinct
  | .markers => rowMarkersAllRoutine restrictedMarkerPorts restrictedTargetWord (.inr .markerCounter)
  | .uniqueCert => uniqueAllRoutine restrictedUniqueCertPorts
  | .sets => cellSetRoutine restrictedSetPorts
  | .clades => allCladesRoutine restrictedCladePorts
  | .score => scoreBudgetRoutine restrictedScorePorts (restrictedHeader .budget)

def restrictedStepEval (m A B : ℕ) : RestrictedGuardStep → RestrictedStore → RestrictedStore
  | .uniqueTarget => uniqueAllResult restrictedUniqueTargetPorts m A
  | .mixed => mixedAllResult restrictedMixedPorts m A
  | .coverage => coverageResult restrictedCoveragePorts m A
  | .markers => rowMarkersAllEval restrictedMarkerPorts restrictedTargetWord (.inr .markerCounter) m A
  | .uniqueCert => uniqueAllResult restrictedUniqueCertPorts m A
  | .sets => cellSetResult restrictedSetPorts m A
  | .clades => allCladesResult restrictedCladePorts m A
  | .score => scoreBudgetResult restrictedScorePorts m A B

def restrictedStepBound (m A B L : ℕ) : RestrictedGuardStep → ℕ
  | .uniqueTarget => uniqueAllBound m A L
  | .mixed => mixedAllBound m A L
  | .coverage => coverageBound m A L
  | .markers => rowMarkersAllBound m A L
  | .uniqueCert => uniqueAllBound m A L
  | .sets => 2 * cellSubsetBound m A L + 1
  | .clades => allCladesBound m A L
  | .score => scoreBudgetBound m A B L

theorem restrictedGuardPrograms_actual :
    restrictedGuardSteps.map restrictedStepRoutine = restrictedGuardPrograms := rfl

theorem restrictedStep_executes (g : RestrictedGuardStep) (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) :
    ∃ n ≤ restrictedStepBound m A B L g,
      (restrictedStepRoutine g).Executes s (restrictedStepEval m A B g s) n ∧
      (restrictedStepEval m A B g s).stk = s.stk ∧
      (restrictedStepEval m A B g s).state.1 = (s.state.1.1, false) := by
  cases g with
  | uniqueTarget =>
      obtain ⟨n, hn, he⟩ := uniqueAll_executes restrictedUniqueTargetPorts m A L s
        (restricted_unique_target_entry m A B L s hs)
      exact ⟨n, hn, he, rfl, rfl⟩
  | mixed =>
      obtain ⟨n, hn, he⟩ := mixedAll_executes restrictedMixedPorts m A L s
        (restricted_mixed_entry m A B L s hs)
      exact ⟨n, hn, he, rfl, rfl⟩
  | coverage =>
      obtain ⟨n, hn, he⟩ := coverage_executes restrictedCoveragePorts (.inr .coverageOutput)
        restrictedCoverageOutput_distinct m A L s (restricted_coverage_entry m A B L s hs)
        (hs.fresh _ rfl)
      exact ⟨n, hn, he, rfl, rfl⟩
  | markers =>
      exact rowMarkersAll_executes restrictedMarkerPorts restrictedTargetWord (.inr .markerCounter)
        (by intro j; cases j <;> decide) (by intro j; cases j <;> decide) (by decide)
        m A L s (restricted_marker_entry m A B L s hs)
  | uniqueCert =>
      obtain ⟨n, hn, he⟩ := uniqueAll_executes restrictedUniqueCertPorts m A L s
        (restricted_unique_cert_entry m A B L s hs)
      exact ⟨n, hn, he, rfl, rfl⟩
  | sets =>
      obtain ⟨n, hn, he⟩ := cellSet_executes restrictedSetPorts m A L s
        (restricted_set_entry m A B L s hs)
      exact ⟨n, hn, he, rfl, rfl⟩
  | clades =>
      obtain ⟨n, hn, he⟩ := allClades_executes restrictedCladePorts m A L
        (s.stk restrictedCertWord) (s.stk restrictedCertMask) s (restricted_clade_entry m A B L s hs)
      exact ⟨n, hn, he, rfl, rfl⟩
  | score =>
      obtain ⟨n, hn, he⟩ := scoreBudget_executes restrictedScorePorts (restrictedHeader .budget)
        (by intro j; cases j <;> decide) m A B L s (restricted_score_entry m A B L s hs)
        (hs.fresh _ rfl) hs.budget
      exact ⟨n, hn, he, rfl, rfl⟩

def restrictedStepsRoutine (gs : List RestrictedGuardStep) : RestrictedRoutine :=
  restrictedSeq (gs.map (fun g => restrictedGate (restrictedStepRoutine g)))

def restrictedStepsEval (m A B : ℕ) : List RestrictedGuardStep → RestrictedStore → RestrictedStore
  | [], s => s
  | g :: gs, s => restrictedStepsEval m A B gs
      (if s.state.2 then restrictedStepEval m A B g s else s)

def restrictedStepsBound (m A B L : ℕ) (gs : List RestrictedGuardStep) : ℕ :=
  (gs.map (fun g => restrictedStepBound m A B L g + 2)).sum + 1

/-- This is the actual fixed-depth sequential controller, not a semantic
forall oracle. A rejected bit skips every later call, which is essential
because a local routine may reset its own result to true. -/
theorem restrictedSteps_executes (gs : List RestrictedGuardStep) (m A B L : ℕ)
    (s : RestrictedStore) (hs : RestrictedGuardInv m A B L s) :
    ∃ n ≤ restrictedStepsBound m A B L gs,
      (restrictedStepsRoutine gs).Executes s (restrictedStepsEval m A B gs s) n ∧
      (restrictedStepsEval m A B gs s).stk = s.stk ∧
      RestrictedGuardInv m A B L (restrictedStepsEval m A B gs s) := by
  induction gs generalizing s with
  | nil =>
      exact ⟨1, by simp [restrictedStepsBound], Atom.executes cleanupNoop s, rfl, hs⟩
  | cons g gs ih =>
      cases hf : s.state.2 with
      | false =>
          have hgate := restrictedGate_failed (restrictedStepRoutine g) s hf
          obtain ⟨b, hb, htail, hstk, hinv⟩ := ih s hs
          refine ⟨2 + b, ?_, ?_, ?_, ?_⟩
          · simp only [restrictedStepsBound, List.map_cons, List.sum_cons] at *
            omega
          · simpa only [restrictedStepsRoutine, restrictedSeq, List.map_cons,
              restrictedStepsEval, hf, Bool.false_eq_true, ↓reduceIte] using
              RoutineComposition.seq_executes _ _ hgate htail
          · simpa only [restrictedStepsEval, hf, Bool.false_eq_true, ↓reduceIte] using hstk
          · simpa only [restrictedStepsEval, hf, Bool.false_eq_true, ↓reduceIte] using hinv
      | true =>
          obtain ⟨a, ha, hstep, hstk1, hframe⟩ := restrictedStep_executes g m A B L s hs
          have hgate := restrictedGate_passed _ s _ a hf hstep
          have hu := RestrictedGuardInv.transport m A B L s _ hs hstk1
          obtain ⟨b, hb, htail, hstk2, hinv⟩ := ih _ hu
          refine ⟨(a + 1) + b, ?_, ?_, ?_, ?_⟩
          · simp only [restrictedStepsBound, List.map_cons, List.sum_cons] at *
            omega
          · simpa only [restrictedStepsRoutine, restrictedSeq, List.map_cons,
              restrictedStepsEval, hf, ↓reduceIte] using
              RoutineComposition.seq_executes _ _ hgate htail
          · simpa only [restrictedStepsEval, hf, ↓reduceIte] using hstk2.trans hstk1
          · simpa only [restrictedStepsEval, hf, ↓reduceIte] using hinv

theorem restrictedSteps_failed (gs : List RestrictedGuardStep) (m A B : ℕ) (s : RestrictedStore)
    (hf : s.state.2 = false) :
    (restrictedStepsRoutine gs).Executes s s (2 * gs.length + 1) ∧
      restrictedStepsEval m A B gs s = s := by
  induction gs with
  | nil => exact ⟨Atom.executes cleanupNoop s, rfl⟩
  | cons g gs ih =>
      have hgate := restrictedGate_failed (restrictedStepRoutine g) s hf
      constructor
      · simpa [restrictedStepsRoutine, restrictedSeq, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using RoutineComposition.seq_executes _ _ hgate ih.1
      · simpa [restrictedStepsEval, hf] using ih.2

/-- Every observed raw parser/range fact survives the COMPLETE guard
phase, because the instantiated source contracts restore the entire
caller stack function, not merely selected saved fields. -/
theorem restrictedSteps_preserve_observations (gs : List RestrictedGuardStep) (N m B L : ℕ)
    (s : RestrictedStore) (hi : RestrictedGuardInv m (N + m * N + 3) B L s)
    (ho : RestrictedSyntaxObservation N m s) :
    RestrictedSyntaxObservation N m (restrictedStepsEval m (N + m * N + 3) B gs s) := by
  obtain ⟨n, hn, he, hstk, hfinal⟩ := restrictedSteps_executes gs m (N + m * N + 3) B L s hi
  exact RestrictedSyntaxObservation.transport N m s _ ho hstk

/- The full eight-step operational sequence is now proposed under the
ONE prefix-derived invariant. Its final exact original semantic bit,
global input-only bound, all-word prefix cleanup mass and compiled
haltList packaging remain unjoined. VerifierMachineWitness and the
independent EncodedSourceHardness premise are still not supplied.
-/

end PolytomyReductionModel.WholeVerifierController
