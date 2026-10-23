/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

ONE fixed inventory and emitted program for the ORIGINAL restricted
marked-star decision language. All component calls below are concrete.
There is no supplied optimizer, parser, semantic-loop oracle or freely
variable cap. This file is NOT yet the whole execution/time theorem:
the exact cross-phase invariants and all-word polynomial are still due.
-/
import PolytomyVerifierFrontController

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive RestrictedExtraPort where
  | front (port : VerifierFrontPort)
  | targetGrammar (port : GrammarPort)
  | certGrammar (port : GrammarPort)
  | uniqueTarget (port : InclusionPort)
  | uniqueCert (port : InclusionPort)
  | mixed (port : MixedPort)
  | coverage (port : InclusionPort)
  | coverageOutput
  | marker (port : RowMarkerPort)
  | markerCounter
  | sets (port : InclusionPort)
  | clades (port : CladePort)
  | score (port : ScorePort)
  | answer
  deriving DecidableEq, Fintype

abbrev RestrictedPort := NumericStack RestrictedExtraPort
abbrev RestrictedStore := CountdownStore RestrictedPort Unit
abbrev RestrictedRoutine := Routine (fun _ : RestrictedPort => Bool) (CountdownState Unit)

def restrictedFrontPorts : VerifierFrontPorts RestrictedExtraPort where
  toFun := RestrictedExtraPort.front
  inj' := by intro a b h; cases h; rfl

def restrictedHeader (j : VerifierFrontPort) : RestrictedPort := .inr (.front j)
def restrictedTargetWord : RestrictedPort := .inr (.targetGrammar .tail)
def restrictedTargetMask : RestrictedPort := .inr (.targetGrammar .nodeMask)
def restrictedCertWord : RestrictedPort := .inr (.certGrammar .tail)
def restrictedCertMask : RestrictedPort := .inr (.certGrammar .nodeMask)

def restrictedTargetGrammarMap : GrammarPort → RestrictedPort
  | .source => .inl .source
  | .rows => restrictedHeader .rows
  | .types => restrictedHeader .types
  | j => .inr (.targetGrammar j)

def restrictedCertGrammarMap : GrammarPort → RestrictedPort
  | .source => restrictedHeader .certificate
  | .rows => restrictedHeader .rows
  | .types => restrictedHeader .types
  | j => .inr (.certGrammar j)

def restrictedTargetGrammarPorts : GrammarPorts RestrictedPort where
  toFun := restrictedTargetGrammarMap
  inj' := by decide

def restrictedCertGrammarPorts : GrammarPorts RestrictedPort where
  toFun := restrictedCertGrammarMap
  inj' := by decide

def restrictedUniqueTargetMap : InclusionPort → RestrictedPort
  | .outer .originalWord => restrictedTargetWord
  | .outer .originalMask => restrictedTargetMask
  | .outer .rows => restrictedHeader .rows
  | .outer .types => restrictedHeader .types
  | j => .inr (.uniqueTarget j)

def restrictedUniqueCertMap : InclusionPort → RestrictedPort
  | .outer .originalWord => restrictedCertWord
  | .outer .originalMask => restrictedCertMask
  | .outer .rows => restrictedHeader .rows
  | .outer .types => restrictedHeader .types
  | j => .inr (.uniqueCert j)

def restrictedUniqueTargetPorts : InclusionPorts RestrictedPort where
  toFun := restrictedUniqueTargetMap
  inj' := by decide

def restrictedUniqueCertPorts : InclusionPorts RestrictedPort where
  toFun := restrictedUniqueCertMap
  inj' := by decide

def restrictedMixedMap : MixedPort → RestrictedPort
  | .outer .originalWord => restrictedTargetWord
  | .outer .originalMask => restrictedTargetMask
  | .outer .rows => restrictedHeader .rows
  | .outer .types => restrictedHeader .types
  | j => .inr (.mixed j)

def restrictedMixedPorts : MixedPorts RestrictedPort where
  toFun := restrictedMixedMap
  inj' := by decide

def restrictedCoverageMap : InclusionPort → RestrictedPort
  | .outer .originalWord => restrictedTargetWord
  | .outer .originalMask => restrictedTargetMask
  | .outer .rows => restrictedHeader .rows
  | .outer .types => restrictedHeader .types
  | j => .inr (.coverage j)

def restrictedCoveragePorts : InclusionPorts RestrictedPort where
  toFun := restrictedCoverageMap
  inj' := by decide

theorem restrictedCoverageOutput_distinct (j : InclusionPort) :
    (.inr .coverageOutput : RestrictedPort) ≠ restrictedCoveragePorts j := by
  cases j with
  | outer k => cases k <;> decide
  | inner k => cases k <;> decide

def restrictedMarkerMap : RowMarkerPort → RestrictedPort
  | .rows => restrictedHeader .rows
  | .types => restrictedHeader .types
  | j => .inr (.marker j)

def restrictedMarkerPorts : RowMarkerPorts RestrictedPort where
  toFun := restrictedMarkerMap
  inj' := by decide

def restrictedSetMap : InclusionPort → RestrictedPort
  | .outer .originalWord => restrictedTargetWord
  | .outer .originalMask => restrictedTargetMask
  | .inner .originalWord => restrictedCertWord
  | .inner .originalMask => restrictedCertMask
  | .outer .rows => restrictedHeader .rows
  | .outer .types => restrictedHeader .types
  | j => .inr (.sets j)

def restrictedSetPorts : InclusionPorts RestrictedPort where
  toFun := restrictedSetMap
  inj' := by decide

def restrictedCladeMap : CladePort → RestrictedPort
  | .outer .originalWord => restrictedTargetWord
  | .outer .originalMask => restrictedTargetMask
  | .inner .originalWord => restrictedCertWord
  | .inner .originalMask => restrictedCertMask
  | .outer .rows => restrictedHeader .rows
  | .outer .types => restrictedHeader .types
  | j => .inr (.clades j)

def restrictedCladePorts : CladePorts RestrictedPort where
  toFun := restrictedCladeMap
  inj' := by decide

def restrictedScoreMap : ScorePort → RestrictedPort
  | .outer .originalWord => restrictedCertWord
  | .outer .originalMask => restrictedCertMask
  | .outer .rows => restrictedHeader .rows
  | .outer .types => restrictedHeader .types
  | j => .inr (.score j)

def restrictedScorePorts : ScorePorts RestrictedPort where
  toFun := restrictedScoreMap
  inj' := by decide

/-- Every later component, including syntax components which reset their
local result, is behind the actual current success bit. -/
def restrictedGate (r : RestrictedRoutine) : RestrictedRoutine :=
  RoutineControl.branch Prod.snd r (Atom.routine cleanupNoop)

def restrictedSeq : List RestrictedRoutine → RestrictedRoutine
  | [] => Atom.routine cleanupNoop
  | r :: rs => RoutineComposition.seq r (restrictedSeq rs)

def restrictedGuardPrograms : List RestrictedRoutine :=
  [uniqueAllRoutine restrictedUniqueTargetPorts,
   mixedAllRoutine restrictedMixedPorts,
   coverageRoutine restrictedCoveragePorts (.inr .coverageOutput) restrictedCoverageOutput_distinct,
   rowMarkersAllRoutine restrictedMarkerPorts restrictedTargetWord (.inr .markerCounter),
   uniqueAllRoutine restrictedUniqueCertPorts,
   cellSetRoutine restrictedSetPorts,
   allCladesRoutine restrictedCladePorts,
   scoreBudgetRoutine restrictedScorePorts (restrictedHeader .budget)]

def restrictedSyntaxRoutine : RestrictedRoutine :=
  RoutineComposition.seq (restrictedGate (originalTargetForestRoutine restrictedTargetGrammarPorts))
    (restrictedGate (originalCertificateGrammarRoutine restrictedCertGrammarPorts))

def restrictedPrefixRoutine : RestrictedRoutine :=
  RoutineComposition.seq (verifierFrontRoutine restrictedFrontPorts) restrictedSyntaxRoutine

/-- The whole semantic pipeline, without final cleanup yet. Front input
is the original pair word on numeric.source and every other tape empty.
The target grammar consumes the header residual; certificate grammar
consumes the saved ORIGINAL unframed certificate. Later scans share only
their saved words/masks and physical m,A operands; private banks differ.
No new copies or uncharged semantic rewiring are hidden in these maps. -/
def restrictedPipeline : RestrictedRoutine :=
  RoutineComposition.seq restrictedPrefixRoutine
    (restrictedSeq (restrictedGuardPrograms.map restrictedGate))

def restrictedEmitOp : Op RestrictedPort Bool (CountdownState Unit) :=
  .push (.inr .answer) Prod.snd

def restrictedResetOp : Op RestrictedPort Bool (CountdownState Unit) :=
  .load (fun _ => (((), false), false))

/-- A fixed finite compile-time enumeration, independent of input bits.
Its order is irrelevant to clearing. This is not a runtime semantic
enumeration or an input-dependent hidden-state bound. -/
noncomputable def restrictedCleanupOwned : List RestrictedPort :=
  (Finset.univ : Finset RestrictedPort).toList

theorem restrictedCleanupOwned_complete (j : RestrictedPort) : j ∈ restrictedCleanupOwned := by
  simp [restrictedCleanupOwned]

noncomputable def restrictedFinishRoutine : RestrictedRoutine :=
  RoutineComposition.seq (clearManyRoutine restrictedCleanupOwned)
    (RoutineComposition.seq (Atom.routine restrictedEmitOp) (Atom.routine restrictedResetOp))

def restrictedCleanStore (answer : Bool) : RestrictedStore :=
  ⟨(((), false), false), Function.update (fun _ => []) (.inr .answer) [answer]⟩

/-- Both truth values and arbitrary incoming junk: EVERY public tape is
physically cleared, one bit is emitted, then finite control is reset.
An input-length bound on incoming mass is still a pipeline obligation. -/
theorem restrictedFinish_executes (s : RestrictedStore) :
    ∃ n ≤ cleanupMass restrictedCleanupOwned s + restrictedCleanupOwned.length + 3,
      restrictedFinishRoutine.Executes s (restrictedCleanStore s.state.2) n := by
  obtain ⟨a, ha, hclear⟩ := clearMany_executes restrictedCleanupOwned s
  let u := clearManyEval restrictedCleanupOwned s
  have hu : u.stk = fun _ => [] := by
    funext j
    exact clearMany_member restrictedCleanupOwned j (restrictedCleanupOwned_complete j) s
  have hust : u.state = s.state := clearMany_state restrictedCleanupOwned s
  have hemit := Atom.executes restrictedEmitOp u
  have hreset := Atom.executes restrictedResetOp (restrictedEmitOp.apply u)
  have hfinal : restrictedResetOp.apply (restrictedEmitOp.apply u) = restrictedCleanStore s.state.2 := by
    apply countdownStore_ext
    · rfl
    · simp [restrictedResetOp, restrictedEmitOp, restrictedCleanStore, Op.apply, hu, hust]
  rw [hfinal] at hreset
  exact ⟨a + (1 + 1), by omega,
    RoutineComposition.seq_executes _ _ hclear (RoutineComposition.seq_executes _ _ hemit hreset)⟩

noncomputable def restrictedVerifierRoutine : RestrictedRoutine :=
  RoutineComposition.seq restrictedPipeline restrictedFinishRoutine

def restrictedInitialStore (bits : List Bool) : RestrictedStore :=
  numericStore (fun _ => []) ((), false) false bits [] [] [] []

/- DECISIVE CONTRACT STILL DUE, NOT REPLACED BY THE PROGRAM DEFINITION:

For every original Boolean word bits, emit scanPairVerifier bits in
restrictedCleanStore, with one input-length polynomial bound. Prove:

1. Front to both GrammarEntry predicates in THIS inventory, including
   certificate-bank freshness and outside-bank preservation on failure.
2. Successful grammar to the exact saved whole words/node masks, raw
   parser observations, all-range Boolean and empty residual requirements.
3. ONE invariant establishing every later component's physical entry;
   the restored-stack contracts then maintain it across all eight guards.
4. The eight exact original predicates, with globally absorbing failure.
   The loose front A bound is operational ONLY. Original budget clipping
   still uses parsed_valid_target_bounds and parsed_verifier_score_bound.
5. All-word pipeline time AND final cleanup mass bounded by one explicit
   polynomial; private routine scratch is empty by actual Executes joins.
6. Compile/package this particular routine at the exact haltList boundary.

VerifierMachineWitness is NOT supplied by this file. EncodedSourceHardness
is a separate missing premise. All these terms are UNELABORATED.
-/

end PolytomyReductionModel.WholeVerifierController
