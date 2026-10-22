/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/machine certificate.

Exact finite-alphabet TM2 obligations for the full constructor and verifier.
No inhabitant of either machine-witness type is supplied or assumed by any
unconditional complexity theorem. These are the remaining proof targets.
-/
import PolytomyExplicitConstructor
import Mathlib.Computability.TuringMachine.Computable

namespace PolytomyReductionModel

/-- Fixed Boolean alphabet, with the first list length explicitly framed.
    Its length is 2*input.length + cert.length + 1. -/
def verifierPairBits (input cert : List Bool) : List Bool :=
  unaryFrame input.length ++ input ++ cert

def readVerifierPair (bits : List Bool) : Option (List Bool × List Bool) :=
  match readUnaryFrame bits with
  | none => none
  | some (width, rest) =>
      if width ≤ rest.length then some (rest.take width, rest.drop width)
      else none

theorem readVerifierPair_encode (input cert : List Bool) :
    readVerifierPair (verifierPairBits input cert) = some (input, cert) := by
  simp [readVerifierPair, verifierPairBits, List.append_assoc, readUnaryFrame_encode]

theorem verifierPairBits_length (input cert : List Bool) :
    (verifierPairBits input cert).length = 2 * input.length + cert.length + 1 := by
  simp only [verifierPairBits, unaryFrame, List.length_append,
    List.length_replicate, List.length_singleton]
  omega

/-- Defined on EVERY machine-input bit string. Malformed pair framing
    rejects; it does not require an external promise about the tape input. -/
def scanPairVerifier (bits : List Bool) : Bool :=
  match readVerifierPair bits with
  | none => false
  | some (input, cert) => scanEncodedTarget input cert

theorem scanPairVerifier_encode (input cert : List Bool) :
    scanPairVerifier (verifierPairBits input cert) = scanEncodedTarget input cert := by
  simp only [scanPairVerifier, readVerifierPair_encode]

theorem target_actual_iff_bounded_machine_pair (input : List Bool) (lambda : ℝ) :
    EncodedTargetCartaDecision input lambda ↔
      ∃ cert : List Bool, cert.length ≤ targetBitCertificateBound input.length ∧
        scanPairVerifier (verifierPairBits input cert) = true := by
  simp only [scanPairVerifier_encode]
  exact scan_encoded_target_actual_iff_bounded input lambda

/-- NOT INHABITED HERE: an actual finite-state, finite-stack-index TM2
    program, its alphabets and polynomial time bound, with all-input
    correctness in the pinned mathlib operational semantics. -/
abbrev ConstructorMachineWitness :=
  Turing.TM2ComputableInPolyTime
    (fun bits : List Bool => bits) (fun bits : List Bool => bits) scanEncodedConstructor

/-- NOT INHABITED HERE: the independent checker on a complete Boolean tape,
    returning exactly a one-bit Boolean answer under the same machine model. -/
abbrev VerifierMachineWitness :=
  Turing.TM2ComputableInPolyTime
    (fun bits : List Bool => bits) (fun answer : Bool => [answer]) scanPairVerifier

/-- An OPEN obligation, not an axiom or a proved existence assertion. -/
def ConcreteMachineObligation : Prop :=
  Nonempty ConstructorMachineWitness ∧ Nonempty VerifierMachineWitness

theorem full_explicit_pair_interface (input : List Bool) (lambda : ℝ) :
    (scanEncodedConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (scanEncodedConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (scanEncodedConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (scanEncodedConstructor input).length ∧
          scanPairVerifier (verifierPairBits (scanEncodedConstructor input) cert) = true) := by
  simpa only [scanPairVerifier_encode] using full_explicit_encoded_reduction input lambda

/- A machine witness must establish TM2OutputsInTime for ALL inputs, with
the exact haltList convention: result in the output stack, other stacks
empty, initial control state restored, halted label. Auxiliary cleanup and
binary arithmetic/copying costs cannot be omitted. No use is made of the
pinned proof_wanted generic polynomial-composition declaration. A compatible
formal hardness source and full source elaboration are separate obligations.
-/

end PolytomyReductionModel
