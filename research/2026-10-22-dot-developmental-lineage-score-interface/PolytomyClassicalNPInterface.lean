/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE ONLY, UNELABORATED. No installation or execution.

Definitions: Edouard Bonnet and Codex 5.6 and 6, classical-complexity,
0c0840319318215fd7b36a9a822b81ce55cf6941, and cook-levin,
905f2da2698d5b38002676f74632aa716e731389, both Apache-2.0.
Actual composition proof: Szymon Torunczyk and GPT, compositional-polytime,
7fadbfd005b359a66ccc1165b2d1becddb2906b8, Apache-2.0.

Only DEFINITION interfaces and the actual proof-side composition are used.
No concept-side NP-hardness, certificate, SAT or model-equivalence axiom
is invoked. External pin compatibility and kernel axiom audits remain open.

The final result is explicitly CONDITIONAL on the whole original machines
and source hardness. None of those hypotheses is silently discharged by
the concrete pair converter. The target remains the actual D_lambda over
every independently admissible binary refinement and compatible labeling.
-/
import PolytomyVerifierPairMachine
import Lax218471Proofs.Combinators
import Lax434930.NondeterministicPolynomialTime
import Lax429075.Reductions

namespace PolytomyReductionModel

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime
open Lax429075.Reductions

def cartaTargetLanguage (lambda : ℝ) : Language :=
  {input | EncodedTargetCartaDecision input lambda}

def msscSourceLanguage : Language := {input | SourceBitMSSCDecision input}

theorem external_pair_eq (input cert : List Bool) :
    Lax434930.Certificates.pair input cert = blockPair input cert := by
  induction input with
  | nil => rfl
  | cons b input ih =>
      simp only [Lax434930.Certificates.pair, blockPair, ih]

def convertedPairVerifier : List Bool → Bool := scanPairVerifier ∘ convertVerifierPair

theorem convertedPairVerifier_external_pair (input cert : List Bool) :
    convertedPairVerifier (Lax434930.Certificates.pair input cert) =
      scanEncodedTarget input cert := by
  simpa only [convertedPairVerifier, Function.comp_apply, external_pair_eq] using
    convertedVerifier_pair input cert

/-- The adapter is supplied; the ENTIRE independent checker is not. -/
theorem convertedPairVerifier_polytime (hV : Nonempty VerifierMachineWitness) :
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool
      convertedPairVerifier) := by
  have h := Lax218471Proofs.Combinators.comp
    (show Nonempty (Turing.TM2ComputableInPolyTime
      (fun xs : List Bool => xs) (fun xs : List Bool => xs) convertVerifierPair)
      from ⟨verifierPairConversionPoly⟩) hV
  simpa only [convertedPairVerifier, Computability.encodeBool] using h

/-- This is membership in the original certificate/TM2 class, not in a
    newly defined size-only or abstract-cost substitute. -/
theorem cartaTarget_in_NP_of_verifier (lambda : ℝ)
    (hV : Nonempty VerifierMachineWitness) : cartaTargetLanguage lambda ∈ NP := by
  let V : Language := {bits | convertedPairVerifier bits = true}
  refine ⟨V, ?_, Polynomial.X * (2 * Polynomial.X + 3), ?_⟩
  · exact ⟨convertedPairVerifier, fun _ => Iff.rfl,
      convertedPairVerifier_polytime hV⟩
  · intro input
    simpa [cartaTargetLanguage, V, convertedPairVerifier_external_pair,
      targetBitCertificateBound] using scan_encoded_target_actual_iff_bounded input lambda

/-- The map is the SAME total byte constructor, including malformed and
    boundary source strings. Its full machine witness remains a hypothesis. -/
theorem full_carta_manyOne_of_constructor (lambda : ℝ)
    (hC : Nonempty ConstructorMachineWitness) :
    ManyOne msscSourceLanguage (cartaTargetLanguage lambda) := by
  refine ⟨scanEncodedConstructor, hC, ?_⟩
  intro input
  exact (full_explicit_encoded_reduction input lambda).2.1

/-- Actual proof-side composition in the matching Boolean encoding. -/
theorem boolean_manyOne_trans {A B C : Language}
    (hAB : ManyOne A B) (hBC : ManyOne B C) : ManyOne A C := by
  rcases hAB with ⟨f, hf, hAB⟩
  rcases hBC with ⟨g, hg, hBC⟩
  refine ⟨g ∘ f, Lax218471Proofs.Combinators.comp hf hg, ?_⟩
  intro input
  exact (hAB input).trans (hBC (f input))

/-- The precise missing upstream property. This DEFINITION is not an axiom
    or a claim that our encoded MSSC language has formal hardness evidence. -/
def EncodedSourceHardness : Prop :=
  ∀ A : Language, A ∈ NP → ManyOne A msscSourceLanguage

/-- Complete conditional interface; the hypotheses are the existing OPEN
    obligations, not newly assumed scientific premises. In particular the
    supplied parser/pair-converter does not instantiate hC or hV. -/
theorem full_carta_NPComplete_conditional (lambda : ℝ)
    (hC : Nonempty ConstructorMachineWitness)
    (hV : Nonempty VerifierMachineWitness)
    (hSource : EncodedSourceHardness) : NPComplete (cartaTargetLanguage lambda) := by
  refine ⟨cartaTarget_in_NP_of_verifier lambda hV, ?_⟩
  intro A hA
  exact boolean_manyOne_trans (hSource A hA) (full_carta_manyOne_of_constructor lambda hC)

/- This file does not invoke Cook-Levin itself. A proof network whose raw
theorems mention concept axioms must first be explicitly closed or replaced;
ordinary import of a file named "Proofs" is not evidence of such closure.
No unconditional NP-completeness or verified source theorem is claimed.
The separate general-DAG dynamic program and original stochastic cellular
identification problems remain outside this conditional restricted-star
interface and remain open in their previously recorded scopes.
-/

end PolytomyReductionModel
