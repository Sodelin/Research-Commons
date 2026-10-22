/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Keep the complete ORIGINAL complexity interface after supplying proposed
normalizer machine terms. The downstream constructor/checker and encoded
hardness remain explicit unresolved hypotheses, not hidden axioms.
-/
import PolytomyNormalizerMachine
import PolytomyClassicalNPInterface

namespace PolytomyReductionModel

/-- The remaining total downstream function, on ALL intermediate words.
    This is a definition of an OPEN obligation, not a witness. -/
abbrev NormalRecordMachineWitness :=
  Turing.TM2ComputableInPolyTime (fun bits : List Bool => bits)
    (fun bits : List Bool => bits) normalRecordConstructor

theorem original_constructor_of_normal_record_machine
    (hDownstream : Nonempty NormalRecordMachineWitness) : Nonempty ConstructorMachineWitness := by
  have h := Lax218471Proofs.Combinators.comp ⟨originalNormalizerPoly⟩ hDownstream
  have heq : normalRecordConstructor ∘ normalizedSource = scanEncodedConstructor := by
    funext bits
    exact normalized_constructor_original bits
  simpa only [heq] using h

/-- Full finite semantic endpoint is retained alongside the concrete
    source-proposed normalizer, without claiming the constructor finished. -/
theorem original_normalizer_full_reduction_endpoint (input : List Bool) (lambda : ℝ) :
    (normalizedSource input).length ≤ unaryNormalSizeBound input.length ∧
      (normalRecordConstructor (normalizedSource input)).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (normalRecordConstructor (normalizedSource input)) lambda) ∧
      (EncodedTargetCartaDecision (normalRecordConstructor (normalizedSource input)) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (normalRecordConstructor (normalizedSource input)).length ∧
          boundedEncodedTarget (normalRecordConstructor (normalizedSource input)) cert = true) :=
  full_reduction_with_unary_normal_form input lambda

/-- Still CONDITIONAL: the three uninhabited original full-claim
    dependencies survive the normalizer advance. No broad closure. -/
theorem full_carta_NPComplete_after_normalizer_conditional (lambda : ℝ)
    (hDownstream : Nonempty NormalRecordMachineWitness)
    (hVerifier : Nonempty VerifierMachineWitness)
    (hSource : EncodedSourceHardness) :
    Lax429075.Reductions.NPComplete (cartaTargetLanguage lambda) :=
  full_carta_NPComplete_conditional lambda
    (original_constructor_of_normal_record_machine hDownstream) hVerifier hSource

/- The conditional result targets the same original actual D_lambda
decision problem over all independently admissible joining refinements
and compatible labels, with the existing external Boolean encodings.
No source hardness axiom, generic concept-side polytime axiom, new target
language, biological stochastic model or execution evidence is introduced.
-/

end PolytomyReductionModel
