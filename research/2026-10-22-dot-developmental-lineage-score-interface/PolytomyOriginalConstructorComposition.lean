/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The ORIGINAL external constructor is now supplied by source terms for
BOTH concrete all-input factors and the inspected proof-side composition
theorem. Independent target verifier and source encoded hardness remain
explicit dependencies of the full NP-completeness statement.
-/
import PolytomyOriginalNormalRecordMachine

namespace PolytomyReductionModel

/-- Composes the actual original normalizer and actual downstream
machine, then uses the ALL-input BYTE-EXACT original factorization.
No arbitrary polytime-function premise remains in this constructor term. -/
theorem originalConstructorMachine_proposed : Nonempty ConstructorMachineWitness :=
  original_constructor_of_normal_record_machine ⟨originalNormalRecordPoly⟩

/-- Whole original semantic and independent-certificate endpoint,
retained alongside the new source-only constructor machine term. -/
theorem original_constructor_machine_full_endpoint (input : List Bool) (lambda : ℝ) :
    Nonempty ConstructorMachineWitness ∧
      (normalizedSource input).length ≤ unaryNormalSizeBound input.length ∧
      (normalRecordConstructor (normalizedSource input)).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (normalRecordConstructor (normalizedSource input)) lambda) ∧
      (EncodedTargetCartaDecision (normalRecordConstructor (normalizedSource input)) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (normalRecordConstructor (normalizedSource input)).length ∧
          boundedEncodedTarget (normalRecordConstructor (normalizedSource input)) cert = true) :=
  ⟨originalConstructorMachine_proposed, original_normalizer_full_reduction_endpoint input lambda⟩

/-- STILL CONDITIONAL. The independent original target verifier and a
compatible encoded-source hardness theorem are not supplied here.
All source terms in this file also await actual elaboration/kernel review. -/
theorem full_carta_NPComplete_after_original_constructor_conditional (lambda : ℝ)
    (hVerifier : Nonempty VerifierMachineWitness) (hSource : EncodedSourceHardness) :
    Lax429075.Reductions.NPComplete (cartaTargetLanguage lambda) :=
  full_carta_NPComplete_conditional lambda originalConstructorMachine_proposed hVerifier hSource

/- The SAME external SourceBitMSSCDecision, EncodedTargetCartaDecision,
all independently admissible joining refinements, compatible potency
labels and actual D_lambda score are retained. The constructor computes
neither an optimal ordering nor a source witness. An independent target
certificate is still checked on its own target data, not by recovering a
hidden MSSC instance. No biological/global-DAG closure, historical novelty,
execution, successful compilation or verified certificate is claimed.
-/

end PolytomyReductionModel
