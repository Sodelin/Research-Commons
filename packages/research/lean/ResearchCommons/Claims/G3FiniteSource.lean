import G7ControlledWordPolynomial
import G7ActualExactLawResponses
import G7EffectiveWordCoefficients

/-! Fixed-source polynomial components of CB-G3-001 (reuse rank12).
All aliases retain their full original types. One original natural bank is
shared across masks, outputs and history. Physical interval dependencies,
calendar order, legal readout and Nonempty completion hypotheses remain.
No RCF backend, exhaustive admission/enumeration or terminal NO is added. -/
set_option autoImplicit false
noncomputable section
namespace ResearchCommons.Claims.G3FiniteSource

abbrev fixed_controlled_word_coefficients :=
  @GProgram.G7.ControlledWordPolynomial.actual_controlled_word_polynomial

abbrev completed_controlled_source_readout :=
  @GProgram.G7.ActualExactLawResponses.actual_controlled_unranked_readout_polynomial

abbrev single_source_joint_response :=
  @GProgram.G7.ActualExactLawResponses.actual_base_vector_eq_polynomial

abbrev same_source_history_equations :=
  @GProgram.G7.ActualExactLawResponses.actual_history_consistency_iff_polynomial

abbrev constructive_word_rows :=
  @GProgram.G7.EffectiveWordCoefficients.wordRows_actual

abbrev constructive_natural_word_rows :=
  @GProgram.G7.EffectiveWordCoefficients.naturalWordRows_actual

end ResearchCommons.Claims.G3FiniteSource
