import E8DeterministicTopKCertificate
import E8CertificateStability
import E8ExactResidualMass
import E8GridTracebackBridge
import UnifiedLean.Source.E8SCFG2BEOwnership

/-! Reuse of completed conditional RNA results. Every original hypothesis is
retained. These exports neither assume an actual C++ trace admission nor
turn a finite grid approximation into an exact or independent RNA sampler. -/
noncomputable section
namespace ResearchCommons.Claims.RNA
abbrev interval_top_k := @E8DeterministicTopKCertificate.interval_certificate_topK
abbrev empirical_top_k := @E8DeterministicTopKCertificate.empirical_radius_topK
abbrev anytime_top_k := @E8DeterministicTopKCertificate.anytime_empirical_radius_topK
abbrev discrepancy_top_k := @E8CertificateStability.widened_certificate_topK
abbrev strict_gap_certificate := @E8CertificateStability.true_gap_implies_certificate
abbrev residual_top_k := @E8ExactResidualMass.exact_residual_topK
abbrev residual_conservation := @E8ExactResidualMass.normalized_residual_eq_one_sub_selected
abbrev midpoint_branch_tv := @E8MidpointProductionKernel.gridKernel_TV
abbrev continuous_branch := @E8MidpointProductionKernel.continuous_weight_kernel
abbrev midpoint_trace_error := @E8GridTracebackBridge.grid_trace_observable_error
abbrev midpoint_class_error := @E8GridTracebackBridge.unambiguous_grid_class_error
abbrev source_event_coordinates := @UnifiedLean.Source.E8SCFG2RootEventDecoder.eventFromKey_exact_coordinates
abbrev local_schema_root_bound := @UnifiedLean.Source.E8SCFG2RootEventDecoder.child_upper_from_local_guard
abbrev bounded_root_events := @UnifiedLean.Source.E8SCFG2RootEventDecoder.rootEvents
abbrev be_root_ownership := @UnifiedLean.Source.E8SCFG2BEOwnership.root_tree_be_owned
end ResearchCommons.Claims.RNA
