-- Public declaration interface, not a new proof or algorithm.
import Lean.Util.CollectAxioms
import Lean
import AllLevelParameterDomain
import AncestryObservation
import CMFullMomentUniqueness
import CanonicalTheta
import ClinicalModels.Audit
import ClinicalModels.PublishedCBT
import ClinicalModels.SourceBridge
import ControlledMemory
import ExactAbstraction
import FiniteGenomeIdentifiability
import FounderMaximal
import HistoryObservation
import MergeHistoryProjection
import NanuqActualNanuqAnchorBridge
import PairingBridge
import PairingCore
import PairingGARG
import PairingObservation
import PedigreeBlockDependence
import PedigreeBlockGraph
import PedigreeBlockModel
import PedigreeBlockObservation
import PedigreeBlockProbability
import PedigreeBlockRecovery
import PredictiveState
import RawNanuq
import RealFounderWindow
import RealSpeciesTheorem
import ResearchCommons.Calibration.RareEvent
import ResearchCommons.Claims.BlockRecovery
import ResearchCommons.Claims.CM
import ResearchCommons.Claims.Causal
import ResearchCommons.Claims.FounderWindow
import ResearchCommons.Claims.G1
import ResearchCommons.Claims.G2
import ResearchCommons.Claims.G3Certificate
import ResearchCommons.Claims.G3FiniteSource
import ResearchCommons.Claims.G4
import ResearchCommons.Claims.G4Observers
import ResearchCommons.Claims.G5
import ResearchCommons.Claims.G6
import ResearchCommons.Claims.G7
import ResearchCommons.Claims.Genome
import ResearchCommons.Claims.Memory
import ResearchCommons.Claims.NANUQ
import ResearchCommons.Claims.Ownership
import ResearchCommons.Claims.RNA
import ResearchCommons.Claims.SequenceFirstOccurrence
import ResearchCommons.Claims.Wong
import ResearchCommons.ExactQuery.Rectangle
import ResearchCommons.ExactQuery.Source
import ResearchCommons.G4.AlgebraicProfile
import ResearchCommons.MSCI.Alignment
import ResearchCommons.MSCI.JC69
import ResearchCommons.MSCI.JC69Measurable
import ResearchCommons.MSCI.JC69Observation
import ResearchCommons.MSCI.JC69Source
import ResearchCommons.MSCI.JC69Tree
import ResearchCommons.MSCI.JC69Unranked
import ResearchCommons.MSCI.KilledClocks
import ResearchCommons.MSCI.RootPair
import ResearchCommons.Menu.FiniteForcing
import ResearchCommons.NANUQ.ContiguousCopies
import ResearchCommons.NANUQ.RawNoise
import ResearchCommons.Numerics.CountPrefix
import SocialScience.Aggregation
import SocialScience.Audit
import SocialScience.Causality
import SocialScience.CollectiveAction
import SocialScience.Identifiability
import SocialScience.Learning
import SocialScience.Measurement
import Solidarity
import SpeciesSeed
import StochasticAbstraction
import StochasticExamples
import ThreeTaxonFiniteEvidence
import ThreeTaxonIdentifiability
import WongAlexander
import WongPredictiveBridge

open Lean Elab Command
namespace ResearchCommons.Generated.ClaimExports
#check @ResearchCommons.Claims.G1.original_class_master_with_sharpness
#check @ResearchCommons.Claims.G2.complete_unranked_all_panel_projectivity
#check @ResearchCommons.Claims.G2.natural_timed_all_panel_projectivity
#check @ResearchCommons.Claims.G2.controlled_timed_all_panel_projectivity
#check @ResearchCommons.Claims.G2.natural_timed_forgetting
#check @ResearchCommons.Claims.G2.controlled_timed_forgetting
#check @ResearchCommons.Claims.G2.registered_timed_all_panel_projectivity
#check @ResearchCommons.Claims.G3FiniteSource.fixed_controlled_word_coefficients
#check @ResearchCommons.Claims.G3FiniteSource.completed_controlled_source_readout
#check @ResearchCommons.Claims.G3FiniteSource.single_source_joint_response
#check @ResearchCommons.Claims.G3FiniteSource.same_source_history_equations
#check @ResearchCommons.Claims.G3FiniteSource.constructive_word_rows
#check @ResearchCommons.Claims.G3FiniteSource.constructive_natural_word_rows
#check @ResearchCommons.Claims.G3Certificate.supported_moment
#check @ResearchCommons.Claims.G3Certificate.supported_atoms_in_supplied_grid
#check @ResearchCommons.Claims.G3Certificate.supplied_common_rows_restrict_supported_bank
#check @ResearchCommons.Claims.G3Certificate.actual_randomized_comb_moment
#check @ResearchCommons.Claims.G3Certificate.supplied_positive_grid_cardinality
#check @ResearchCommons.Claims.G4Observers.current_root_opaque_graft
#check @ResearchCommons.Claims.G4Observers.same_register_and_history
#check @ResearchCommons.Claims.G4Observers.same_exterior_contextual_replacement
#check @ResearchCommons.Claims.G4Observers.entering_current_root_cap
#check @ResearchCommons.Claims.G4Observers.completed_forest_singleton_mass
#check @ResearchCommons.Claims.G4Observers.selected_passive_forest_law
#check @ResearchCommons.Claims.G4Observers.specified_comb_topology_probability
#check @ResearchCommons.Claims.G4.finite_common_menu_responses
#check @ResearchCommons.Claims.G4.ordinary_target_both_responses
#check @ResearchCommons.Claims.G4.ordinary_target_legal_certificate
#check @ResearchCommons.Menu.finite_original_polynomial_equations
#check @ResearchCommons.Menu.finite_original_polynomial_responses
#check @ResearchCommons.Menu.finite_qualified_menu_extension
#check @ResearchCommons.G4.AlgebraicProfile.finite_original_generators
#check @ResearchCommons.G4.AlgebraicProfile.finite_vanishing_equations
#check @ResearchCommons.G4.AlgebraicProfile.finite_response_equations
#check @ResearchCommons.Claims.G5.full_cluster_split_unions
#check @ResearchCommons.Claims.G6.checked_cell_sound
#check @ResearchCommons.Claims.G6.cell_solver_complete
#check @ResearchCommons.Claims.G6.checked_physical_bank
#check @ResearchCommons.Claims.G6.actual_cell_observed_tv
#check @ResearchCommons.Claims.G6.rational_witness_sound
#check @ResearchCommons.Claims.G6.rational_witness_complete
#check @ResearchCommons.Claims.G6.rational_witness_none
#check @ResearchCommons.Claims.G6.ordered_list_refinement
#check @ResearchCommons.Claims.G6.whole_edge_coin_chart
#check @ResearchCommons.Claims.G7.winning_iff_valid_plan
#check @ResearchCommons.Claims.G7.valid_run_identifies
#check @ResearchCommons.Claims.G7.losing_history_pair
#check @ResearchCommons.Claims.G7.total_policy_finite_horizon
#check @ResearchCommons.Claims.G7.rank_budget
#check @ResearchCommons.Claims.G7.actual_original_policy_plan
#check @ResearchCommons.Claims.G7.actual_budget_exclusion
#check @ResearchCommons.Claims.Causal.original_selected_binary_upper
#check @ResearchCommons.Claims.Causal.physical_policy_valid
#check @ResearchCommons.Claims.Causal.physical_policy_identifies
#check @ResearchCommons.Claims.Causal.actual_trek_source_unique
#check @ResearchCommons.Claims.Causal.physical_no_short_plan
#check @ResearchCommons.Claims.Causal.promised_budget_exact
#check @ResearchCommons.Claims.Causal.arbitrary_seed_lower
#check @ResearchCommons.Claims.Causal.no_targets_empty_graph
#check @ResearchCommons.Claims.Causal.no_targets_singleton_class
#check @ResearchCommons.Claims.Causal.no_targets_zero_query
#check @Astra.CommonMoment.nodes_subset_of_equal_sparse_moments
#check @Astra.CommonMoment.moment_on_supergrid
#check @Astra.CommonMoment.atomMass_eq_of_equal_sparse_moments
#check @Astra.CommonMoment.atomMass_eq_of_equal_consecutive_moments
#check @Astra.CommonMoment.all_moments_eq_of_equal_consecutive_moments
#check @ResearchCommons.Claims.CM.cap_five_separation
#check @ResearchCommons.Claims.CM.grouped_rational_law
#check @ResearchCommons.Claims.CM.grouped_rational_moments
#check @ResearchCommons.Claims.SequenceFirstOccurrence.plus_first_occurrence
#check @ResearchCommons.Claims.SequenceFirstOccurrence.even_minus_first_occurrence
#check @ResearchCommons.Claims.SequenceFirstOccurrence.odd_minus_first_occurrence
#check @ResearchCommons.Claims.SequenceFirstOccurrence.plus_all_starts
#check @ResearchCommons.Claims.SequenceFirstOccurrence.even_minus_all_starts
#check @ResearchCommons.Claims.SequenceFirstOccurrence.canonical_three_families
#check @ResearchCommons.Claims.RNA.represented_scanner_pipeline
#check @ResearchCommons.Claims.RNA.original_scaffold_partner
#check @ResearchCommons.Claims.RNA.normalized_root_carrier
#check @ResearchCommons.Claims.NANUQ.rooted_cap_distinct_set_and_mean
#check @ResearchCommons.Claims.NANUQ.repeated_label_anchor
#check @ResearchCommons.Claims.NANUQ.weighted_anchor_composition
#check @ResearchCommons.Claims.NANUQ.unit_anchor_composition
#check @ResearchCommons.Claims.NANUQ.opened_choice_distinct_set_and_mean
#check @ResearchCommons.Claims.NANUQ.galled_cap_opened_family_and_mean
#check @ResearchCommons.Claims.NANUQ.actual_opened_curve_drawing
#check @ResearchCommons.Claims.NANUQ.actual_opened_curve_subset
#check @ResearchCommons.Claims.NANUQ.original_curve_adapter_roundtrip
#check @ResearchCommons.Claims.NANUQ.actual_opened_planar_curves
#check @ResearchCommons.Claims.NANUQ.actual_opened_planar_subset
#check @ResearchCommons.Claims.NANUQ.actual_source_cycle_circle
#check @ResearchCommons.MSCI.actual_totalRate_strict_merger
#check @ResearchCommons.MSCI.actual_merger_charge_count_nonincreasing
#check @ResearchCommons.MSCI.actual_killedRate_strict_merger
#check @ResearchCommons.MSCI.actual_merger_killed_difference_positive
#check @ResearchCommons.MSCI.JC69.character_add
#check @ResearchCommons.MSCI.JC69.probability_semigroup
#check @ResearchCommons.MSCI.JC69.fourier_transfer
#check @ResearchCommons.MSCI.JC69.kernel_probability
#check @ResearchCommons.MSCI.JC69.normalized_generator
#check @ResearchCommons.MSCI.JC69.uniform_root_pair_probability
#check @ResearchCommons.MSCI.JC69.clock_pair_correlation
#check @ResearchCommons.MSCI.JC69.clock_survival_timeOfSurvival
#check @ResearchCommons.MSCI.JC69.pair_time_decoder
#check @ResearchCommons.MSCI.JC69.character_sum
#check @ResearchCommons.MSCI.JC69.actual_current_tree_character
#check @ResearchCommons.MSCI.JC69Tree.likelihood_sum
#check @ResearchCommons.MSCI.JC69Tree.kernel_probability
#check @ResearchCommons.MSCI.JC69Tree.tree_fourier
#check @ResearchCommons.MSCI.JC69Tree.root_fourier
#check @ResearchCommons.MSCI.JC69Tree.totalCharge_eq_original_leaves
#check @ResearchCommons.MSCI.JC69Tree.label_pattern_character
#check @ResearchCommons.MSCI.JC69Tree.original_pattern_readout_injective
#check @ResearchCommons.MSCI.JC69Tree.actual_single_root_covers_original_copies
#check @ResearchCommons.MSCI.JC69Tree.actual_clock_survivals_admitted
#check @ResearchCommons.MSCI.JC69Tree.actual_decoded_chronology
#check @ResearchCommons.MSCI.JC69Tree.actual_tree_kernel_probability
#check @ResearchCommons.MSCI.JC69Tree.locus_likelihood_sum
#check @ResearchCommons.MSCI.JC69Tree.locus_fourier
#check @ResearchCommons.MSCI.JC69Observation.originalPatternEquiv
#check @ResearchCommons.MSCI.JC69Observation.actual_original_label_probability
#check @ResearchCommons.MSCI.JC69Observation.actual_original_label_fourier
#check @ResearchCommons.MSCI.JC69Measurable.root_age_measurable
#check @ResearchCommons.MSCI.JC69Measurable.clock_likelihood_measurable
#check @ResearchCommons.MSCI.JC69Measurable.root_probability_measurable
#check @ResearchCommons.MSCI.JC69Measurable.decoded_probability_measurable
#check @ResearchCommons.MSCI.JC69Measurable.decoded_locus_measurable
#check @ResearchCommons.MSCI.JC69Measurable.actual_original_probability_measurable
#check @ResearchCommons.MSCI.JC69Source.conditional_kernel_probability
#check @ResearchCommons.MSCI.JC69Source.conditional_mass_measurable
#check @ResearchCommons.MSCI.JC69Source.conditional_locus_mass_measurable
#check @ResearchCommons.MSCI.JC69Source.original_point_measurable
#check @ResearchCommons.MSCI.JC69Source.actual_original_point_support
#check @ResearchCommons.MSCI.JC69Source.actual_source_locus_normalized
#check @ResearchCommons.MSCI.JC69Source.actual_source_locus_integral
#check @ResearchCommons.MSCI.JC69Source.registered_locus_probability
#check @ResearchCommons.MSCI.JC69Unranked.unordered_decoration_transport
#check @ResearchCommons.MSCI.JC69Unranked.decoded_root_probability_unordered
#check @ResearchCommons.MSCI.JC69Unranked.completed_forest_singleton
#check @ResearchCommons.MSCI.JC69Unranked.conditional_kernel_same_timed_observation
#check @ResearchCommons.MSCI.JC69Unranked.conditional_locus_same_timed_observation
#check @ResearchCommons.MSCI.Alignment.mem_allAlignments_iff
#check @ResearchCommons.MSCI.Alignment.allAlignments_nonempty_iff
#check @ResearchCommons.MSCI.Alignment.matches_refl
#check @ResearchCommons.MSCI.Alignment.matches_trans
#check @ResearchCommons.MSCI.RootPair.moment_formula
#check @ResearchCommons.MSCI.RootPair.scaled_moments_injective
#check @ResearchCommons.MSCI.RootPair.moments_injective
#check @ResearchCommons.Numerics.CountPrefix.term_nonneg
#check @ResearchCommons.Numerics.CountPrefix.prefix_pos
#check @ResearchCommons.Numerics.CountPrefix.prefix_le_exp
#check @ResearchCommons.Numerics.CountPrefix.exp_le_upper
#check @ResearchCommons.Numerics.CountPrefix.normalized_prefix_sum
#check @ResearchCommons.Numerics.CountPrefix.lostMass_nonneg
#check @ResearchCommons.Numerics.CountPrefix.lostMass_le_deficit
#check @ResearchCommons.Numerics.CountPrefix.certified_error
#check @Nanuq.Canonical.theta_source
#check @Nanuq.Canonical.theta_weighted
#check @Nanuq.Canonical.theta_exact_quartet_mean
#check @Nanuq.Source.RootedBinary.rawRho_valid
#check @Nanuq.Source.RootedBinary.rawRho_nonneg
#check @Nanuq.Source.RootedBinary.rawRho_witness_symmetric
#check @Nanuq.Source.RootedBinary.rawRho_endpoint_symmetric
#check @Nanuq.Source.RootedBinary.rawNanuq_symmetric
#check @Nanuq.Source.RootedBinary.rawNanuq_positive
#check @Nanuq.Source.RootedBinary.rawNanuq_ordered_formula
#check @Nanuq.Source.RootedBinary.actualQuartetData_witness_symmetric
#check @Nanuq.Source.RootedBinary.actual_weightedNanuq_eq_anchor
#check @Nanuq.Source.RootedBinary.actual_weightedNanuq_blob_composition
#check @Nanuq.Source.RootedBinary.actual_sourceNanuq_blob_composition
#check @ResearchCommons.Claims.NANUQ.raw_tensor_eq_actual
#check @ResearchCommons.Claims.NANUQ.raw_weighted_blob_composition
#check @ResearchCommons.Claims.NANUQ.raw_source_blob_composition
#check @ResearchCommons.ExactQuery.Rectangle.interval_displays_iff_rectangle
#check @ResearchCommons.ExactQuery.Rectangle.split_union_rectangle_oracle
#check @ResearchCommons.ExactQuery.Rectangle.rectangle_left_partition
#check @ResearchCommons.ExactQuery.Rectangle.rectangle_right_partition
#check @ResearchCommons.ExactQuery.Rectangle.rectangle_singleton
#check @ResearchCommons.ExactQuery.Rectangle.wrap_query_singleton
#check @ResearchCommons.ExactQuery.Source.OriginalRepresentative
#check @ResearchCommons.ExactQuery.Source.OriginalCircle
#check @ResearchCommons.ExactQuery.Source.original_circle_identity
#check @ResearchCommons.ExactQuery.Source.original_split_target
#check @ResearchCommons.ExactQuery.Source.original_split_evaluator
#check @ResearchCommons.ExactQuery.Source.original_source_orders
#check @ResearchCommons.ExactQuery.Source.original_orders_normalized
#check @ResearchCommons.ExactQuery.Source.original_bounded_targets_and_circles
#check @ResearchCommons.ExactQuery.Source.original_quartet_splice
#check @ResearchCommons.ExactQuery.Rectangle.triangle_mid_partition
#check @ResearchCommons.ExactQuery.Rectangle.triangle_mid_disjoint
#check @ResearchCommons.ExactQuery.Rectangle.seed_covered_iff_triangle
#check @ResearchCommons.ExactQuery.Rectangle.all_candidates_covered
#check @ResearchCommons.ExactQuery.Rectangle.wrap_and_nonwrap_disjoint
#check @ResearchCommons.ExactQuery.Rectangle.emitted_roots_have_distinct_query_positions
#check @Nanuq.AllLevelParameters.all_rows_iff_exact_domain
#check @Nanuq.AllLevelParameters.four_taxon_rows_iff_box
#check @Nanuq.AllLevelParameters.four_taxon_certificate_insufficient
#check @Nanuq.AllLevelParameters.four_taxon_certificate_misses_adjacent_lower_bound
#check @Nanuq.AllLevelParameters.original_and_modified_in_domain
#check @ResearchCommons.NANUQ.ContiguousCopies.extreme_bounds
#check @ResearchCommons.NANUQ.ContiguousCopies.same_interval_side_extreme
#check @ResearchCommons.NANUQ.ContiguousCopies.extreme_card_le_two
#check @ResearchCommons.NANUQ.ContiguousCopies.cut_quartet_extremes_iff
#check @ResearchCommons.NANUQ.ContiguousCopies.selection_side_extremes
#check @ResearchCommons.NANUQ.ContiguousCopies.cut_split_extremes_iff
#check @ResearchCommons.NANUQ.RawNoise.distinct_mean_twice_integer
#check @ResearchCommons.NANUQ.RawNoise.source_nanuq_integer
#check @ResearchCommons.NANUQ.RawNoise.raw_source_integer
#check @ResearchCommons.NANUQ.RawNoise.round_of_abs_sub_lt_half
#check @ResearchCommons.NANUQ.RawNoise.integer_matrix_rounding
#check @ResearchCommons.NANUQ.RawNoise.raw_source_rounding
#check @SocialScience.Identifiability.equivalent_refl
#check @SocialScience.Identifiability.equivalent_symm
#check @SocialScience.Identifiability.equivalent_trans
#check @SocialScience.Identifiability.restrict_design
#check @SocialScience.Identifiability.more_probes_preserve_identification
#check @SocialScience.Identifiability.postprocess_preserves_equivalence
#check @SocialScience.Identifiability.baseline_ambiguous
#check @SocialScience.Identifiability.baseline_not_identified
#check @SocialScience.Identifiability.both_probes_identify
#check @SocialScience.Measurement.common_intercept_preserves_order
#check @SocialScience.Measurement.common_intercept_preserves_difference
#check @SocialScience.Measurement.shift_invariance
#check @SocialScience.Measurement.population_shift_invariance
#check @SocialScience.Measurement.known_intercept_identifies
#check @SocialScience.Measurement.anchor_identifies_intercept
#check @SocialScience.Measurement.group_intercepts_can_reverse_order
#check @SocialScience.Measurement.bounded_bias_interval
#check @SocialScience.Measurement.difference_exceeding_bias_identifies_order
#check @SocialScience.Learning.fits_empty
#check @SocialScience.Learning.fits_cons_iff
#check @SocialScience.Learning.fits_append_iff
#check @SocialScience.Learning.more_evidence_narrows_models
#check @SocialScience.Learning.truth_survives_correct_label
#check @SocialScience.Learning.distinguishing_query_eliminates_rival
#check @SocialScience.Learning.conflicting_labels_impossible
#check @SocialScience.Learning.incorrect_label_excludes_truth
#check @SocialScience.Learning.duplicate_evidence_same_models
#check @SocialScience.Causality.observational_equivalence
#check @SocialScience.Causality.intervention_disagreement
#check @SocialScience.Causality.treatment_effect_numerator
#check @SocialScience.Causality.common_cause_numerator
#check @SocialScience.Causality.no_universal_observational_estimator
#check @SocialScience.Causality.all_responses_identify
#check @Solidarity.adj_symm
#check @Solidarity.reach_trans
#check @Solidarity.reach_symm
#check @Solidarity.zero_reaches
#check @Solidarity.path_connected
#check @Solidarity.at_most_two_neighbors
#check @Solidarity.unbounded_reachable
#check @Solidarity.membership_nesting
#check @Solidarity.overlapping_memberships
#check @Solidarity.connected_without_trust
#check @Solidarity.cooperation_stable_iff
#check @Solidarity.no_sanction_failure
#check @Solidarity.heterogeneous_cooperation_exists
#check @Solidarity.homogeneous_cooperation_can_fail
#check @Solidarity.symbols_alone_insufficient
#check @Solidarity.mutual_gain
#check @SocialScience.CollectiveAction.adding_members_preserves_feasibility
#check @SocialScience.CollectiveAction.restricting_members_preserves_acceptance
#check @SocialScience.CollectiveAction.union_accepts_iff
#check @SocialScience.CollectiveAction.indispensable_member_withdrawal
#check @SocialScience.CollectiveAction.complementary_pair_feasible
#check @SocialScience.CollectiveAction.no_specialist_alone_feasible
#check @SocialScience.CollectiveAction.aggregate_surplus_not_participation
#check @SocialScience.CollectiveAction.repaired_allocation_ready
#check @SocialScience.CollectiveAction.two_person_budget_iff
#check @SocialScience.CollectiveAction.acceptable_share_interval
#check @SocialScience.Aggregation.reversal_cells_valid
#check @SocialScience.Aggregation.first_stratum_advantage
#check @SocialScience.Aggregation.second_stratum_advantage
#check @SocialScience.Aggregation.pooled_reversal
#check @SocialScience.Aggregation.simpson_reversal
#check @SocialScience.Aggregation.equal_weight_addition_preserves_order
#check @SocialScience.Aggregation.aggregate_cannot_identify_components
#check @SocialScience.Aggregation.recoding_cannot_restore_components
#check @ClinicalModels.PublishedCBT.approach_trajectory
#check @ClinicalModels.PublishedCBT.avoidance_trajectory
#check @ClinicalModels.PublishedCBT.avoidance_observational_equivalence
#check @ClinicalModels.PublishedCBT.avoidance_no_perfect_classifier
#check @ClinicalModels.PublishedCBT.approach_observations_differ
#check @ClinicalModels.PublishedCBT.approach_identifies_state
#check @ClinicalModels.PublishedCBT.safe_columns_total_mass
#check @ClinicalModels.PublishedCBT.danger_columns_total_mass
#check @ClinicalModels.PublishedCBT.safe_columns_nonnegative
#check @ClinicalModels.PublishedCBT.danger_columns_nonnegative
#check @ClinicalModels.PublishedCBT.implicit_mappings_equal_at_tenth
#check @ClinicalModels.PublishedCBT.approach_implicit_equality_iff
#check @ClinicalModels.PublishedCBT.avoidance_implicit_columns_equal
#check @ClinicalModels.PublishedCBT.explicit_prior_weights
#check @ClinicalModels.SourceBridge.source_sensory_columns
#check @ClinicalModels.SourceBridge.source_affective_columns
#check @ClinicalModels.SourceBridge.source_transition_columns
#check @ClinicalModels.SourceBridge.source_implicit_columns
#check @FiniteGenomeIdentifiability.opposite_compatible_completions
#check @FiniteGenomeIdentifiability.no_exact_specieslike_verdict
#check @FiniteGenomeIdentifiability.no_exact_specieslike_decoder
#check @WongAlexander.actual_garg_opposite_infinite_completions
#check @ThreeTaxonIdentifiability.law_nonnegative
#check @ThreeTaxonIdentifiability.law_normalized
#check @ThreeTaxonIdentifiability.unique_maximizer
#check @ThreeTaxonIdentifiability.law_identifiable
#check @ThreeTaxonIdentifiability.boundary_uniform
#check @ThreeTaxonIdentifiability.no_boundary_decoder
#check @ThreeTaxonFiniteEvidence.sampleMass_positive
#check @ThreeTaxonFiniteEvidence.sampleMass_lower_bound
#check @ThreeTaxonFiniteEvidence.finite_sample_support_overlap
#check @ThreeTaxonFiniteEvidence.no_uniform_certain_decoder
#check @ThreeTaxonFiniteEvidence.quantitative_error_witness
#check @ThreeTaxonFiniteEvidence.robust_strict_mode
#check @ThreeTaxonFiniteEvidence.robust_maximizer_recovers
#check @ThreeTaxonFiniteEvidence.half_gap_tie
#check @ResearchCommons.Claims.Genome.law_transport
#check @ResearchCommons.Claims.Genome.evidence_law_identifiable
#check @PairingCore.edge_exact_image
#check @PairingCore.owner_exactly_two
#check @PairingCore.arbitrary_prefix_opposite_iap
#check @PairingCore.constrained_counterexample
#check @PairingCore.founders_exactly_four
#check @PairingCore.parents_opposite_sex
#check @PairingCore.same_copy_sex
#check @PairingCore.exact_edges_do_not_lift_paths
#check @PairingCore.natural_biosphere
#check @PairingCore.no_iap_decoder
#check @PairingGARG.topology_iff
#check @PairingGARG.sample_iff
#check @PairingGARG.nonemptyAnnotations
#check @PairingGARG.uniqueParentAt
#check @PairingGARG.sampleSupported
#check @PairingGARG.atLocus_iff
#check @PairingBridge.code_injective
#check @PairingBridge.finite_topology_iff_genome
#check @PairingBridge.finite_pedigree_exact_image
#check @PairingBridge.extraction_retains_every_edge
#check @PairingBridge.generation_dated_biosphere
#check @PairingObservation.query_coownership
#check @PairingObservation.local_query
#check @PairingObservation.query_formula
#check @PairingObservation.query_mixing
#check @PairingObservation.query_splitting
#check @PairingObservation.observe_eq_iff
#check @PairingObservation.split_observation_eq_iff
#check @PairingObservation.identifies_iap_iff
#check @PairingObservation.no_bounded_sampling_decoder
#check @PairingObservation.observed_positive_not_iap
#check @PairingObservation.even_owner_agreement
#check @PairingObservation.even_owners_equal
#check @PairingObservation.no_even_ownership_decoder
#check @PairingObservation.bounded_identifies_iap_iff
#check @PairingObservation.bounded_iap_iff_one_query
#check @PedigreeBlock.complement_ne
#check @PedigreeBlock.not_share_iff_complement
#check @PedigreeBlock.not_connected_iff_bad
#check @PedigreeBlock.reachable_of_restrict
#check @PedigreeBlock.connected_of_restrict
#check @PedigreeBlock.badEquiv
#check @PedigreeBlock.bad_card
#check @PedigreeBlock.configLaw_probability
#check @PedigreeBlock.configPMF_mass
#check @PedigreeBlock.bad_probability
#check @PedigreeBlock.uniform_pi_event
#check @PedigreeBlock.config_bit_cylinder
#check @PedigreeBlock.fair_bit_singleton
#check @PedigreeBlock.good_probability
#check @PedigreeBlock.familyLaw_probability
#check @PedigreeBlock.family_event_product
#check @PedigreeBlock.families_good_probability
#check @PedigreeBlock.observedShare_iff
#check @PedigreeBlock.observed_path_preserves_family
#check @PedigreeBlock.family_path_iff
#check @PedigreeBlock.recovered_iff_connected
#check @PedigreeBlock.connected_probability
#check @PedigreeBlock.recovered_probability
#check @PedigreeBlock.observationLaw_probability
#check @PedigreeBlock.output_recovery_probability
#check @PedigreeBlock.repeatBlock_share_iff
#check @PedigreeBlock.repeatBlock_connected_iff
#check @PedigreeBlock.repeatedLaw_probability
#check @PedigreeBlock.repeatedLaw_block_marginal
#check @PedigreeBlock.repeatedLaw_connected_eq_one_block
#check @PedigreeBlock.repeatedLaw_connected_probability
#check @ResearchCommons.Claims.BlockRecovery.recovered_of_restrict
#check @ExactAbstraction.exact_factor_iff
#check @ExactAbstraction.exact_factor_unique
#check @ExactAbstraction.trajectory_preservation
#check @ExactAbstraction.compatible_gives_trajectories
#check @PredictiveState.encode_eq_iff
#check @PredictiveState.quotient_observe
#check @PredictiveState.quotient_step
#check @PredictiveState.run_commutes
#check @PredictiveState.exact_refinement_future
#check @PredictiveState.factors_iff
#check @PredictiveState.coarsest_exact
#check @PredictiveState.distinguishing_word
#check @PredictiveState.distinguishable_injective
#check @PredictiveState.distinguishable_card_le
#check @PredictiveState.restrict_actions
#check @PredictiveState.depth_iff_words
#check @PredictiveState.future_depth
#check @PredictiveState.stabilization_complete
#check @PredictiveState.feedback_commutes
#check @PredictiveState.feedback_trajectories
#check @ControlledMemory.cell_commutes
#check @ControlledMemory.history_commutes
#check @ControlledMemory.no_finite_suffix_decoder
#check @ControlledMemory.cross_model_all_words
#check @ControlledMemory.cross_model_all_times
#check @ControlledMemory.probe_refinement_factor
#check @ControlledMemory.cell_future_iff
#check @ControlledMemory.history_future_iff
#check @ControlledMemory.at_least_four
#check @ControlledMemory.memory_required_at_fixed_visible
#check @ControlledMemory.reachable_probe_witness
#check @ControlledMemory.all_summaries_reachable
#check @ControlledMemory.passive_visible_exact
#check @ControlledMemory.passive_future_iff
#check @ControlledMemory.changed_probe_refutes_summary
#check @HistoryObservation.stable_type_matched_history_null
#check @HistoryObservation.selection_no_history_effect
#check @HistoryObservation.selected_history_perfectly_predicts
#check @HistoryObservation.arbitrary_delayed_distinction
#check @AncestryObservation.restriction_commutes
#check @AncestryObservation.restriction_all_words
#check @AncestryObservation.sample_query_factors
#check @AncestryObservation.no_universal_sample_expansion
#check @WongPredictiveBridge.extracted_is_compress
#check @WongPredictiveBridge.actual_garg_restriction_all_words
#check @WongPredictiveBridge.no_global_iap_decoder
#check @MergeHistoryProjection.split_preserves_legal
#check @MergeHistoryProjection.adjacent_merge_histories
#check @MergeHistoryProjection.legal_histories
#check @MergeHistoryProjection.admissible_splits_with_spectator
#check @MergeHistoryProjection.same_current_partition
#check @MergeHistoryProjection.distinct_restored_partitions
#check @MergeHistoryProjection.no_exact_partition_model
#check @MergeHistoryProjection.no_partition_only_admissible_split
#check @StochasticAbstraction.exact_iff
#check @StochasticAbstraction.exact_unique
#check @StochasticAbstraction.exact_iff_all_initial_laws
#check @StochasticAbstraction.runLaw_preserves
#check @StochasticAbstraction.runLaw_initial
#check @StochasticAbstraction.experiment_preserves
#check @StochasticAbstraction.experimentLaw_preserves
#check @StochasticAbstraction.observationPolicy_factors
#check @StochasticAbstraction.observed_experiment_law
#check @StochasticAbstraction.observed_statistic_preserves
#check @StochasticAbstraction.deterministic_instance
#check @StochasticAbstraction.joint_sensor_exact
#check @StochasticAbstraction.joint_sensor_observed_law
#check @StochasticExamples.matching_marginals_different_joint
#check @StochasticExamples.c_is_mixture
#check @StochasticExamples.same_all_traces
#check @StochasticExamples.no_trace_based_test_separates
#check @StochasticExamples.same_profile
#check @StochasticExamples.profile_pushes_differ
#check @StochasticExamples.no_commuting_profile_kernel
#check @ResearchCommons.Calibration.sample_mass_nonnegative
#check @ResearchCommons.Calibration.sample_mass_normalized
#check @ResearchCommons.Calibration.all_zero_mass
#check @ResearchCommons.Calibration.miss_positive
#check @ResearchCommons.Calibration.miss_le_one
#check @ResearchCommons.Calibration.null_error_at_zero
#check @ResearchCommons.Calibration.all_zero_error_contribution
#check @ResearchCommons.Calibration.sum_error_lower
#check @ResearchCommons.Calibration.worst_error_lower
#check @ResearchCommons.Calibration.threshold_rule_errors
#check @ResearchCommons.Calibration.balanced_rule_errors
#check @ResearchCommons.Calibration.sharp_sum_error
#check @ResearchCommons.Calibration.sharp_worst_error
#check @ResearchCommons.Calibration.sharp_equal_prior_error
#check @ResearchCommons.Calibration.no_finite_certain_decision
#check @ResearchCommons.Calibration.zero_trials_miss
#check @ResearchCommons.Calibration.fixed_rate_arbitrarily_accurate
#check @ResearchCommons.Calibration.miss_lower_rate_bound
#check @ResearchCommons.Calibration.bernoulli_lower
#check @ResearchCommons.Calibration.no_uniform_finite_guarantee
#check @RealFounderWindow.nonempty_has_earliest
#check @RealFounderWindow.earliest_is_founder
#check @RealFounderWindow.founder_covers
#check @RealFounderWindow.window_finite_founders
#check @RealFounderWindow.commonAncestor_window
#check @RealFounderWindow.window_nonnegative
#check @RealFounderWindow.window_directed_union
#check @RealFounderWindow.directed_union_finite_founders
#check @FounderMaximal.directed_union_connected
#check @FounderMaximal.union_reflection
#check @FounderMaximal.windowSpecies_directed_union
#check @FounderMaximal.maximal_extension_of_directed_union
#check @FounderMaximal.maximal_window_extension_ordered
#check @SpeciesSeed.anchored_minimal_exists
#check @SpeciesSeed.productivePart_convex
#check @SpeciesSeed.productivePart_internal_infinite
#check @SpeciesSeed.minimal_anchored_iap
#check @SpeciesSeed.exists_anchored_seed
#check @SpeciesSeed.exists_seed
#check @RealSpeciesTheorem.windowSpecies_iff
#check @RealSpeciesTheorem.push_maximal
#check @RealSpeciesTheorem.maximal_window_extension
#check @RealSpeciesTheorem.every_vertex_has_seed
#check @RealSpeciesTheorem.every_vertex_in_maximal_real_window
#check @ResearchCommons.Claims.Wong.intrinsic_count_time_law
#check @ResearchCommons.Claims.Wong.measurable_valid_history
#check @ResearchCommons.Claims.Wong.actual_history_support
#check @ResearchCommons.Claims.RNA.admitted_gamma_class_probability
#check @ResearchCommons.Claims.RNA.admitted_positive_output_bijection
#check @ResearchCommons.Claims.RNA.observed_ordered_derivation_sum
#check @ResearchCommons.Claims.RNA.scheduled_ordered_derivation_sum
#check @ResearchCommons.Claims.RNA.valid_active_ordered_fold
#check @ResearchCommons.Claims.RNA.interval_top_k
#check @ResearchCommons.Claims.RNA.anytime_top_k
#check @ResearchCommons.Claims.RNA.discrepancy_top_k
#check @ResearchCommons.Claims.RNA.strict_gap_certificate
#check @ResearchCommons.Claims.RNA.residual_top_k
#check @ResearchCommons.Claims.RNA.residual_conservation
#check @ResearchCommons.Claims.RNA.source_event_coordinates
#check @ResearchCommons.Claims.RNA.local_schema_root_bound
#check @ResearchCommons.Claims.RNA.bounded_root_events
#check @ResearchCommons.Claims.RNA.be_root_ownership
#check @ResearchCommons.Claims.RNA.midpoint_branch_tv
#check @ResearchCommons.Claims.RNA.continuous_branch
#check @ResearchCommons.Claims.RNA.midpoint_trace_error
#check @ResearchCommons.Claims.RNA.midpoint_class_error
#check @ResearchCommons.Claims.RNA.local_sample_v_slots
#check @ResearchCommons.Claims.RNA.local_sample_v_grid_error
#check @ResearchCommons.Claims.RNA.supported_wrapper_rank
run_cmd do
  let environment ← getEnv
  let requested : Array (String × Name × String) := #[
    ("CB-G1-001", ``ResearchCommons.Claims.G1.original_class_master_with_sharpness, "ResearchCommons.Claims.G1"),
    ("CB-G2-001", ``ResearchCommons.Claims.G2.complete_unranked_all_panel_projectivity, "ResearchCommons.Claims.G2"),
    ("CB-G2-001", ``ResearchCommons.Claims.G2.natural_timed_all_panel_projectivity, "ResearchCommons.Claims.G2"),
    ("CB-G2-001", ``ResearchCommons.Claims.G2.controlled_timed_all_panel_projectivity, "ResearchCommons.Claims.G2"),
    ("CB-G2-001", ``ResearchCommons.Claims.G2.natural_timed_forgetting, "ResearchCommons.Claims.G2"),
    ("CB-G2-001", ``ResearchCommons.Claims.G2.controlled_timed_forgetting, "ResearchCommons.Claims.G2"),
    ("CB-G2-001", ``ResearchCommons.Claims.G2.registered_timed_all_panel_projectivity, "ResearchCommons.Claims.G2"),
    ("CB-G3-001", ``ResearchCommons.Claims.G3FiniteSource.fixed_controlled_word_coefficients, "ResearchCommons.Claims.G3FiniteSource"),
    ("CB-G3-001", ``ResearchCommons.Claims.G3FiniteSource.completed_controlled_source_readout, "ResearchCommons.Claims.G3FiniteSource"),
    ("CB-G3-001", ``ResearchCommons.Claims.G3FiniteSource.single_source_joint_response, "ResearchCommons.Claims.G3FiniteSource"),
    ("CB-G3-001", ``ResearchCommons.Claims.G3FiniteSource.same_source_history_equations, "ResearchCommons.Claims.G3FiniteSource"),
    ("CB-G3-001", ``ResearchCommons.Claims.G3FiniteSource.constructive_word_rows, "ResearchCommons.Claims.G3FiniteSource"),
    ("CB-G3-001", ``ResearchCommons.Claims.G3FiniteSource.constructive_natural_word_rows, "ResearchCommons.Claims.G3FiniteSource"),
    ("CB-G3-002", ``ResearchCommons.Claims.G3Certificate.supported_moment, "ResearchCommons.Claims.G3Certificate"),
    ("CB-G3-002", ``ResearchCommons.Claims.G3Certificate.supported_atoms_in_supplied_grid, "ResearchCommons.Claims.G3Certificate"),
    ("CB-G3-002", ``ResearchCommons.Claims.G3Certificate.supplied_common_rows_restrict_supported_bank, "ResearchCommons.Claims.G3Certificate"),
    ("CB-G3-002", ``ResearchCommons.Claims.G3Certificate.actual_randomized_comb_moment, "ResearchCommons.Claims.G3Certificate"),
    ("CB-G3-002", ``ResearchCommons.Claims.G3Certificate.supplied_positive_grid_cardinality, "ResearchCommons.Claims.G3Certificate"),
    ("CB-G4-001", ``ResearchCommons.Claims.G4Observers.current_root_opaque_graft, "ResearchCommons.Claims.G4Observers"),
    ("CB-G4-001", ``ResearchCommons.Claims.G4Observers.same_register_and_history, "ResearchCommons.Claims.G4Observers"),
    ("CB-G4-001", ``ResearchCommons.Claims.G4Observers.same_exterior_contextual_replacement, "ResearchCommons.Claims.G4Observers"),
    ("CB-G4-001", ``ResearchCommons.Claims.G4Observers.entering_current_root_cap, "ResearchCommons.Claims.G4Observers"),
    ("CB-G4-001", ``ResearchCommons.Claims.G4Observers.completed_forest_singleton_mass, "ResearchCommons.Claims.G4Observers"),
    ("CB-G4-001", ``ResearchCommons.Claims.G4Observers.selected_passive_forest_law, "ResearchCommons.Claims.G4Observers"),
    ("CB-G4-001", ``ResearchCommons.Claims.G4Observers.specified_comb_topology_probability, "ResearchCommons.Claims.G4Observers"),
    ("CB-G4-002", ``ResearchCommons.Claims.G4.finite_common_menu_responses, "ResearchCommons.Claims.G4"),
    ("CB-G4-003", ``ResearchCommons.Claims.G4.ordinary_target_both_responses, "ResearchCommons.Claims.G4"),
    ("CB-G4-003", ``ResearchCommons.Claims.G4.ordinary_target_legal_certificate, "ResearchCommons.Claims.G4"),
    ("CB-G4-004", ``ResearchCommons.Menu.finite_original_polynomial_equations, "ResearchCommons.Menu.FiniteForcing"),
    ("CB-G4-004", ``ResearchCommons.Menu.finite_original_polynomial_responses, "ResearchCommons.Menu.FiniteForcing"),
    ("CB-G4-004", ``ResearchCommons.Menu.finite_qualified_menu_extension, "ResearchCommons.Menu.FiniteForcing"),
    ("CB-G4-006", ``ResearchCommons.G4.AlgebraicProfile.finite_original_generators, "ResearchCommons.G4.AlgebraicProfile"),
    ("CB-G4-006", ``ResearchCommons.G4.AlgebraicProfile.finite_vanishing_equations, "ResearchCommons.G4.AlgebraicProfile"),
    ("CB-G4-006", ``ResearchCommons.G4.AlgebraicProfile.finite_response_equations, "ResearchCommons.G4.AlgebraicProfile"),
    ("CB-G5-001", ``ResearchCommons.Claims.G5.full_cluster_split_unions, "ResearchCommons.Claims.G5"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.checked_cell_sound, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.cell_solver_complete, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.checked_physical_bank, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.actual_cell_observed_tv, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.rational_witness_sound, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.rational_witness_complete, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.rational_witness_none, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.ordered_list_refinement, "ResearchCommons.Claims.G6"),
    ("CB-G6-001", ``ResearchCommons.Claims.G6.whole_edge_coin_chart, "ResearchCommons.Claims.G6"),
    ("CB-G7-001", ``ResearchCommons.Claims.G7.winning_iff_valid_plan, "ResearchCommons.Claims.G7"),
    ("CB-G7-001", ``ResearchCommons.Claims.G7.valid_run_identifies, "ResearchCommons.Claims.G7"),
    ("CB-G7-001", ``ResearchCommons.Claims.G7.losing_history_pair, "ResearchCommons.Claims.G7"),
    ("CB-G7-001", ``ResearchCommons.Claims.G7.total_policy_finite_horizon, "ResearchCommons.Claims.G7"),
    ("CB-G7-001", ``ResearchCommons.Claims.G7.rank_budget, "ResearchCommons.Claims.G7"),
    ("CB-G7-001", ``ResearchCommons.Claims.G7.actual_original_policy_plan, "ResearchCommons.Claims.G7"),
    ("CB-G7-001", ``ResearchCommons.Claims.G7.actual_budget_exclusion, "ResearchCommons.Claims.G7"),
    ("CB-CAUSAL-001", ``ResearchCommons.Claims.Causal.original_selected_binary_upper, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-001", ``ResearchCommons.Claims.Causal.physical_policy_valid, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-001", ``ResearchCommons.Claims.Causal.physical_policy_identifies, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-001", ``ResearchCommons.Claims.Causal.actual_trek_source_unique, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-002", ``ResearchCommons.Claims.Causal.physical_no_short_plan, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-002", ``ResearchCommons.Claims.Causal.promised_budget_exact, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-002", ``ResearchCommons.Claims.Causal.arbitrary_seed_lower, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-003", ``ResearchCommons.Claims.Causal.no_targets_empty_graph, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-003", ``ResearchCommons.Claims.Causal.no_targets_singleton_class, "ResearchCommons.Claims.Causal"),
    ("CB-CAUSAL-003", ``ResearchCommons.Claims.Causal.no_targets_zero_query, "ResearchCommons.Claims.Causal"),
    ("CB-RXN-001", ``Astra.CommonMoment.nodes_subset_of_equal_sparse_moments, "CMFullMomentUniqueness"),
    ("CB-RXN-001", ``Astra.CommonMoment.moment_on_supergrid, "CMFullMomentUniqueness"),
    ("CB-RXN-001", ``Astra.CommonMoment.atomMass_eq_of_equal_sparse_moments, "CMFullMomentUniqueness"),
    ("CB-RXN-001", ``Astra.CommonMoment.atomMass_eq_of_equal_consecutive_moments, "CMFullMomentUniqueness"),
    ("CB-RXN-001", ``Astra.CommonMoment.all_moments_eq_of_equal_consecutive_moments, "CMFullMomentUniqueness"),
    ("CB-CM-001", ``ResearchCommons.Claims.CM.cap_five_separation, "ResearchCommons.Claims.CM"),
    ("CB-CM-001", ``ResearchCommons.Claims.CM.grouped_rational_law, "ResearchCommons.Claims.CM"),
    ("CB-CM-001", ``ResearchCommons.Claims.CM.grouped_rational_moments, "ResearchCommons.Claims.CM"),
    ("CB-SEQ-001", ``ResearchCommons.Claims.SequenceFirstOccurrence.plus_first_occurrence, "ResearchCommons.Claims.SequenceFirstOccurrence"),
    ("CB-SEQ-001", ``ResearchCommons.Claims.SequenceFirstOccurrence.even_minus_first_occurrence, "ResearchCommons.Claims.SequenceFirstOccurrence"),
    ("CB-SEQ-001", ``ResearchCommons.Claims.SequenceFirstOccurrence.odd_minus_first_occurrence, "ResearchCommons.Claims.SequenceFirstOccurrence"),
    ("CB-SEQ-001", ``ResearchCommons.Claims.SequenceFirstOccurrence.plus_all_starts, "ResearchCommons.Claims.SequenceFirstOccurrence"),
    ("CB-SEQ-001", ``ResearchCommons.Claims.SequenceFirstOccurrence.even_minus_all_starts, "ResearchCommons.Claims.SequenceFirstOccurrence"),
    ("CB-SEQ-001", ``ResearchCommons.Claims.SequenceFirstOccurrence.canonical_three_families, "ResearchCommons.Claims.SequenceFirstOccurrence"),
    ("CB-RNA-001", ``ResearchCommons.Claims.RNA.represented_scanner_pipeline, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-001", ``ResearchCommons.Claims.RNA.original_scaffold_partner, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-001", ``ResearchCommons.Claims.RNA.normalized_root_carrier, "ResearchCommons.Claims.RNA"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.rooted_cap_distinct_set_and_mean, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.repeated_label_anchor, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.weighted_anchor_composition, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.unit_anchor_composition, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.opened_choice_distinct_set_and_mean, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.galled_cap_opened_family_and_mean, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.actual_opened_curve_drawing, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.actual_opened_curve_subset, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.original_curve_adapter_roundtrip, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.actual_opened_planar_curves, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.actual_opened_planar_subset, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-001", ``ResearchCommons.Claims.NANUQ.actual_source_cycle_circle, "ResearchCommons.Claims.NANUQ"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.actual_totalRate_strict_merger, "ResearchCommons.MSCI.KilledClocks"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.actual_merger_charge_count_nonincreasing, "ResearchCommons.MSCI.KilledClocks"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.actual_killedRate_strict_merger, "ResearchCommons.MSCI.KilledClocks"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.actual_merger_killed_difference_positive, "ResearchCommons.MSCI.KilledClocks"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.character_add, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.probability_semigroup, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.fourier_transfer, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.kernel_probability, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.normalized_generator, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.uniform_root_pair_probability, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.clock_pair_correlation, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.clock_survival_timeOfSurvival, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.pair_time_decoder, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.character_sum, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69.actual_current_tree_character, "ResearchCommons.MSCI.JC69"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.likelihood_sum, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.kernel_probability, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.tree_fourier, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.root_fourier, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.totalCharge_eq_original_leaves, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.label_pattern_character, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.original_pattern_readout_injective, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.actual_single_root_covers_original_copies, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.actual_clock_survivals_admitted, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.actual_decoded_chronology, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.actual_tree_kernel_probability, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.locus_likelihood_sum, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Tree.locus_fourier, "ResearchCommons.MSCI.JC69Tree"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Observation.originalPatternEquiv, "ResearchCommons.MSCI.JC69Observation"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Observation.actual_original_label_probability, "ResearchCommons.MSCI.JC69Observation"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Observation.actual_original_label_fourier, "ResearchCommons.MSCI.JC69Observation"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Measurable.root_age_measurable, "ResearchCommons.MSCI.JC69Measurable"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Measurable.clock_likelihood_measurable, "ResearchCommons.MSCI.JC69Measurable"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Measurable.root_probability_measurable, "ResearchCommons.MSCI.JC69Measurable"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Measurable.decoded_probability_measurable, "ResearchCommons.MSCI.JC69Measurable"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Measurable.decoded_locus_measurable, "ResearchCommons.MSCI.JC69Measurable"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Measurable.actual_original_probability_measurable, "ResearchCommons.MSCI.JC69Measurable"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.conditional_kernel_probability, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.conditional_mass_measurable, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.conditional_locus_mass_measurable, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.original_point_measurable, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.actual_original_point_support, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.actual_source_locus_normalized, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.actual_source_locus_integral, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Source.registered_locus_probability, "ResearchCommons.MSCI.JC69Source"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Unranked.unordered_decoration_transport, "ResearchCommons.MSCI.JC69Unranked"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Unranked.decoded_root_probability_unordered, "ResearchCommons.MSCI.JC69Unranked"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Unranked.completed_forest_singleton, "ResearchCommons.MSCI.JC69Unranked"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Unranked.conditional_kernel_same_timed_observation, "ResearchCommons.MSCI.JC69Unranked"),
    ("CB-MSCI-001", ``ResearchCommons.MSCI.JC69Unranked.conditional_locus_same_timed_observation, "ResearchCommons.MSCI.JC69Unranked"),
    ("CB-MSCI-002", ``ResearchCommons.MSCI.Alignment.mem_allAlignments_iff, "ResearchCommons.MSCI.Alignment"),
    ("CB-MSCI-002", ``ResearchCommons.MSCI.Alignment.allAlignments_nonempty_iff, "ResearchCommons.MSCI.Alignment"),
    ("CB-MSCI-002", ``ResearchCommons.MSCI.Alignment.matches_refl, "ResearchCommons.MSCI.Alignment"),
    ("CB-MSCI-002", ``ResearchCommons.MSCI.Alignment.matches_trans, "ResearchCommons.MSCI.Alignment"),
    ("CB-MSCI-003", ``ResearchCommons.MSCI.RootPair.moment_formula, "ResearchCommons.MSCI.RootPair"),
    ("CB-MSCI-003", ``ResearchCommons.MSCI.RootPair.scaled_moments_injective, "ResearchCommons.MSCI.RootPair"),
    ("CB-MSCI-003", ``ResearchCommons.MSCI.RootPair.moments_injective, "ResearchCommons.MSCI.RootPair"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.term_nonneg, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.prefix_pos, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.prefix_le_exp, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.exp_le_upper, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.normalized_prefix_sum, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.lostMass_nonneg, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.lostMass_le_deficit, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-SOFTWARE-002", ``ResearchCommons.Numerics.CountPrefix.certified_error, "ResearchCommons.Numerics.CountPrefix"),
    ("CB-NANUQ-002", ``Nanuq.Canonical.theta_source, "CanonicalTheta"),
    ("CB-NANUQ-002", ``Nanuq.Canonical.theta_weighted, "CanonicalTheta"),
    ("CB-NANUQ-002", ``Nanuq.Canonical.theta_exact_quartet_mean, "CanonicalTheta"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.rawRho_valid, "RawNanuq"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.rawRho_nonneg, "RawNanuq"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.rawRho_witness_symmetric, "RawNanuq"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.rawRho_endpoint_symmetric, "RawNanuq"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.rawNanuq_symmetric, "RawNanuq"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.rawNanuq_positive, "RawNanuq"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.rawNanuq_ordered_formula, "RawNanuq"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.actualQuartetData_witness_symmetric, "NanuqActualNanuqAnchorBridge"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.actual_weightedNanuq_eq_anchor, "NanuqActualNanuqAnchorBridge"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.actual_weightedNanuq_blob_composition, "NanuqActualNanuqAnchorBridge"),
    ("CB-NANUQ-002", ``Nanuq.Source.RootedBinary.actual_sourceNanuq_blob_composition, "NanuqActualNanuqAnchorBridge"),
    ("CB-NANUQ-002", ``ResearchCommons.Claims.NANUQ.raw_tensor_eq_actual, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-002", ``ResearchCommons.Claims.NANUQ.raw_weighted_blob_composition, "ResearchCommons.Claims.NANUQ"),
    ("CB-NANUQ-002", ``ResearchCommons.Claims.NANUQ.raw_source_blob_composition, "ResearchCommons.Claims.NANUQ"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.interval_displays_iff_rectangle, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.split_union_rectangle_oracle, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.rectangle_left_partition, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.rectangle_right_partition, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.rectangle_singleton, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.wrap_query_singleton, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.OriginalRepresentative, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.OriginalCircle, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.original_circle_identity, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.original_split_target, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.original_split_evaluator, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.original_source_orders, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.original_orders_normalized, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.original_bounded_targets_and_circles, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Source.original_quartet_splice, "ResearchCommons.ExactQuery.Source"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.triangle_mid_partition, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.triangle_mid_disjoint, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.seed_covered_iff_triangle, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.all_candidates_covered, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.wrap_and_nonwrap_disjoint, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-EXACTQUERY-001", ``ResearchCommons.ExactQuery.Rectangle.emitted_roots_have_distinct_query_positions, "ResearchCommons.ExactQuery.Rectangle"),
    ("CB-NANUQ-003", ``Nanuq.AllLevelParameters.all_rows_iff_exact_domain, "AllLevelParameterDomain"),
    ("CB-NANUQ-003", ``Nanuq.AllLevelParameters.four_taxon_rows_iff_box, "AllLevelParameterDomain"),
    ("CB-NANUQ-003", ``Nanuq.AllLevelParameters.four_taxon_certificate_insufficient, "AllLevelParameterDomain"),
    ("CB-NANUQ-003", ``Nanuq.AllLevelParameters.four_taxon_certificate_misses_adjacent_lower_bound, "AllLevelParameterDomain"),
    ("CB-NANUQ-003", ``Nanuq.AllLevelParameters.original_and_modified_in_domain, "AllLevelParameterDomain"),
    ("CB-NANUQ-004", ``ResearchCommons.NANUQ.ContiguousCopies.extreme_bounds, "ResearchCommons.NANUQ.ContiguousCopies"),
    ("CB-NANUQ-004", ``ResearchCommons.NANUQ.ContiguousCopies.same_interval_side_extreme, "ResearchCommons.NANUQ.ContiguousCopies"),
    ("CB-NANUQ-004", ``ResearchCommons.NANUQ.ContiguousCopies.extreme_card_le_two, "ResearchCommons.NANUQ.ContiguousCopies"),
    ("CB-NANUQ-004", ``ResearchCommons.NANUQ.ContiguousCopies.cut_quartet_extremes_iff, "ResearchCommons.NANUQ.ContiguousCopies"),
    ("CB-NANUQ-004", ``ResearchCommons.NANUQ.ContiguousCopies.selection_side_extremes, "ResearchCommons.NANUQ.ContiguousCopies"),
    ("CB-NANUQ-004", ``ResearchCommons.NANUQ.ContiguousCopies.cut_split_extremes_iff, "ResearchCommons.NANUQ.ContiguousCopies"),
    ("CB-NANUQ-005", ``ResearchCommons.NANUQ.RawNoise.distinct_mean_twice_integer, "ResearchCommons.NANUQ.RawNoise"),
    ("CB-NANUQ-005", ``ResearchCommons.NANUQ.RawNoise.source_nanuq_integer, "ResearchCommons.NANUQ.RawNoise"),
    ("CB-NANUQ-005", ``ResearchCommons.NANUQ.RawNoise.raw_source_integer, "ResearchCommons.NANUQ.RawNoise"),
    ("CB-NANUQ-005", ``ResearchCommons.NANUQ.RawNoise.round_of_abs_sub_lt_half, "ResearchCommons.NANUQ.RawNoise"),
    ("CB-NANUQ-005", ``ResearchCommons.NANUQ.RawNoise.integer_matrix_rounding, "ResearchCommons.NANUQ.RawNoise"),
    ("CB-NANUQ-005", ``ResearchCommons.NANUQ.RawNoise.raw_source_rounding, "ResearchCommons.NANUQ.RawNoise"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.equivalent_refl, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.equivalent_symm, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.equivalent_trans, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.restrict_design, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.more_probes_preserve_identification, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.postprocess_preserves_equivalence, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.baseline_ambiguous, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.baseline_not_identified, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Identifiability.both_probes_identify, "SocialScience.Identifiability"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.common_intercept_preserves_order, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.common_intercept_preserves_difference, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.shift_invariance, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.population_shift_invariance, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.known_intercept_identifies, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.anchor_identifies_intercept, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.group_intercepts_can_reverse_order, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.bounded_bias_interval, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Measurement.difference_exceeding_bias_identifies_order, "SocialScience.Measurement"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.fits_empty, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.fits_cons_iff, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.fits_append_iff, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.more_evidence_narrows_models, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.truth_survives_correct_label, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.distinguishing_query_eliminates_rival, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.conflicting_labels_impossible, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.incorrect_label_excludes_truth, "SocialScience.Learning"),
    ("CB-SOFTSCI-001", ``SocialScience.Learning.duplicate_evidence_same_models, "SocialScience.Learning"),
    ("CB-SOFTSCI-002", ``SocialScience.Causality.observational_equivalence, "SocialScience.Causality"),
    ("CB-SOFTSCI-002", ``SocialScience.Causality.intervention_disagreement, "SocialScience.Causality"),
    ("CB-SOFTSCI-002", ``SocialScience.Causality.treatment_effect_numerator, "SocialScience.Causality"),
    ("CB-SOFTSCI-002", ``SocialScience.Causality.common_cause_numerator, "SocialScience.Causality"),
    ("CB-SOFTSCI-002", ``SocialScience.Causality.no_universal_observational_estimator, "SocialScience.Causality"),
    ("CB-SOFTSCI-002", ``SocialScience.Causality.all_responses_identify, "SocialScience.Causality"),
    ("CB-SOFTSCI-003", ``Solidarity.adj_symm, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.reach_trans, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.reach_symm, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.zero_reaches, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.path_connected, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.at_most_two_neighbors, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.unbounded_reachable, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.membership_nesting, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.overlapping_memberships, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.connected_without_trust, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.cooperation_stable_iff, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.no_sanction_failure, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.heterogeneous_cooperation_exists, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.homogeneous_cooperation_can_fail, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.symbols_alone_insufficient, "Solidarity"),
    ("CB-SOFTSCI-003", ``Solidarity.mutual_gain, "Solidarity"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.adding_members_preserves_feasibility, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.restricting_members_preserves_acceptance, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.union_accepts_iff, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.indispensable_member_withdrawal, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.complementary_pair_feasible, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.no_specialist_alone_feasible, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.aggregate_surplus_not_participation, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.repaired_allocation_ready, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.two_person_budget_iff, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-003", ``SocialScience.CollectiveAction.acceptable_share_interval, "SocialScience.CollectiveAction"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.reversal_cells_valid, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.first_stratum_advantage, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.second_stratum_advantage, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.pooled_reversal, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.simpson_reversal, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.equal_weight_addition_preserves_order, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.aggregate_cannot_identify_components, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-004", ``SocialScience.Aggregation.recoding_cannot_restore_components, "SocialScience.Aggregation"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.approach_trajectory, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.avoidance_trajectory, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.avoidance_observational_equivalence, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.avoidance_no_perfect_classifier, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.approach_observations_differ, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.approach_identifies_state, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.safe_columns_total_mass, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.danger_columns_total_mass, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.safe_columns_nonnegative, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.danger_columns_nonnegative, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.implicit_mappings_equal_at_tenth, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.approach_implicit_equality_iff, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.avoidance_implicit_columns_equal, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.PublishedCBT.explicit_prior_weights, "ClinicalModels.PublishedCBT"),
    ("CB-SOFTSCI-005", ``ClinicalModels.SourceBridge.source_sensory_columns, "ClinicalModels.SourceBridge"),
    ("CB-SOFTSCI-005", ``ClinicalModels.SourceBridge.source_affective_columns, "ClinicalModels.SourceBridge"),
    ("CB-SOFTSCI-005", ``ClinicalModels.SourceBridge.source_transition_columns, "ClinicalModels.SourceBridge"),
    ("CB-SOFTSCI-005", ``ClinicalModels.SourceBridge.source_implicit_columns, "ClinicalModels.SourceBridge"),
    ("CB-GENOME-001", ``FiniteGenomeIdentifiability.opposite_compatible_completions, "FiniteGenomeIdentifiability"),
    ("CB-GENOME-001", ``FiniteGenomeIdentifiability.no_exact_specieslike_verdict, "FiniteGenomeIdentifiability"),
    ("CB-GENOME-001", ``FiniteGenomeIdentifiability.no_exact_specieslike_decoder, "FiniteGenomeIdentifiability"),
    ("CB-GENOME-001", ``WongAlexander.actual_garg_opposite_infinite_completions, "WongAlexander"),
    ("CB-GENOME-002", ``ThreeTaxonIdentifiability.law_nonnegative, "ThreeTaxonIdentifiability"),
    ("CB-GENOME-002", ``ThreeTaxonIdentifiability.law_normalized, "ThreeTaxonIdentifiability"),
    ("CB-GENOME-002", ``ThreeTaxonIdentifiability.unique_maximizer, "ThreeTaxonIdentifiability"),
    ("CB-GENOME-002", ``ThreeTaxonIdentifiability.law_identifiable, "ThreeTaxonIdentifiability"),
    ("CB-GENOME-002", ``ThreeTaxonIdentifiability.boundary_uniform, "ThreeTaxonIdentifiability"),
    ("CB-GENOME-002", ``ThreeTaxonIdentifiability.no_boundary_decoder, "ThreeTaxonIdentifiability"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.sampleMass_positive, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.sampleMass_lower_bound, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.finite_sample_support_overlap, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.no_uniform_certain_decoder, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.quantitative_error_witness, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.robust_strict_mode, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.robust_maximizer_recovers, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ThreeTaxonFiniteEvidence.half_gap_tie, "ThreeTaxonFiniteEvidence"),
    ("CB-GENOME-002", ``ResearchCommons.Claims.Genome.law_transport, "ResearchCommons.Claims.Genome"),
    ("CB-GENOME-002", ``ResearchCommons.Claims.Genome.evidence_law_identifiable, "ResearchCommons.Claims.Genome"),
    ("CB-GENOME-003", ``PairingCore.edge_exact_image, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.owner_exactly_two, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.arbitrary_prefix_opposite_iap, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.constrained_counterexample, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.founders_exactly_four, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.parents_opposite_sex, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.same_copy_sex, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.exact_edges_do_not_lift_paths, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.natural_biosphere, "PairingCore"),
    ("CB-GENOME-003", ``PairingCore.no_iap_decoder, "PairingCore"),
    ("CB-GENOME-003", ``PairingGARG.topology_iff, "PairingGARG"),
    ("CB-GENOME-003", ``PairingGARG.sample_iff, "PairingGARG"),
    ("CB-GENOME-003", ``PairingGARG.nonemptyAnnotations, "PairingGARG"),
    ("CB-GENOME-003", ``PairingGARG.uniqueParentAt, "PairingGARG"),
    ("CB-GENOME-003", ``PairingGARG.sampleSupported, "PairingGARG"),
    ("CB-GENOME-003", ``PairingGARG.atLocus_iff, "PairingGARG"),
    ("CB-GENOME-003", ``PairingBridge.code_injective, "PairingBridge"),
    ("CB-GENOME-003", ``PairingBridge.finite_topology_iff_genome, "PairingBridge"),
    ("CB-GENOME-003", ``PairingBridge.finite_pedigree_exact_image, "PairingBridge"),
    ("CB-GENOME-003", ``PairingBridge.extraction_retains_every_edge, "PairingBridge"),
    ("CB-GENOME-003", ``PairingBridge.generation_dated_biosphere, "PairingBridge"),
    ("CB-GENOME-003", ``PairingObservation.query_coownership, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.local_query, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.query_formula, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.query_mixing, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.query_splitting, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.observe_eq_iff, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.split_observation_eq_iff, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.identifies_iap_iff, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.no_bounded_sampling_decoder, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.observed_positive_not_iap, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.even_owner_agreement, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.even_owners_equal, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.no_even_ownership_decoder, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.bounded_identifies_iap_iff, "PairingObservation"),
    ("CB-GENOME-003", ``PairingObservation.bounded_iap_iff_one_query, "PairingObservation"),
    ("CB-GENOME-004", ``PedigreeBlock.complement_ne, "PedigreeBlockModel"),
    ("CB-GENOME-004", ``PedigreeBlock.not_share_iff_complement, "PedigreeBlockGraph"),
    ("CB-GENOME-004", ``PedigreeBlock.not_connected_iff_bad, "PedigreeBlockGraph"),
    ("CB-GENOME-004", ``PedigreeBlock.reachable_of_restrict, "PedigreeBlockGraph"),
    ("CB-GENOME-004", ``PedigreeBlock.connected_of_restrict, "PedigreeBlockGraph"),
    ("CB-GENOME-004", ``PedigreeBlock.badEquiv, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.bad_card, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.configLaw_probability, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.configPMF_mass, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.bad_probability, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.uniform_pi_event, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.config_bit_cylinder, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.fair_bit_singleton, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.good_probability, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.familyLaw_probability, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.family_event_product, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.families_good_probability, "PedigreeBlockProbability"),
    ("CB-GENOME-004", ``PedigreeBlock.observedShare_iff, "PedigreeBlockObservation"),
    ("CB-GENOME-004", ``PedigreeBlock.observed_path_preserves_family, "PedigreeBlockObservation"),
    ("CB-GENOME-004", ``PedigreeBlock.family_path_iff, "PedigreeBlockObservation"),
    ("CB-GENOME-004", ``PedigreeBlock.recovered_iff_connected, "PedigreeBlockObservation"),
    ("CB-GENOME-004", ``PedigreeBlock.connected_probability, "PedigreeBlockRecovery"),
    ("CB-GENOME-004", ``PedigreeBlock.recovered_probability, "PedigreeBlockRecovery"),
    ("CB-GENOME-004", ``PedigreeBlock.observationLaw_probability, "PedigreeBlockRecovery"),
    ("CB-GENOME-004", ``PedigreeBlock.output_recovery_probability, "PedigreeBlockRecovery"),
    ("CB-GENOME-004", ``PedigreeBlock.repeatBlock_share_iff, "PedigreeBlockDependence"),
    ("CB-GENOME-004", ``PedigreeBlock.repeatBlock_connected_iff, "PedigreeBlockDependence"),
    ("CB-GENOME-004", ``PedigreeBlock.repeatedLaw_probability, "PedigreeBlockDependence"),
    ("CB-GENOME-004", ``PedigreeBlock.repeatedLaw_block_marginal, "PedigreeBlockDependence"),
    ("CB-GENOME-004", ``PedigreeBlock.repeatedLaw_connected_eq_one_block, "PedigreeBlockDependence"),
    ("CB-GENOME-004", ``PedigreeBlock.repeatedLaw_connected_probability, "PedigreeBlockDependence"),
    ("CB-GENOME-004", ``ResearchCommons.Claims.BlockRecovery.recovered_of_restrict, "ResearchCommons.Claims.BlockRecovery"),
    ("CB-MEMORY-001", ``ExactAbstraction.exact_factor_iff, "ExactAbstraction"),
    ("CB-MEMORY-001", ``ExactAbstraction.exact_factor_unique, "ExactAbstraction"),
    ("CB-MEMORY-001", ``ExactAbstraction.trajectory_preservation, "ExactAbstraction"),
    ("CB-MEMORY-001", ``ExactAbstraction.compatible_gives_trajectories, "ExactAbstraction"),
    ("CB-MEMORY-001", ``PredictiveState.encode_eq_iff, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.quotient_observe, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.quotient_step, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.run_commutes, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.exact_refinement_future, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.factors_iff, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.coarsest_exact, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.distinguishing_word, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.distinguishable_injective, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.distinguishable_card_le, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.restrict_actions, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.depth_iff_words, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.future_depth, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.stabilization_complete, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.feedback_commutes, "PredictiveState"),
    ("CB-MEMORY-001", ``PredictiveState.feedback_trajectories, "PredictiveState"),
    ("CB-MEMORY-001", ``ControlledMemory.cell_commutes, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.history_commutes, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.no_finite_suffix_decoder, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.cross_model_all_words, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.cross_model_all_times, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.probe_refinement_factor, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.cell_future_iff, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.history_future_iff, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.at_least_four, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.memory_required_at_fixed_visible, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.reachable_probe_witness, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.all_summaries_reachable, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.passive_visible_exact, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.passive_future_iff, "ControlledMemory"),
    ("CB-MEMORY-001", ``ControlledMemory.changed_probe_refutes_summary, "ControlledMemory"),
    ("CB-MEMORY-001", ``HistoryObservation.stable_type_matched_history_null, "HistoryObservation"),
    ("CB-MEMORY-001", ``HistoryObservation.selection_no_history_effect, "HistoryObservation"),
    ("CB-MEMORY-001", ``HistoryObservation.selected_history_perfectly_predicts, "HistoryObservation"),
    ("CB-MEMORY-001", ``HistoryObservation.arbitrary_delayed_distinction, "HistoryObservation"),
    ("CB-MEMORY-001", ``AncestryObservation.restriction_commutes, "AncestryObservation"),
    ("CB-MEMORY-001", ``AncestryObservation.restriction_all_words, "AncestryObservation"),
    ("CB-MEMORY-001", ``AncestryObservation.sample_query_factors, "AncestryObservation"),
    ("CB-MEMORY-001", ``AncestryObservation.no_universal_sample_expansion, "AncestryObservation"),
    ("CB-MEMORY-001", ``WongPredictiveBridge.extracted_is_compress, "WongPredictiveBridge"),
    ("CB-MEMORY-001", ``WongPredictiveBridge.actual_garg_restriction_all_words, "WongPredictiveBridge"),
    ("CB-MEMORY-001", ``WongPredictiveBridge.no_global_iap_decoder, "WongPredictiveBridge"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.split_preserves_legal, "MergeHistoryProjection"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.adjacent_merge_histories, "MergeHistoryProjection"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.legal_histories, "MergeHistoryProjection"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.admissible_splits_with_spectator, "MergeHistoryProjection"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.same_current_partition, "MergeHistoryProjection"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.distinct_restored_partitions, "MergeHistoryProjection"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.no_exact_partition_model, "MergeHistoryProjection"),
    ("CB-MEMORY-002", ``MergeHistoryProjection.no_partition_only_admissible_split, "MergeHistoryProjection"),
    ("CB-MEMORY-003", ``StochasticAbstraction.exact_iff, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.exact_unique, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.exact_iff_all_initial_laws, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.runLaw_preserves, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.runLaw_initial, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.experiment_preserves, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.experimentLaw_preserves, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.observationPolicy_factors, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.observed_experiment_law, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.observed_statistic_preserves, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.deterministic_instance, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.joint_sensor_exact, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticAbstraction.joint_sensor_observed_law, "StochasticAbstraction"),
    ("CB-MEMORY-003", ``StochasticExamples.matching_marginals_different_joint, "StochasticExamples"),
    ("CB-MEMORY-003", ``StochasticExamples.c_is_mixture, "StochasticExamples"),
    ("CB-MEMORY-003", ``StochasticExamples.same_all_traces, "StochasticExamples"),
    ("CB-MEMORY-003", ``StochasticExamples.no_trace_based_test_separates, "StochasticExamples"),
    ("CB-MEMORY-003", ``StochasticExamples.same_profile, "StochasticExamples"),
    ("CB-MEMORY-003", ``StochasticExamples.profile_pushes_differ, "StochasticExamples"),
    ("CB-MEMORY-003", ``StochasticExamples.no_commuting_profile_kernel, "StochasticExamples"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.sample_mass_nonnegative, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.sample_mass_normalized, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.all_zero_mass, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.miss_positive, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.miss_le_one, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.null_error_at_zero, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.all_zero_error_contribution, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.sum_error_lower, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.worst_error_lower, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.threshold_rule_errors, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.balanced_rule_errors, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.sharp_sum_error, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.sharp_worst_error, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.sharp_equal_prior_error, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.no_finite_certain_decision, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.zero_trials_miss, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.fixed_rate_arbitrarily_accurate, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.miss_lower_rate_bound, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.bernoulli_lower, "ResearchCommons.Calibration.RareEvent"),
    ("CB-MEMORY-004", ``ResearchCommons.Calibration.no_uniform_finite_guarantee, "ResearchCommons.Calibration.RareEvent"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.nonempty_has_earliest, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.earliest_is_founder, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.founder_covers, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.window_finite_founders, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.commonAncestor_window, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.window_nonnegative, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.window_directed_union, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``RealFounderWindow.directed_union_finite_founders, "RealFounderWindow"),
    ("CB-ALEXANDER-004", ``FounderMaximal.directed_union_connected, "FounderMaximal"),
    ("CB-ALEXANDER-004", ``FounderMaximal.union_reflection, "FounderMaximal"),
    ("CB-ALEXANDER-004", ``FounderMaximal.windowSpecies_directed_union, "FounderMaximal"),
    ("CB-ALEXANDER-004", ``FounderMaximal.maximal_extension_of_directed_union, "FounderMaximal"),
    ("CB-ALEXANDER-004", ``FounderMaximal.maximal_window_extension_ordered, "FounderMaximal"),
    ("CB-ALEXANDER-004", ``SpeciesSeed.anchored_minimal_exists, "SpeciesSeed"),
    ("CB-ALEXANDER-004", ``SpeciesSeed.productivePart_convex, "SpeciesSeed"),
    ("CB-ALEXANDER-004", ``SpeciesSeed.productivePart_internal_infinite, "SpeciesSeed"),
    ("CB-ALEXANDER-004", ``SpeciesSeed.minimal_anchored_iap, "SpeciesSeed"),
    ("CB-ALEXANDER-004", ``SpeciesSeed.exists_anchored_seed, "SpeciesSeed"),
    ("CB-ALEXANDER-004", ``SpeciesSeed.exists_seed, "SpeciesSeed"),
    ("CB-ALEXANDER-004", ``RealSpeciesTheorem.windowSpecies_iff, "RealSpeciesTheorem"),
    ("CB-ALEXANDER-004", ``RealSpeciesTheorem.push_maximal, "RealSpeciesTheorem"),
    ("CB-ALEXANDER-004", ``RealSpeciesTheorem.maximal_window_extension, "RealSpeciesTheorem"),
    ("CB-ALEXANDER-004", ``RealSpeciesTheorem.every_vertex_has_seed, "RealSpeciesTheorem"),
    ("CB-ALEXANDER-004", ``RealSpeciesTheorem.every_vertex_in_maximal_real_window, "RealSpeciesTheorem"),
    ("CB-WONG-001", ``ResearchCommons.Claims.Wong.intrinsic_count_time_law, "ResearchCommons.Claims.Wong"),
    ("CB-WONG-001", ``ResearchCommons.Claims.Wong.measurable_valid_history, "ResearchCommons.Claims.Wong"),
    ("CB-WONG-001", ``ResearchCommons.Claims.Wong.actual_history_support, "ResearchCommons.Claims.Wong"),
    ("CB-RNA-002", ``ResearchCommons.Claims.RNA.admitted_gamma_class_probability, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-002", ``ResearchCommons.Claims.RNA.admitted_positive_output_bijection, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-003", ``ResearchCommons.Claims.RNA.observed_ordered_derivation_sum, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-003", ``ResearchCommons.Claims.RNA.scheduled_ordered_derivation_sum, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-003", ``ResearchCommons.Claims.RNA.valid_active_ordered_fold, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-004", ``ResearchCommons.Claims.RNA.interval_top_k, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-004", ``ResearchCommons.Claims.RNA.anytime_top_k, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-004", ``ResearchCommons.Claims.RNA.discrepancy_top_k, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-004", ``ResearchCommons.Claims.RNA.strict_gap_certificate, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-004", ``ResearchCommons.Claims.RNA.residual_top_k, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-004", ``ResearchCommons.Claims.RNA.residual_conservation, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-005", ``ResearchCommons.Claims.RNA.source_event_coordinates, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-005", ``ResearchCommons.Claims.RNA.local_schema_root_bound, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-005", ``ResearchCommons.Claims.RNA.bounded_root_events, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-005", ``ResearchCommons.Claims.RNA.be_root_ownership, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-006", ``ResearchCommons.Claims.RNA.midpoint_branch_tv, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-006", ``ResearchCommons.Claims.RNA.continuous_branch, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-006", ``ResearchCommons.Claims.RNA.midpoint_trace_error, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-006", ``ResearchCommons.Claims.RNA.midpoint_class_error, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-006", ``ResearchCommons.Claims.RNA.local_sample_v_slots, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-006", ``ResearchCommons.Claims.RNA.local_sample_v_grid_error, "ResearchCommons.Claims.RNA"),
    ("CB-RNA-006", ``ResearchCommons.Claims.RNA.supported_wrapper_rank, "ResearchCommons.Claims.RNA")
  ]
  for (id, declaration, expected) in requested do
    let some index := environment.getModuleIdxFor? declaration | throwError m!"Missing owner for {id}: {declaration}"
    let actual := environment.header.moduleNames[index.toNat]!.toString
    unless actual == expected do
      throwError m!"Wrong export owner for {id}: {declaration}, expected {expected}, actual {actual}"
  logInfo m!"Verified {requested.size} exact claim export owners"
end ResearchCommons.Generated.ClaimExports
