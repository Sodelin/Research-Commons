import ExponentialClockMoments
import G1SharedRegisterStress
import G2LiveLineageRouting
import G3AllResidueNormalIdentities
import G3AllResiduePositivity
import G3BernoulliCriticalNumerators
import G3BernoulliDerivatives
import G3CapSixDeterminant
import G3FiniteMomentBarrier
import G4AllRootBinomialCompression
import G4AllRootPairClocks
import G4BalancedForestIdentity
import G4FourRootPositivity
import G4IndependentRoutingBridge
import G4KingmanHankelObstruction
import G4TwoRootSourceStopping
import G5BoundedExactBlock
import G5BridgeBarrier
import G5BridgeComponentEntries
import G5CalendarRoutes
import G5CoupledQuartetKernel
import G5CutChildNecessity
import G5ExponentialGermIdentification
import G5FairSelectorMoments
import G5MinimalGraphInterface
import G5NonbridgeRouteBound
import G5PairMomentCases
import G5ProtectiveBlock
import G5ThreeGroupKernel
import G5UnknownRateSupport
import G6BridgeCannotEnterHybrid
import G7OriginalCensus
import KingmanFiniteChernoff
import KingmanFiniteClockTail
import RepresentationTransport

/-! Exact-source integration checkpoint of presently compiled components.
This is not a whole source theorem or full claimed-package certificate.
Actual graph/process/observable/algorithm bridges remain explicit in the manifest. -/

#print axioms GProgram.Kingman.ClockMoments.exponential_positivePart_integral
#print axioms GProgram.Kingman.ClockMoments.exponential_first_moment
#print axioms GProgram.Kingman.ClockMoments.exponential_transform
#print axioms GProgram.G1.pairSurvival_eq_exp
#print axioms GProgram.G1.pairSurvival_log_two
#print axioms GProgram.G1.pairSurvival_log_four
#print axioms GProgram.G1.shared_register_exact_counterexample
#print axioms GProgram.G1.retained_register_joint_normalized
#print axioms GProgram.G1.retained_register_joint_nonnegative
#print axioms GProgram.G1.resampling_changes_exposed_context
#print axioms GProgram.G1.exposed_event_preserved_iff_equal_conditionals
#print axioms GProgram.G2.coalesced_copies_cannot_split
#print axioms GProgram.G2.routed_parent_eq_iff_live_coin_eq
#print axioms GProgram.G2.opposite_copy_bits_are_not_a_live_pulse
#print axioms GProgram.G2.wrong_pulse_split_mass
#print axioms GProgram.G2.fair_copy_pulse_splits_merged_ancestor
#print axioms GProgram.G3.AllResidue.normal_sum
#print axioms GProgram.G3.AllResidue.normal_drift
#print axioms GProgram.G3.AllResidue.normal_residue_value
#print axioms GProgram.G3.AllResidue.normal_residue_derivative
#print axioms GProgram.G3.AllResidue.normal_square_value
#print axioms GProgram.G3.AllResidue.normal_square_derivative
#print axioms GProgram.G3.AllResidue.normal_mass_pos
#print axioms GProgram.G3.AllResidue.normal_mass_ne_zero
#print axioms GProgram.G3.AllResidue.quadratic_factor_pos
#print axioms GProgram.G3.AllResidue.exceptionalJ_exact
#print axioms GProgram.G3.AllResidue.exceptional_remainder_nonneg
#print axioms GProgram.G3.AllResidue.exceptionalJ_pos
#print axioms GProgram.G3.AllResidue.critical_gcd_product_pos
#print axioms GProgram.G3.AllResidue.source_denominator_pos
#print axioms GProgram.G3.AllResidue.clear_p_response
#print axioms GProgram.G3.AllResidue.clear_q_response
#print axioms GProgram.G3.AllResidue.p_response_zero_iff
#print axioms GProgram.G3.AllResidue.q_response_zero_iff
#print axioms GProgram.G3.AllResidue.bernoulli_factor_pos
#print axioms GProgram.G3.AllResidue.bernoulli_factor_lt_one
#print axioms GProgram.G3.AllResidue.hasDerivAt_bernoulliFactor_p
#print axioms GProgram.G3.AllResidue.hasDerivAt_bernoulliFactor_q
#print axioms GProgram.G3.AllResidue.hasDerivAt_bernoulliLog_p
#print axioms GProgram.G3.AllResidue.hasDerivAt_bernoulliLog_q
#print axioms GProgram.G3.CapSix.LU_eq_J0
#print axioms GProgram.G3.CapSix.det_L
#print axioms GProgram.G3.CapSix.det_U
#print axioms GProgram.G3.CapSix.exact_determinant
#print axioms GProgram.G3.CapSix.J0_nonsingular
#print axioms GProgram.G3.CapSix.scaled_J_nonsingular
#print axioms GProgram.G3.MomentBarrier.coupled_barrier_minimal
#print axioms GProgram.G3.MomentBarrier.exact_double_sum
#print axioms GProgram.G3.MomentBarrier.finite_moment_inequality
#print axioms GProgram.G3.MomentBarrier.coupled_barrier
#print axioms GProgram.G4.BinomialCompression.original_all_root_binomial_sum
#print axioms GProgram.G4.BinomialCompression.original_all_root_exponential_coefficients
#print axioms GProgram.G4.BinomialCompression.rootSetEquiv
#print axioms GProgram.G4.BinomialCompression.all_root_binomial_sum
#print axioms GProgram.G4.PairClocks.private_arms_no_first_merge
#print axioms GProgram.G4.PairClocks.livePair_card
#print axioms GProgram.G4.PairClocks.all_root_no_first_merge
#print axioms GProgram.G4.PairClocks.product_clock_eq_holding_model
#print axioms GProgram.G4.balanced_residual_identity
#print axioms GProgram.G4.balanced_coordinate_separates_cap4
#print axioms GProgram.G4.ordinary_balanced_positive
#print axioms GProgram.G4.FourRoot.exact_defect_factorization
#print axioms GProgram.G4.FourRoot.zero_delta_forces_negative_defect3
#print axioms GProgram.G4.FourRoot.no_common_moment_signature
#print axioms GProgram.G4.FourRoot.rational_cap3_scalar_witness
#print axioms GProgram.G4.IndependentRouting.exponential_model_original_coordinates
#print axioms GProgram.G4.IndependentRouting.original_source_coordinates
#print axioms GProgram.G4.IndependentRouting.exponential_four_root_arm_law
#print axioms GProgram.G4.IndependentRouting.actual_parent0_count
#print axioms GProgram.G4.IndependentRouting.generic_two
#print axioms GProgram.G4.IndependentRouting.generic_three
#print axioms GProgram.G4.IndependentRouting.generic_four
#print axioms GProgram.G4.IndependentRouting.routingWeight_normalized
#print axioms GProgram.G4.Hankel.choose_two_add
#print axioms GProgram.G4.Hankel.shiftedHankel_factorization
#print axioms GProgram.G4.Hankel.shiftedHankel_det_ne_zero
#print axioms GProgram.G4.Hankel.finite_window_coefficients_zero
#print axioms GProgram.G4.Hankel.eventual_recurrence_coefficients_zero
#print axioms GProgram.G4.Hankel.pairClockSurvival_eq
#print axioms GProgram.G4.Hankel.source_clock_eventual_recurrence_coefficients_zero
#print axioms G4TwoRootSourceStopping.bareSurvival_eq
#print axioms G4TwoRootSourceStopping.rootedACladeResponse_injective
#print axioms G4TwoRootSourceStopping.observable_finite_length_certificate
#print axioms GProgram.G5.BoundedSupport.bounded_unary_obstruction
#print axioms GProgram.G5.BoundedSupport.exact_block_small_obstruction
#print axioms GProgram.G5.BoundedSupport.exact_block_iff_local
#print axioms GProgram.G5.bridge_target_component_iff_descendant
#print axioms GProgram.G5.unique_child_edge
#print axioms GProgram.G5.descendant_via_unique_child
#print axioms GProgram.G5.hybrid_descendant_component
#print axioms GProgram.G5.ComponentEntries.bridge_targets_sameBlob_iff_eq
#print axioms GProgram.G5.ComponentEntries.bridge_target_not_root_component
#print axioms GProgram.G5.ComponentEntries.nonroot_component_has_incoming_bridge
#print axioms GProgram.G5.ComponentEntries.nonroot_component_unique_entry
#print axioms GProgram.G5.bridge_mem_every_descendant_route
#print axioms GProgram.G5.original_tip_route_exists
#print axioms GProgram.G5.EdgePath.active_unique
#print axioms GProgram.G5.protective_edge_active_on_every_route
#print axioms GProgram.G5.protective_edge_absent_on_outside_route
#print axioms GProgram.G5.protective_interval_nonempty
#print axioms GProgram.G5.younger_side_open_interval_has_no_first
#print axioms GProgram.G5.QuartetKernel.selectorWitness_iff_blockWitness
#print axioms GProgram.G5.QuartetKernel.pairCount_four_iff
#print axioms GProgram.G5.QuartetKernel.pairCount_one_split
#print axioms GProgram.G5.CutChildTest.source
#print axioms GProgram.G5.CutChildTest.tips_contemporary
#print axioms GProgram.G5.CutChildTest.actual_weaker_source_counterexample
#print axioms GProgram.G5.CutChildTest.actual_protective_route_failure
#print axioms GProgram.G5.ExponentialGerm.coefficient_zero_of_grid
#print axioms GProgram.G5.ExponentialGerm.coefficients_eq_of_right_germ
#print axioms GProgram.G5.ExponentialGerm.constant_coefficient_eq_of_right_germ
#print axioms GProgram.G5.QuartetKernel.meetingChoices_card
#print axioms GProgram.G5.QuartetKernel.fairMeetingMass_eq_count
#print axioms GProgram.G5.Minimal.root_source_side_of_rooted_acyclic
#print axioms GProgram.G5.Minimal.bridge_component_iff_descendant
#print axioms GProgram.G5.NonbridgeRoutes.UpPath.unique_from_kept_source
#print axioms GProgram.G5.NonbridgeRoutes.UpPath.unique_of_same_first
#print axioms GProgram.G5.NonbridgeRoutes.cut_child_nonbridge_incoming_unique
#print axioms GProgram.G5.NonbridgeRoutes.original_nonbridge_route_unique_of_first
#print axioms GProgram.G5.NonbridgeRoutes.finite_nonbridge_route_family_card_le_indegree
#print axioms GProgram.G5.NonbridgeRoutes.hybrid_nonbridge_route_family_card_le_two
#print axioms GProgram.G5.NonbridgeRoutes.ordinary_nonbridge_route_family_card_le_one
#print axioms GProgram.G5.QuartetKernel.pairCount_zero_iff
#print axioms GProgram.G5.QuartetKernel.pairCount_two_iff
#print axioms GProgram.G5.QuartetKernel.pairCount_one_iff
#print axioms GProgram.G5.routeFamily_exists
#print axioms GProgram.G5.protective_population_block_eq
#print axioms GProgram.G5.QuartetKernel.threeGroup_absence_iff
#print axioms GProgram.G5.ExponentialGerm.finite_coefficients_zero_of_right_germ
#print axioms GProgram.G5.ExponentialGerm.finite_coefficients_eq_of_right_germ
#print axioms GProgram.G5.ExponentialGerm.finite_constant_mass_eq_of_right_germ
#print axioms GProgram.G6.BridgeEntry.bridge_targets_injective
#print axioms GProgram.G6.BridgeEntry.bridge_incoming_unique
#print axioms GProgram.G6.BridgeEntry.bridge_target_indegree_one
#print axioms GProgram.G6.BridgeEntry.two_incoming_occurrences_not_bridge
#print axioms GProgram.G6.BridgeEntry.original_bridge_target_not_hybrid
#print axioms GProgram.G6.BridgeEntry.original_hybrid_parents_nonbridge
#print axioms GProgram.G7.sum_inDegree
#print axioms GProgram.G7.sum_outDegree
#print axioms GProgram.G7.original_census
#print axioms GProgram.Kingman.FiniteChernoff.finite_mgf_exact
#print axioms GProgram.Kingman.FiniteChernoff.product_bound
#print axioms GProgram.Kingman.FiniteChernoff.uniform_chernoff_tail
#print axioms GProgram.Kingman.FiniteClockTail.uniform_markov_tail
#print axioms GProgram.Kingman.FiniteClockTail.reciprocalSum_exact
#print axioms GProgram.Kingman.FiniteClockTail.finite_clock_mean
#print axioms RepresentationPilot.recoding_preserves_collision
#print axioms RepresentationPilot.target_fiber_constancy_iff_of_decoder
#print axioms RepresentationPilot.incidence_injective
#print axioms RepresentationPilot.joint_incidence_injective
#print axioms RepresentationPilot.full_haar_leftInverse
#print axioms RepresentationPilot.full_haar_injective
#print axioms RepresentationPilot.dropping_detail_collides
