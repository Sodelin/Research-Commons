#!/usr/bin/env python3
"""Bounded hosted component check with shared encrypted capture/recovery."""
import argparse
from pathlib import Path
import sys
from online_capture import run_case

ROOT = Path(__file__).resolve().parent
CASES = {
    'g7-trace-rows': ('lean/proposals/G7SuccessfulTraceRows.lean', [
        'Astra.G7SuccessfulTraceRows.fibre_bind',
        'Astra.G7SuccessfulTraceRows.queried_bind_matrix',
        'Astra.G7SuccessfulTraceRows.compressed_step']),
    'population-coefficients': ('lean/proposals/PopulationCoefficientProjection.lean', [
        'Astra.NativePopulationTableCertificate.polynomial_coefficient',
        'Astra.NativePopulationTableCertificate.coefficient_zero_of_absent',
        'Astra.NativePopulationTableCertificate.checkExpr_sound']),
    'g7-finite-target': ('lean/OnlineG7FiniteTargetReceiver.lean', [
        'Astra.G7FiniteTargetReceiver.consistent_piece',
        'Astra.G7FiniteTargetReceiver.reachable_iff_consistent_source',
        'Astra.G7FiniteTargetReceiver.target_clause_iff_valid_stop',
        'Astra.G7FiniteTargetReceiver.target_clause_iff_exclusions',
        'Astra.G7FiniteTargetReceiver.target_of_shared_constant_guard',
        'Astra.G7FiniteTargetReceiver.reachable_target_unique',
        'Astra.G7FiniteTargetReceiver.reachable_homogeneous_unique_target',
        'Astra.G7FiniteTargetReceiver.unreachable_all_targets',
        'Astra.G7FiniteTargetReceiver.empty_cases_unreachable',
        'Astra.G7FiniteTargetReceiver.physical_target_of_guarded_clause',
        'Astra.G7FiniteTargetReceiver.physical_stop_identifies']),
    'g7-power-domain': ('lean/G7FixedCalendarPowerDomain.lean', [
        'Astra.FixedCalendarPowerDomain.rate_pos',
        'Astra.FixedCalendarPowerDomain.rate_survival',
        'Astra.FixedCalendarPowerDomain.power_eq_iff_log_eq',
        'Astra.FixedCalendarPowerDomain.positive_power_iff_exp',
        'Astra.FixedCalendarPowerDomain.slot_survival_mem',
        'Astra.FixedCalendarPowerDomain.correlated_slots_exists_unique']),
    'g7-padded-response': ('lean/OnlineG7PaddedResponseCarrier.lean', [
        'Astra.G7PaddedResponseCarrier.restrict_pad',
        'Astra.G7PaddedResponseCarrier.pad_restrict',
        'Astra.G7PaddedResponseCarrier.pad_add',
        'Astra.G7PaddedResponseCarrier.pad_zero_outputs',
        'Astra.G7PaddedResponseCarrier.inconsistent_nonzero_padding',
        'Astra.G7PaddedResponseCarrier.winning_reply_quantifier_iff']),
    'g7-source-transfer': ('lean/OnlineG7ExactLawSourceTransfer.lean', [
        'Astra.G7ExactLawSourceTransfer.related_consistent_iff',
        'Astra.G7ExactLawSourceTransfer.consistent_has_source',
        'Astra.G7ExactLawSourceTransfer.homogeneous_iff',
        'Astra.G7ExactLawSourceTransfer.winning_iff',
        'Astra.G7ExactLawSourceTransfer.valid_plan_iff',
        'Astra.G7ExactLawSourceTransfer.physical_run_of_symbolic_valid',
        'Astra.G7ExactLawSourceTransfer.physical_pair_of_symbolic_pair',
        'Astra.G7ExactLawSourceTransfer.physical_pair_of_symbolic_loss']),
    'g7-path-game': ('lean/OnlineG7FinitePathGame.lean', [
        'Astra.G7FinitePathGame.remaining_after_legal',
        'Astra.G7FinitePathGame.winning_mono',
        'Astra.G7FinitePathGame.winning_iff_call_cap',
        'Astra.G7FinitePathGame.regional_winning_iff_capped',
        'Astra.G7FinitePathGame.total_policy_capped_at_history',
        'Astra.G7FinitePathGame.capped_loss_excludes_total_policy']),
    'g7-path-budget': ('lean/OnlineG7FinitePathBudgetBridge.lean', [
        'Astra.G7FinitePathBudgetBridge.finite_union_deletion_closed',
        'Astra.G7FinitePathBudgetBridge.next_action_legal_deletion',
        'Astra.G7FinitePathBudgetBridge.extension_call_bound',
        'Astra.G7FinitePathBudgetBridge.zero_remaining_no_legal_action']),
    'g7-game': ('lean/OnlineG7ExactLawGame.lean', [
        'GProgram.G7.ExactLawResourceGame.consistent_extend',
        'GProgram.G7.ExactLawResourceGame.homogeneous_iff_terminal',
        'GProgram.G7.ExactLawResourceGame.winning_iff_valid_plan',
        'GProgram.G7.ExactLawResourceGame.valid_run_identifies',
        'GProgram.G7.ExactLawResourceGame.losing_step',
        'GProgram.G7.ExactLawResourceGame.losing_has_full_history_pair',
        'GProgram.G7.ExactLawResourceGame.trajectory_budget_deletion_closed',
        'GProgram.G7.ExactLawRankCompression.redundant_response_unique',
        'GProgram.G7.ExactLawRankCompression.determined_extend',
        'GProgram.G7.ExactLawRankCompression.first_informative',
        'GProgram.G7.ExactLawRankCompression.total_strategy_wins_with_rank_budget',
        'GProgram.G7.ExactLawRankCompression.pointwise_total_strategy_has_finite_informative_horizon']),
    'code-receiver': ('lean/OnlineOriginalCodeChartReceiver.lean', [
        'Astra.OriginalCodeChartReceiver.checked_original_witness',
        'Astra.OriginalCodeChartReceiver.checked_original_bank',
        'Astra.OriginalCodeChartReceiver.checked_original_bank_rates',
        'Astra.OriginalCodeChartReceiver.checked_original_bank_feasible',
        'Astra.OriginalCodeChartReceiver.checked_original_exclusion']),
    'code-chart': ('lean/OnlineOriginalCodeChartReflection.lean', [
        'Astra.OriginalCodeChartReflection.fieldReflection',
        'Astra.OriginalCodeChartReflection.decoded_emitRows_of_code',
        'Astra.OriginalCodeChartReflection.coefficient_lengths_of_code',
        'Astra.OriginalCodeChartReflection.decoded_emitRows_toFinset_of_code']),
    'aggregate': ('lean/OnlineNativeCellAggregateReflection.lean', [
        'Astra.NativeCellAggregateReflection.erase_emitRows_eq_encoded',
        'Astra.NativeCellAggregateReflection.decoded_emitRows_eq_compileCellList',
        'Astra.NativeCellAggregateReflection.emitted_coefficient_lengths',
        'Astra.NativeCellAggregateReflection.decoded_emitRows_toFinset']),
    'admission': ('lean/OnlineOriginalCodeBankLayout.lean', [
        'GProgram.G7.OriginalAdmission.sourceOfValid',
        'GProgram.G7.OriginalAdmission.decodedIDs',
        'GProgram.G7.OriginalAdmission.decoded_parent_exact',
        'Astra.OriginalCodeBankLayout.layout',
        'Astra.OriginalCodeBankLayout.hybrid_position',
        'Astra.OriginalCodeBankLayout.parent_occurrence']),
    'reject-false': ('lean/UnionCaptureRejectFalse.lean',
                     ['Astra.UnionCaptureControls.false_proof']),
    'reject-sorry': ('lean/UnionCaptureRejectSorry.lean',
                     ['Astra.UnionCaptureControls.sorry_proof']),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True, choices=list(CASES))
    parser.add_argument('--record-codec', required=True, type=Path)
    parser.add_argument('--codec-sha256', required=True)
    args = parser.parse_args()
    source, audits = CASES[args.case]
    return run_case(ROOT, args.case, source, audits,
        'online_lean_drain.mjs', 'online_lean_quiet.mjs', args.record_codec,
        args.codec_sha256, Path(__file__).name)


if __name__ == '__main__':
    sys.exit(main())
