#!/usr/bin/env python3
"""Byte/source inspection of a saved plan only; no target imports or runs."""
import hashlib
import json
import pathlib
from datetime import datetime, timezone

REPO = pathlib.Path('/workspace/Research-Commons')
PACKET = REPO / 'research/2026-10-10-codex-lean-rust-parity'
OWN = pathlib.Path(__file__).resolve().parent
NOTE = PACKET / 'rust/notes/SOURCE-FIT-ORIGINAL-CONTROL-REUSE-20261010T2312Z.md'
CAPTURE = NOTE.with_suffix('.json')
NOTE_SHA = '66051721d6081e8bd431aa30c0f9e061aae40e27a55a17bbfb0938981c5fff02'
CAPTURE_SHA = 'ce28a0c52ec5181d4b9938a57bf0b4d394a28b9e095e536beb2675a595bdaf33'

def pin(path, expected=None, size=None):
    path = pathlib.Path(path)
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if expected is not None:
        assert digest == expected, (str(path), digest, expected)
    if size is not None:
        assert len(raw) == size, (str(path), len(raw), size)
    return {'path': str(path), 'sha256': digest, 'bytes': len(raw)}

note_pin = pin(NOTE, NOTE_SHA)
capture_pin = pin(CAPTURE, CAPTURE_SHA)
capture = json.loads(CAPTURE.read_text())
assert note_pin == capture['note']
assert capture['status'] == 'READ_ONLY_SOURCE_PINNED_PROPOSAL'
assert capture['proposed_interface'] == 'controlled_selected_word(&Bank, original_mask, limits)'
assert capture['provider_formula'] == 'sum(original_initializer_polynomial * endpoint_specialized_conditional_word_polynomial)'
assert capture['new_interface_implemented'] is False
assert capture['register_initializer_specialized'] is False
assert capture['target_processes'] == capture['compiler_processes'] == 0

certificate_path = PACKET / 'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json'
certificate_pin = pin(certificate_path, '1f45babae7a183dc1638ebfd7de210fddcf2dd872e8498f3f80ede4d06e9fcc2')
certificate = json.loads(certificate_path.read_text())
all_pins, accepted, runtime = [], [], []
for item in capture['pins']:
    actual = pin(item['path'], item['sha256'], item['bytes'])
    actual['role'] = item['role']
    actual['inspected_declarations'] = item['inspected_declarations']
    if 'accepted1504_expected_sha256' in item:
        assert item['sha256'] == item['accepted1504_expected_sha256']
        assert certificate['source_pins'][item['module']] == item['sha256']
        actual['module'] = item['module']
        accepted.append(actual)
    else:
        path = pathlib.Path(item['path'])
        if path.is_relative_to(PACKET / 'rust') and path.suffix == '.rs':
            runtime.append(actual)
    all_pins.append(actual)
assert len(all_pins) == 31
assert len(accepted) == 13
assert len(runtime) == capture['runtime_guard_count'] == 11

by_name = {pathlib.Path(item['path']).name: pathlib.Path(item['path']).read_text()
           for item in capture['pins'] if pathlib.Path(item['path']).suffix in {'.rs', '.lean', '.py'}}
assert 'register := s.register' in by_name['FiniteSourceSnapshot.lean']
assert 'history := []' in by_name['FiniteSourceSnapshot.lean']
assert '(originalRegisterPMF N p).bind' in by_name['ControlledUnrankedSourceProjectivity.lean']
assert 'MvPolynomial.rename Sum.inr (initialPolynomial N sample a) *' in by_name['G7ControlledWordPolynomial.lean']
assert 'substituteControl N mask (wordPolynomial N H (controlledMode common mask) word a b)' in by_name['G7ControlledWordPolynomial.lean']
assert 'match program.forcing[*hybrid]' in by_name['source_fit_readout.rs']
assert 'let word_table=match word::word_row(&word_request)' in by_name['source_fit_readout.rs']
assert 'Initial::Conditional(snapshot) => (snapshot.clone(), Polynomial::one(dimension))' in by_name['source_word.rs']
assert 'destination.register != snapshot.register' in by_name['source_boundary.rs']
assert 'readout::Request::natural(bank)' in by_name['source_fit_forward.rs']
compose = by_name['source_word.rs'].split('fn compose(', 1)[1].split('pub fn word_row', 1)[0]
assert compose.index('check(stage, LimitKind::Queries') < compose.index('provider_row(request,')
assert compose.index('provider_row(request,') < compose.index('check(stage, LimitKind::Branches')
assert compose.index('provider_row(request,') < compose.index('check(stage, LimitKind::TermProducts')
assert compose.index('check(stage, LimitKind::TermProducts') < compose.index('entering.polynomial.multiply(')

assessment = {
    'schema': 'independent_original_control_plan_static_qc_v1',
    'contributor': 'Codex / solver_design_recovery',
    'observed_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'PASS_STATIC_FORMULA_AND_SCOPE_WITH_EXPLICIT_RESOURCE_QUALIFICATION; proposal only',
    'reviewer': pin(__file__), 'note': note_pin, 'capture': capture_pin,
    'accepted_1504_certificate': certificate_pin,
    'source_pin_checks': {'all_current_capture_pins': 31, 'accepted_1504_provider_bindings': 13,
                          'runtime_guard_pins': 11, 'all_current_bytes_matched': True},
    'pins': all_pins,
    'mathematical_contract_assessment': {
        'classification': 'Sourced finding plus hand-derived finite assembly argument; no new kernel or runtime verification.',
        'scope': 'One original partial Boolean mask on one immutable supplied rational Bank, naturally initialized nonempty <=4-copy generated complete calendar; formal slot-bank full selected-view law with complete original register.',
        'formula': 'P_mask(view) = sum_reg I_reg(original_gamma) * endpoint_substitute_mask(K_reg, controlledMode)(view)',
        'source_basis': ['OriginalFixedIDControls.controlledGamma', 'OriginalFixedIDControls.controlledMode',
                         'OriginalFixedIDControls.actual_forced_hybrid_kernel',
                         'ControlledUnrankedSourceProjectivity.controlledCalendarLaw',
                         'G7ControlledWordPolynomial.controlledWordPolynomial',
                         'G7ControlledWordPolynomial.actual_controlled_word_polynomial'],
        'finding': 'The proposed formula places the unchanged original initializer outside endpoint substitution, exactly as the accepted controlled-word body. Forced sites switch to IH endpoint pulses; unforced COMMON sites keep the entering stored bit. All current owners are routed as whole carried genealogies, without per-tip splitting.',
        'register_retention': 'Initializer and each conditional witness/view retain the original whole V register. Forced parent selection may differ from that stored bit without changing it.',
        'orientation': 'Original true means parent1; original gamma=1-old_g, where old_g is P(parent0). Forcing b names the original incoming occurrence b; it is never complemented when gamma is converted.',
        'observer_boundary': 'Full selected-view keys retain per-copy ordered genealogy/location and every register bit, but omit representative/ancestor IDs. A selected-fibre coefficient dictionary with a literal range witness is not a dictionary of every full Code state.',
        'current_rooted_specialization': 'Current source_fit_readout constructs a Natural completed word table and substitutes ProgramTerm::forcing into every gamma power, including initializer powers, before its explicit rooted-unranked observer forgets register. Existing rooted comparisons do not establish a register-preserving control law.',
        'hand_derived_separating_example': {
            'kind': 'Algebraic consequence of the accepted initializer and control formula, not a new native run.',
            'original_gamma': '2/3', 'natural_register_false_mass': '1/3',
            'natural_register_true_mass': '2/3', 'forced_parent': 0,
            'proposed_retained_register_true_mass': '2/3',
            'global_endpoint_substitution_if_interpreted_as_register_law_true_mass': '0',
            'meaning': 'Forgetting register can hide this difference; keeping the whole register distinguishes the contracts.'},
    },
    'resource_qualification': {
        'source': 'Pinned source_word.rs compose body; independent read-only ordering check.',
        'actual_order': ['check cumulative query requirement',
                         'invoke provider_row and generate each bounded conditional provider table',
                         'compute and check cumulative branch and term-product requirements',
                         'multiply conditional transition polynomials',
                         'check output destination and normalized-term counts'],
        'required_language_for_future_freeze': 'Remaining query caps are checked before provider calls. Remaining branch/product caps are composition caps checked after bounded provider rows have been generated and before word-stage multiplication. They are not caps preventing all provider-row generation.',
        'wrapper_requirements': [
            'Validate mask/registry and Bank natural/generated/complete domain before soft limits.',
            'Precheck 2^h initializer assignments, 3^h initializer terms and the one-mask conditional-call requirement before allocating/generating those stages.',
            'Consume explicit cumulative child query/branch/product counters across every conditional call; separately account for initializer-times-transition products before that multiplication.',
            'Keep unchanged per-provider caps and their stage/kind/population/required/cap metadata, with no partial rows on UNKNOWN.',
            'Specify whether child and outer products share one aggregate counter in the implementation freeze; recommended contract uses one cumulative allowance.',
            'Cap wrapper normalized destinations/terms, checked count arithmetic, rational operand/result sizes and bounded output; account for cancellation and deterministic canonical witness selection.',
            'Keep OS/provider arithmetic qualifications explicit. Row mass or moment checking does not authenticate executed work or budget exhaustion.',
        ],
        'semantic_formula_blocker': False,
        'executed_work_bound_verified': False,
    },
    'remaining_native_binding_obligations': [
        'Exact JSON -> original registry/parallel occurrence/mask decoding and immutable shared Bank binding.',
        'Literal admitted canonical entering carrier and complete selected-fibre aggregation correspondence, including ancestor/representative variants.',
        'Conditional-only endpoint substitution, exact zero normalization, symbolic mass one and untouched natural initializer.',
        'Generated agenda/phase ordering and root support for every formal completion input before numerical/endpoint pruning.',
        'Explicit rooted observer/register forgetting, original gamma and exponent transport for any later rational evaluated consumer.',
        'Additive versioned public mask/observer envelope and independent reference extension only in a separately authorized future change; current frontend is natural-only.',
    ],
    'meaningful_future_acceptance_controls': [
        'Empty mask equals the unchanged natural full selected table.',
        'Forced parent0/parent1 with opposite entering stored bit retains original 1/3,2/3 register marginal and the addressed E occurrence.',
        'Two live IH owners, including a nonminimum representative carrying three original copies, receive deterministic owner routing without splitting the carried fibre.',
        'Parallel incoming E occurrences with equal endpoint V labels remain distinct in masks, placement and exposure.',
        'Two-hybrid partial mask leaves the other original gamma, mode and register unchanged on one bank.',
        'Low caps refuse without partial tables; malformed registry/mask is rejected before budget refusal; original child refusal metadata is preserved.',
    ],
    'claims_kept_false': ['new implementation', 'public API promotion', 'full Code native dictionary evaluation',
                         'source admission/reconstruction', 'source-equation provenance', 'timed histories',
                         'universal native refinement', 'G6/G7 master closure', 'full solver verification'],
    'source_mutations': [],
    'target_execution_in_this_review': {'producer': 0, 'compiler': 0, 'helper': 0, 'native': 0,
                                       'adapter': 0, 'reference': 0, 'fitter': 0},
    'implementation_authorized_by_this_receipt': False,
    'next_action': 'Root decides whether to freeze a later private implementation scope after the Lean-first gates; retain the precise composition-cap qualification in that freeze.',
}
# Repeat byte reads only, to bind all inspected runtime/provider pins at the end.
for item in capture['pins']:
    pin(item['path'], item['sha256'], item['bytes'])
assessment['post_review_current_capture_pins_matched'] = True
destination = OWN / 'ORIGINAL-CONTROL-PLAN-STATIC-QC-ATTEMPT1.json'
with destination.open('x') as handle:
    json.dump(assessment, handle, indent=2, ensure_ascii=False)
    handle.write('\n')
print(json.dumps(pin(destination)))
