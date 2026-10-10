#!/usr/bin/env python3
"""Review the preserved selected-reference run without invoking any evaluator."""
import argparse
import gzip
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    manifest_path = evidence / 'PRESERVATION-MANIFEST.json'
    require(digest(manifest_path.read_bytes()) ==
            'd1fd08652e8317ea866613c9c36bb588ee779260bab8792264e72318f0af14c7',
            'Different preservation manifest')
    manifest = load(manifest_path)
    files = manifest['preserved_files']
    require(len(files) == 322, 'Expected 322 preserved files')
    seen = set()
    for entry in files:
        path = (evidence / entry['path']).resolve()
        require(path.is_relative_to(evidence) and path not in seen, 'Unsafe or repeated path')
        seen.add(path)
        raw = path.read_bytes()
        require(digest(raw) == entry['sha256'] and len(raw) == entry['bytes'], str(path))
        restored = gzip.decompress(raw) if entry.get('encoding') == 'gzip' else raw
        require(digest(restored) == entry['original_sha256'], 'Original-byte binding')
        if entry.get('encoding') == 'gzip':
            require(len(restored) == entry['restored_bytes'] and
                    digest(restored) == entry['restored_sha256'], 'Gzip restoration')
        require(Path(entry['original_path']).read_bytes() == restored, 'Scratch bytes changed')
    elfs = manifest['excluded_ELF_inventory']
    require(len(elfs) == 9, 'Expected nine retained executables')
    for entry in elfs:
        path = Path(entry['path'])
        raw = path.read_bytes()
        require(raw.startswith(b'\x7fELF') and digest(raw) == entry['sha256'] and
                len(raw) == entry['bytes'], 'Retained executable binding')
        stat = path.stat()
        require([stat.st_dev, stat.st_ino] == entry['device_inode'], 'Executable identity changed')
    pins = manifest['pinned_source_inventory']
    require(len(pins) == 33, 'Expected 33 source pins')
    for path, expected in pins.items():
        require(digest(Path(path).read_bytes()) == expected, 'Current pin changed: ' + path)
    reviews = {}
    for phase, count in [('component', 8), ('application', 4)]:
        outer_path = evidence / phase / 'OUTER-RECEIPT.json'
        outer = load(outer_path)
        review_path = evidence / phase / 'review/RECEIPT.json'
        review = load(review_path)
        require(digest(outer_path.read_bytes()) == manifest['phase_receipts'][phase]['sha256'],
                'Outer receipt binding')
        require(outer['status'] == 'PASS_AUTHORIZED_REFERENCE_PHASE' and
                outer['exit_code'] == 0 and outer['monitor_error'] is None, 'Phase failed')
        require(load(evidence / phase / 'PRE-LAUNCH-PINS.json') == pins ==
                outer['post_pin_rechecks'], 'Before/after pin mismatch')
        require(outer['review_receipt_sha256'] == digest(review_path.read_bytes()) and
                outer['passed_controls'] == count, 'Inner receipt binding')
        require(review['status'] == 'PASS' and review['checks'] == count and
                len(review['tests']) == count and review['compiler_processes_started'] == 0,
                'Unexpected review or compiler invocation')
        require(outer['compiler_invoked'] is False and
                outer['peak_native_allocated_bytes'] < 973078528 and
                outer['peak_nonreclaimable_bytes'] < 15 * 1024**3, 'Resource guard')
        for test in review['tests']:
            require(test.get('pass_', test.get('pass')) is True, 'Control failed')
            command = test['command']
            request = Path(command[command.index('--request') + 1])
            case = request.parent.name
            base = evidence / phase / 'review' / case
            require(digest((base / 'REQUEST.json').read_bytes()) == test['request_sha256'],
                    'Request binding')
            result_path = base / ('component/RESULT.json' if phase == 'component'
                                  else 'application/RESULT.json')
            result = load(result_path)
            expected = test.get('result_sha256', test.get('application_result_sha256'))
            require(digest(result_path.read_bytes()) == expected and
                    result['status'] == test['status'] and result['exit_code'] == test['exit_code'],
                    'Result binding')
            component = result if phase == 'component' else result['component_result']
            for field in ('source_admission_verified', 'source_provenance_verified',
                          'source_observation_fit_verified', 'timed_readout_verified',
                          'full_code_evaluated', 'universal_native_refinement_verified',
                          'certificate_valid', 'full_solver_verified'):
                require(component[field] is False, 'Unsupported scope promotion: ' + field)
            if phase == 'application':
                child_path = base / 'application/component/RESULT.json'
                require(digest(child_path.read_bytes()) == test['child_result_sha256'] and
                        load(child_path) == component, 'Application child binding')
            if case == 'missing-reference':
                require(component['solver_called'] is False and component['checker_called'] is False
                        and component['reference_checker_called'] is False, 'Prelaunch refusal')
            elif case == 'native-only-default':
                require(component['reference_requested'] is False and
                        component['reference_checker_called'] is False and
                        component['independent_all_coefficients_checked'] is False,
                        'Native-only default claimed independent reference')
            elif test['exit_code'] == 0:
                require(component['reference_checker_called'] is True and
                        component['reference_baseline_called'] is True and
                        component['independent_all_coefficients_checked'] is True and
                        component['independent_probabilities_checked'] is True and
                        component['reference_identity_recheck_stable'] is True,
                        'Requested reference did not verify table')
                check = component['reference_check']
                require(check['request_sha256'] == test['request_sha256'] and
                        check['response_sha256'] == component['native_result_sha256'] and
                        check['rooted_outcomes'] == test['rooted_outcomes'], 'Reference binding')
            elif case == 'frame-only-unknown':
                require(component['reference_frame_checked'] is True and
                        component['reference_baseline_called'] is False and
                        component['independent_all_coefficients_checked'] is False,
                        'Frame-only check overstated')
            else:
                require(component['rooted_law_evaluated'] is False and
                        component['independent_all_coefficients_checked'] is False,
                        'Failed reference accepted a table')
        reviews[phase] = digest(review_path.read_bytes())
    component = load(evidence / 'component/review/RECEIPT.json')
    require(component['rooted_outcomes'] == 24 and component['whole_edge_terms'] == 49,
            'Component table totals')
    require([(x['rooted_outcomes'], x['whole_edge_terms']) for x in component['tests'][:4]] ==
            [(3, 7), (3, 13), (3, 7), (15, 22)], 'Per-case table totals')
    receipt = dict(status='PASS_SAVED_BYTE_BINDING_AND_SCOPE_REVIEW',
                   observed_utc=datetime.now(timezone.utc).isoformat(),
                   evidence=str(evidence), preservation_manifest_sha256=digest(manifest_path.read_bytes()),
                   preserved_files=322, retained_executables=9, current_pins=33,
                   component_checks=8, application_checks=4, rooted_rows=24, whole_edge_terms=49,
                   review_receipts=reviews, reviewer_sha256=digest(Path(__file__).read_bytes()),
                   producer_processes_started=0, mathematical_evaluators_started=0,
                   independent_mathematical_replay=False, full_solver_verified=False,
                   scope='Saved bytes, process receipts, refusal behavior and scope only; independent mathematical review is separate.')
    with args.output.open('x') as stream:
        json.dump(receipt, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps(receipt, sort_keys=True))


if __name__ == '__main__':
    main()
