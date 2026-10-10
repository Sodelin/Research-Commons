#!/usr/bin/env python3
"""Check preserved fitter-transport bindings; never launch mathematical tools."""
import argparse
import gzip
import json
from datetime import datetime, timezone
from pathlib import Path

from review_selected_reference_saved import digest, load, require


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    root = args.evidence.resolve()
    manifest_path = root / 'PRESERVATION-MANIFEST.json'
    require(digest(manifest_path.read_bytes()) ==
            '32ceb0a880bf2c9c731d233c3b440b0171053156b788003f3c1e1dab7c730e3c',
            'Different transport manifest')
    manifest = load(manifest_path)
    require(len(manifest['preserved_files']) == 95, 'Preserved file count')
    seen = set()
    for entry in manifest['preserved_files']:
        path = (root / entry['path']).resolve()
        require(path.is_relative_to(root) and path not in seen, 'Unsafe or repeated evidence path')
        seen.add(path)
        raw = path.read_bytes()
        require(digest(raw) == entry['sha256'] and len(raw) == entry['bytes'], 'Stored-byte binding')
        restored = gzip.decompress(raw) if entry.get('encoding') == 'gzip' else raw
        require(digest(restored) == entry['original_sha256'] and
                Path(entry['original_path']).read_bytes() == restored, 'Original-byte binding')
        if entry.get('encoding') == 'gzip':
            require(digest(restored) == entry['restored_sha256'] and
                    len(restored) == entry['restored_bytes'], 'Gzip restoration')
    require(len(manifest['excluded_ELF_inventory']) == 1, 'Retained executable count')
    for entry in manifest['excluded_ELF_inventory']:
        raw = Path(entry['path']).read_bytes()
        require(raw.startswith(b'\x7fELF') and digest(raw) == entry['sha256'] and
                len(raw) == entry['bytes'], 'Retained executable binding')
    pins = manifest['pinned_source_inventory']
    require(len(pins) == 50, 'Source pin count')
    for path, expected in pins.items():
        require(digest(Path(path).read_bytes()) == expected, 'Current source pin: ' + path)
    outer_path = root / 'transport/OUTER-RECEIPT.json'
    outer = load(outer_path)
    inner_path = root / 'transport/review/RECEIPT.json'
    inner = load(inner_path)
    require(digest(outer_path.read_bytes()) == manifest['phase_receipts']['transport']['sha256'],
            'Outer receipt binding')
    require(outer['exit_code'] == 0 and outer['monitor_error'] is None and
            outer['status'] == 'PASS_AUTHORIZED_REFERENCE_PHASE' and
            outer['passed_controls'] == 34, 'Outer status')
    require(outer['review_receipt_sha256'] == digest(inner_path.read_bytes()) and
            outer['post_pin_rechecks'] == pins == load(root / 'transport/PRE-LAUNCH-PINS.json'),
            'Inner receipt and before/after source binding')
    require(inner['status'] == 'PASS' and inner['checks_passed'] == 34 and
            len(inner['checks']) == 34 and all(t['pass'] is True for t in inner['checks']),
            'Control results')
    for field in ('fitter_processes_started', 'semantic_source_checker_processes_started',
                  'compiler_processes_started'):
        require(inner[field] == 0, 'Unexpected producer execution')
    require(outer['peak_native_allocated_bytes'] < 939524096 and
            outer['peak_nonreclaimable_bytes'] < 15 * 1024**3, 'Resource guard')
    base = root / 'transport/review'
    export = base / 'exported-cli'
    raw = (export / 'BACKEND-RESULT.json').read_bytes()
    require(raw == (base / 'hybrid-common-sat.BACKEND-RESULT.json').read_bytes(), 'Raw backend preservation')
    backend = json.loads(raw)
    origin = load(export / 'ORIGIN.json')
    request_raw = (export / 'SOURCE-FIT-REQUEST.json').read_bytes()
    require(origin['raw_backend_sha256'] == digest(raw) and
            origin['native_request_sha256'] == digest(request_raw), 'Origin/request byte bindings')
    require(origin['original_request'] == backend['request'] and
            origin['selected_entry_index'] == backend['witness_entry'] and
            origin['selected_entry'] == backend['entries'][backend['witness_entry']],
            'Lossless original request and selected entry')
    require(origin['all_original_rows_retained'] is True and
            origin['all_supplied_equations_retained'] is True and
            origin['original_observation_rows'] == len(backend['request']['rows']) == 4 and
            origin['supplied_equations'] == len(origin['selected_entry']['equations']) == 12,
            'Original rows and complete trace')
    require(origin['selected_row'] == backend['request']['rows'][origin['selected_panel_row_index']]
            and origin['selected_row_actions_retained'] is True and
            origin['selected_experiment_reproduced'] is False, 'Selected panel qualification')
    application = load(base / 'application/RESULT.json')
    component = load(base / 'application/component/RESULT.json')
    require(application['component_result'] == component and
            application['request_bytes_sha256'] == digest(request_raw) and
            (base / 'application/REQUEST.json').read_bytes() == request_raw and
            component['request_sha256'] == digest(request_raw), 'Application binding')
    require(application['status'] == 'SUPPLIED_FIT_ROOTED_LAW' and
            component['exit_code'] == 0 and component['native_replay_verified'] is True and
            component['independent_all_coefficients_checked'] is True and
            component['independent_probabilities_checked'] is True and
            component['reference_baseline_called'] is True, 'Actual checked readout')
    check = component['reference_check']
    require(check['rooted_outcomes'] == 3 and check['whole_edge_terms'] == 7 and
            check['response_sha256'] == component['native_result_sha256'], 'Reference/table binding')
    require(digest((base / 'application/component/NATIVE-RESULT.json').read_bytes()) ==
            component['native_result_sha256'] == inner['checks'][-1]['native_table_sha256'] ==
            '3f21282fe0bdc8ecba4e8d4b4779ce3dfc3677bf4bccf904ff367c760b966039',
            'Exact earlier natural table bytes')
    require([p['returncode'] for p in inner['processes']] == [0, 1, 0],
            'Export/create-new refusal/application process outcomes')
    for obj in (origin, application, component):
        for field in ('certificate_valid', 'source_admission_verified', 'source_provenance_verified',
                      'source_observation_fit_verified', 'timed_readout_verified',
                      'universal_native_refinement_verified', 'full_solver_verified'):
            require(obj[field] is False, 'Scope promotion: ' + field)
    receipt = dict(status='PASS_SAVED_TRANSPORT_BYTE_BINDING_AND_SCOPE_REVIEW',
                   observed_utc=datetime.now(timezone.utc).isoformat(),
                   preservation_manifest_sha256=digest(manifest_path.read_bytes()),
                   outer_receipt_sha256=digest(outer_path.read_bytes()),
                   actual_review_sha256=digest(inner_path.read_bytes()),
                   reviewer_sha256=digest(Path(__file__).read_bytes()),
                   saved_review_helper_sha256=digest(Path(__file__).with_name('review_selected_reference_saved.py').read_bytes()),
                   preserved_files=95, retained_executables=1, current_pins=50, controls=34,
                   original_rows=4, original_equations=12, actual_pipeline_rooted_rows=3,
                   actual_pipeline_terms=7, producer_processes_started=0,
                   mathematical_evaluators_started=0, independent_mathematical_replay=False,
                   selected_experiment_reproduced=False, full_solver_verified=False)
    with args.output.open('x') as stream:
        json.dump(receipt, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps(receipt, sort_keys=True))


if __name__ == '__main__':
    main()
