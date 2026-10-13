#!/usr/bin/env python3
"""Authenticate and compare existing COMMON-menu/native interface contracts.

This is a compatibility report, never a graph decoder or source decision. The
accepted menu/query parsers are reused with exact source pins. Original input
bytes and typed IDs survive separately from the derived exact mask PMF.
"""
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASELINE = HERE.parent / '2026-10-13-astra-unified-solver-0645z'
PYTHON_PINS = {
    'certificates.py': 'ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3',
    'external_encoding.py': '78dfd11a8157a5102c520be85a5fc42f4b4137250846ce510df9df98a90f4d69',
}
RESTORE_MANIFEST_SHA = 'c5c84b5fa1755ae05830059353c184a77c52bd236b4053fe2668e6e30f066da6'
RUST_PREFIX = 'research/2026-10-10-codex-lean-rust-parity/rust/src/'
RUST_PINS = {
    'law.rs': 'e519d232bbea12fa7181a7f5c8c700608d2debf412e519fe7f26abc03564c8a2',
    'protocol.rs': '0bcf6e0e099d5983604c8d3e6fe189fbb0431de390b7d0f8c7306bbbced2e72a',
    'source_population.rs': '6afebffe8bb727a1c92bd113d479f01f0b2877bbf527c79866247805bc21da7c',
    'source_fit_bank.rs': 'e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a',
    'forest.rs': 'd0f284781c81b6a70c22a9bcdd21b0379eeb3032f4d3e33e6c0b8073685f0937',
}
NATIVE_COPY_CAP = 4


class ProfileUnavailable(ValueError):
    """Authentication failure is not an invalid mathematical source."""


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_pinned(path, expected, maximum=1024 * 1024):
    try:
        if path.is_symlink() or not path.is_file():
            raise ProfileUnavailable('regular source file required: ' + str(path))
        with path.open('rb') as stream:
            raw = stream.read(maximum + 1)
    except OSError as error:
        raise ProfileUnavailable('source unavailable: ' + str(path)) from error
    if len(raw) > maximum or sha(raw) != expected:
        raise ProfileUnavailable('selected source identity differs: ' + str(path))
    return raw


def providers():
    for name, expected in PYTHON_PINS.items():
        read_pinned(BASELINE / name, expected)
    sys.path.insert(0, str(BASELINE))
    try:
        modules = [importlib.import_module(name) for name in ['certificates', 'external_encoding']]
    finally:
        sys.path.pop(0)
    for module in modules:
        expected_path = BASELINE / (module.__name__ + '.py')
        if Path(module.__file__).resolve() != expected_path.resolve():
            raise ProfileUnavailable('loaded provider has a different origin')
        read_pinned(expected_path, PYTHON_PINS[expected_path.name])
    return modules


def native_profile(restored):
    if restored is None:
        raise ProfileUnavailable('configure the existing restored public source inventory')
    root = Path(restored)
    manifest = json.loads(read_pinned(root / 'RESTORED-SOURCES.json', RESTORE_MANIFEST_SHA))
    inventory = {row['path']: row for row in manifest['files']}
    for name, expected in RUST_PINS.items():
        relative = RUST_PREFIX + name
        row = inventory.get(relative)
        if row is None or row['sha256'] != expected:
            raise ProfileUnavailable('selected native source is absent from the frozen inventory')
        raw = read_pinned(root / relative, expected)
        if len(raw) != row['bytes']:
            raise ProfileUnavailable('selected native source size differs')
    return dict(restored_manifest_sha256=RESTORE_MANIFEST_SHA,
                public_recovery_commit=manifest['commit'], source_pins=dict(RUST_PINS),
                authenticated_source_files=len(RUST_PINS),
                native_binary_executed=False, copy_cap=NATIVE_COPY_CAP)


def mask_pmf(menu, certificates):
    """Derived full-mask distribution only; never rewrites the input records."""
    masses = {}
    for configuration in menu['configurations']:
        # Namespace and original hybrid label are retained; None is not a bit.
        key = tuple(sorted(configuration['mask'].items()))
        masses[key] = masses.get(key, 0) + certificates.rational(configuration['weight'])
    rows = [dict(mask=[dict(hybrid_id=label, value=value) for label, value in key],
                 weight=str(weight)) for key, weight in masses.items() if weight]
    rows.sort(key=lambda row: json.dumps(row['mask'], sort_keys=True, separators=(',', ':')))
    return dict(scope='distribution of complete protected-hybrid masks only',
                configurations_merged_in_original_request=False,
                original_configuration_ids_in_semantic_hash=False,
                zero_mass_removed_only_in_this_derived_summary=True,
                renormalized=False, rows=rows, sha256=certificates.digest(rows))


def report(raw, restored):
    certificates, encoding = providers()
    request = certificates.loads(raw)
    certificates.fields(request, ['schema', 'task', 'input'])
    certificates.require(request['schema'] == 'unified_research_solver_v1'
                         and request['task'] == 'common_menu',
                         'supply the existing unified common_menu request')
    menu = request['input']
    assessment = certificates.common_packet(menu)
    queries = encoding.fixed_queries(menu)
    profile = native_profile(restored)
    rows = []
    for query in queries['queries']:
        copies = [dict(copy_id=copy, taxon_id=taxon)
                  for copy, taxon in query['allocation'].items()]
        # These are fixed external copy labels, never candidate graph indices.
        rows.append(dict(row_sha256=query['row_sha256'],
                         certificate_sha256=query['certificate_sha256'],
                         directed_pair=query['directed_pair'], level=query['level'],
                         fixed_copy_allocation=copies, required_copy_count=len(copies),
                         native_copy_cap=NATIVE_COPY_CAP,
                         fits_native_copy_profile=len(copies) <= NATIVE_COPY_CAP,
                         selected_keep=query['readout']['keep'],
                         normalized_moment=query['normalized_moment'],
                         required_event_probability=query['required_event_probability']))
    typed_ids = {namespace: [dict(id=value, input_ordinal=i) for i, value in enumerate(values)]
                 for namespace, values in [('taxon', menu['taxa']),
                     ('protected_edge', menu['protected_edges']),
                     ('protected_hybrid', menu['protected_hybrids']),
                     ('configuration', [x['id'] for x in menu['configurations']])]}
    return dict(schema='common_native_compatibility_v1', status='UNKNOWN',
                compatibility_report_complete=True,
                reason='padded_copy_profile_exceeded_and_source_parameter_binding_unavailable',
                original_input_bytes_sha256=sha(raw if isinstance(raw, bytes) else raw.encode()),
                canonical_request_sha256=certificates.digest(request),
                canonical_menu_sha256=certificates.digest(menu),
                fixed_external_menu_sha256=certificates.digest(queries),
                reused_python_sources=dict(PYTHON_PINS), selected_native_profile=profile,
                typed_ids=typed_ids, input_ordinals_are_candidate_indices=False,
                same_text_across_id_namespaces_is_permitted=True,
                original_joint_configurations=menu['configurations'],
                derived_mask_pmf=mask_pmf(menu, certificates),
                parameter_constraints=menu['parameter_constraints'],
                source_parameter_binding=dict(status='UNBOUND',
                    protected_edge_occurrence_map=None, protected_hybrid_registry_map=None,
                    rc1_parameter='G:i is probability of original incoming[0]',
                    snapshot_parameter='Gamma is probability of original incoming[1]',
                    established_fit_conversion='Gamma = 1 - old_parent_zero_probability',
                    conversion_provider='source_fit_bank.rs::run, exposed through bind',
                    original_incoming_order_must_be_preserved=True,
                    actual_parameter_conversion_performed=False),
                rows=rows,
                conditional_arithmetic=dict(support_cap=assessment['conditional_support_cap'],
                    hybrid_budget=assessment['conditional_hybrid_budget'], applied_to_search=False),
                obligations=['native profile must carry every fixed padded copy',
                    'bind protected string IDs to original edge occurrences and hybrid registry',
                    'bind exact shared parameters using the established parent-bit convention',
                    'encode complete joint configuration masks and passive readout',
                    'authenticate same-source moments and physical admission'],
                native_execution_performed=False, source_feasibility_certified=False,
                unknown_size_exclusion_certified=False, native_refinement_proved=False,
                arbitrary_input_G3_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request', type=Path, required=True)
    parser.add_argument('--native-sources', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    try:
        with args.request.open('rb') as stream:
            raw = stream.read(262145)
        (args.output / 'REQUEST.json').write_bytes(raw)
        result = report(raw, args.native_sources)
    except ProfileUnavailable as error:
        result = dict(schema='common_native_compatibility_v1', status='UNKNOWN',
                      compatibility_report_complete=False, reason=str(error),
                      source_feasibility_certified=False, native_execution_performed=False)
    except (ValueError, TypeError, KeyError, OSError) as error:
        result = dict(schema='common_native_compatibility_v1', status='REFUSED_REQUEST',
                      compatibility_report_complete=False, reason=str(error),
                      source_feasibility_certified=False, native_execution_performed=False)
    (args.output / 'RESULT.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: result[key] for key in ['status', 'compatibility_report_complete',
                                                'source_feasibility_certified']}))
    return 2 if result['status'] == 'UNKNOWN' else 1


if __name__ == '__main__':
    raise SystemExit(main())
