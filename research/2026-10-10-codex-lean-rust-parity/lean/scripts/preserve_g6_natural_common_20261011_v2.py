#!/usr/bin/env python3
"""Losslessly export bounded nonbinary G6 natural COMMON evidence; keep original scratch bytes.

Prior1497 sources remain at their already distributed immutable source paths.
Only the two new natural COMMON source bodies is copied; parent bodies remain bound by exact immutable distributed paths. Large JSON/loader evidence is
compressed before packet capacity is checked; no object, raw audit duplicate,
original receipt rewrite, or implicit historical pass promotion is permitted.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil

from check_core import save, sha
from evidence_distribution import distribute_file

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('workspace', type=Path)
    parser.add_argument('--run', type=Path)
    parser.add_argument('--label', required=True)
    args = parser.parse_args()
    assert args.label.replace('-', '').replace('_', '').isalnum()
    work = args.workspace.resolve(strict=True)
    final_path = args.run / 'FINAL-RECEIPT.json' if args.run else work / '.build/LATEST-RUN.json'
    final = json.loads(final_path.read_bytes())
    run = Path(final['run'])
    assert run.is_relative_to(work) and (run / 'FINAL-RECEIPT.json').exists()
    stage = work / 'lossless-export' / (args.label + '-' + run.name)
    assert not stage.exists()
    stage.mkdir(parents=True)
    rows = []
    for source in sorted(run.rglob('*')):
        relative = source.relative_to(run)
        if source.is_symlink() or not source.is_file() or 'objects' in relative.parts:
            continue
        if source.suffix in ['.olean', '.ilean', '.ir', '.private', '.server']:
            continue
        row = distribute_file(source, stage, relative,
                              force_gzip=source.suffix != '.gz' and (source.stat().st_size >= 32768 or source.name.startswith('NATIVE-LOADER.')))
        rows.append({**row, 'original_path': str(source), 'original_sha256': sha(source)})
    for name in ['PREPARATION.json', 'DEPENDENCY-GRAPH.json', 'SOURCE-CLOSURE.json', 'SOURCE-TRANSPORT.json',
                 'FRESH-SOURCES.json', 'LOCATION-AND-COMPOSITION-DERIVATION.json', 'RESOURCE-AND-RUN-PLAN.json',
                 'CACHE-SEED-RECEIPT.json', 'CACHE-TRANSPORT-PRE-USE-PLAN.json',
                 'CACHE-INSTALL-ALIASES.json', 'CACHE-INSTALL-TRANSPORT-DERIVATION.json',
                 'STDERR-STORAGE-POLICY.json', 'PARENT-WRAPPER-EQUIVALENCE.json']:
        source = work / name
        assert source.is_file()
        rows.append({**distribute_file(source, stage, Path('preparation') / name, force_gzip=source.stat().st_size >= 32768),
                     'original_path': str(source), 'original_sha256': sha(source)})
    optional_absent = []
    for name in ['MONITOR-REVIEW-CORRECTION.json', 'PRE-USE-MONITOR-VALIDATION.json',
                 'PARTIAL-COMPONENT-ADMISSION-PROVENANCE.json', 'PRESERVATION-PREFLIGHT-FAILURE-v2.json',
                 'EXPORT-PARALLEL-HEADROOM-PREFLIGHT-FAILURE-20261010.json',
                 'PRE-USE-STATIC-MEASUREMENT-20261010.json', 'PREPARATION-INVOCATION-QUALIFICATION.json']:
        source = work / name
        if source.is_file():
            rows.append({**distribute_file(source, stage, Path('preparation') / name, force_gzip=source.stat().st_size >= 32768),
                         'original_path': str(source), 'original_sha256': sha(source)})
        else:
            optional_absent.append({'path': name, 'qualification': 'Not applicable to this dated context; the current guard hash and provenance are bound by its preparation/run plan.'})
    post_transport = work / ('POST-RUN-TRANSPORT-REHASH-' + run.name + '.json')
    post_transport_binding = None
    if final['status'] == 'PASS_ALL_REQUESTED_TARGETS':
        checked = json.loads(post_transport.read_bytes())
        assert checked['status'] == 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION'
        assert checked['run'] == str(run) and checked['final_receipt_sha256'] == sha(run / 'FINAL-RECEIPT.json')
        post_transport_binding = {'original_path': str(post_transport), 'original_sha256': sha(post_transport)}
        rows.append({**distribute_file(post_transport, stage, Path('post-run') / post_transport.name,
                                       force_gzip=post_transport.stat().st_size >= 32768),
                     **post_transport_binding})
    fresh = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
    for module, row in fresh.items():
        source = work / 'source-store' / (row['sha256'] + '.lean')
        assert sha(source) == row['sha256']
        rows.append({**distribute_file(source, stage, Path('sources') / (module + '.lean')),
                     'original_path': str(source), 'original_sha256': sha(source)})
    guard_root = work / 'guard-runs'
    for guard in sorted(guard_root.iterdir()):
        receipt = guard / 'RECEIPT.json'
        if not receipt.exists():
            continue
        g = json.loads(receipt.read_bytes())
        # Frozen core events do not print their run path. Each guarded phase is
        # unique in this dated workspace, so use its exact requested target.
        if g['target'] not in final['targets_requested']:
            continue
        for source in sorted(guard.iterdir()):
            if source.is_file():
                rows.append({**distribute_file(source, stage, Path('resource-guard') / guard.name / source.name,
                                              force_gzip=source.stat().st_size >= 32768),
                             'original_path': str(source), 'original_sha256': sha(source)})
    save(stage / 'COMPRESSED-DISTRIBUTIONS.json', {'status': 'PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION',
         'distributions': [r for r in rows if r.get('encoding') == 'gzip'], 'original_run_unchanged': True})
    export_bytes = sum(p.stat().st_size for p in stage.rglob('*') if p.is_file())
    assert export_bytes <= 8 * 2**20, ('Measured export exceeds explicit packet reserve', export_bytes)
    packet_evidence = ROOT / 'evidence/proof-extensions/g6-natural-common-factorization' / work.name / (args.label + '-' + run.name)
    free_before = shutil.disk_usage(ROOT).free
    reserve = 8 * 2**20
    # The complete lossless stage is always preserved before deciding distribution.
    # Reserve an additional64KiB for this manifest/result, beyond the measured bodies.
    copy_to_packet = free_before >= export_bytes + reserve + 65536
    evidence = packet_evidence if copy_to_packet else stage
    assert not packet_evidence.exists()
    manifest = {'status': final['status'], 'workspace': str(work), 'actual_run': str(run),
        'evidence': str(evidence.relative_to(ROOT)) if copy_to_packet else str(evidence), 'final_receipt': final,
        'lossless_distribution': 'PACKET_COPY' if copy_to_packet else 'FIXED_SHMEM_EXPORT_ONLY_EXPLICIT_CAPACITY_BOUNDARY',
        'complete_lossless_export_original': str(stage),
        'packet_distribution_complete': copy_to_packet,
        'overlay_capacity_preflight': {'free_before_bytes': free_before, 'transient_reserve_bytes': reserve,
            'measured_payload_bytes': export_bytes, 'manifest_and_result_reserve_bytes': 65536,
            'source_or_evidence_deleted': False},
        'executed_target_module_counts': {k: len(json.loads((work / 'DEPENDENCY-GRAPH.json').read_bytes())['targets'][k]['order']) for k in final['targets_requested']},
        'guard_complete_staging_graph_modules': len(json.loads((work / 'SOURCE-CLOSURE.json').read_bytes())),
        'protected_provider_context_executed': False,
        'historical_export_policy': 'Same accepted Family-v2 eightMiB headroom rationale: Git object/index writes use a separate measured pool. Current Root authorized measured packet export or explicitly bound fixed shmem lossless fallback; no deletion or math run policy change.',
        'preserved_files': rows, 'compiled_artifact_bytes_distributed': False,
        'original_attempts_overwritten': False, 'prior1497_sources_duplicated': False,
        'preparation_sha256': sha(work / 'PREPARATION.json'),
        'compressed_distributions_manifest_sha256': sha(stage / 'COMPRESSED-DISTRIBUTIONS.json'),
        'measured_export_bytes_before_manifest': export_bytes,
        'original_raw_audits_and_full_run_files_preserved_at_fixed_scratch_paths': True,
        'explicit_optional_preparation_artifacts_absent': optional_absent,
        'post_run_transport_verification': post_transport_binding,
        'parent_exporter_path': str(Path(__file__).with_name('preserve_g6_parallel_arm_transport_20261010.py')),
        'parent_exporter_sha256': 'a60c9a16fd1641e40bda49d3a42d8c5dde5d44830a01942a1244e9ddef98c154',
        'exporter_derivation': 'Natural scope/count filenames,8MiB portable reserve, required storage policy/parent-source derivation and identity-preserving already-gzip distribution replace the accepted G6 exporter. All decoded evidence, failures, full raw runs, source, resource and transport checks remain required. Combined stderr is already gzip; its encoded identity is distributed unchanged and its capture descriptor binds raw decoded identity.',
        'natural_exporter_parent_sha256': '8eb80aa506cf29e59035968975ff63f2e1feca2be37ff85b2becefc6eceab366',
        'natural_exporter_v2_derivation': 'Only add the actual relative capture-gate launch working-directory qualification to optional preserved preparation evidence; all byte distributions, reserves, fallback and checks unchanged.',
        'exporter_sha256': sha(Path(__file__))}
    save(stage / 'PRESERVATION-MANIFEST.json', manifest)
    if copy_to_packet:
        exact_bytes = sum(p.stat().st_size for p in stage.rglob('*') if p.is_file())
        assert shutil.disk_usage(ROOT).free >= exact_bytes + reserve
        evidence.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(stage, evidence)
        for p in stage.rglob('*'):
            if p.is_file():
                assert sha(p) == sha(evidence / p.relative_to(stage))
    result_path = ROOT / ('G6-NATURAL-COMMON-FACTORIZATION-' + args.label.upper() + '-' + run.name + '-RESULT.json')
    assert not result_path.exists()
    save(result_path, manifest)
    print(json.dumps({'status': final['status'], 'evidence': str(evidence), 'result': str(result_path),
                      'preserved_files': len(rows), 'measured_export_bytes': export_bytes,
                      'packet_distribution_complete': copy_to_packet, 'fixed_lossless_stage': str(stage),
                      'overlay_free_after_bytes': shutil.disk_usage(ROOT).free}))


if __name__ == '__main__':
    main()
