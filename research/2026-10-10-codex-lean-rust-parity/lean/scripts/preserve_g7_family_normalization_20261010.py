#!/usr/bin/env python3
"""Losslessly export bounded nonbinary G7 evidence; keep original scratch bytes.

Prior1497 sources remain at their already distributed immutable source paths.
Only the new family source body is copied; parent bodies remain bound by exact immutable distributed paths. Large JSON/loader evidence is
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
                              force_gzip=source.stat().st_size >= 32768 or source.name.startswith('NATIVE-LOADER.'))
        rows.append({**row, 'original_path': str(source), 'original_sha256': sha(source)})
    for name in ['PREPARATION.json', 'DEPENDENCY-GRAPH.json', 'SOURCE-CLOSURE.json', 'SOURCE-TRANSPORT.json',
                 'FRESH-SOURCES.json', 'LOCATION-AND-COMPOSITION-DERIVATION.json', 'RESOURCE-AND-RUN-PLAN.json',
                 'CACHE-SEED-RECEIPT.json', 'CACHE-TRANSPORT-PRE-USE-PLAN.json',
                 'CACHE-INSTALL-ALIASES.json', 'CACHE-INSTALL-TRANSPORT-DERIVATION.json']:
        source = work / name
        assert source.is_file()
        rows.append({**distribute_file(source, stage, Path('preparation') / name, force_gzip=source.stat().st_size >= 32768),
                     'original_path': str(source), 'original_sha256': sha(source)})
    optional_absent = []
    for name in ['MONITOR-REVIEW-CORRECTION.json', 'PRE-USE-MONITOR-VALIDATION.json',
                 'PARTIAL-COMPONENT-ADMISSION-PROVENANCE.json', 'PRESERVATION-PREFLIGHT-FAILURE-v2.json']:
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
    assert export_bytes <= 40 * 2**20, ('Measured export exceeds explicit packet reserve', export_bytes)
    assert shutil.disk_usage(ROOT).free >= export_bytes + 16 * 2**20
    evidence = ROOT / 'evidence/proof-extensions/g7-family-normalization' / work.name / (args.label + '-' + run.name)
    assert not evidence.exists()
    manifest = {'status': final['status'], 'workspace': str(work), 'actual_run': str(run),
        'evidence': str(evidence.relative_to(ROOT)), 'final_receipt': final,
        'executed_target_module_counts': {k: len(json.loads((work / 'DEPENDENCY-GRAPH.json').read_bytes())['targets'][k]['order']) for k in final['targets_requested']},
        'guard_complete_staging_graph_modules': len(json.loads((work / 'SOURCE-CLOSURE.json').read_bytes())),
        'protected_provider_context_executed': False,
        'parent_exporter_sha256': '432f584460b087266d43681aa5d2f68b9866c328552d5e8be7ba6be02f9558ce',
        'exporter_derivation': 'Only artifact namespace and executable/staging ownership qualifications change from frozen survivalv4. Same lossless transport, all posthash reports,16MiB export reserve and raw fixed-path preservation.',
        'preserved_files': rows, 'compiled_artifact_bytes_distributed': False,
        'original_attempts_overwritten': False, 'prior1497_sources_duplicated': False,
        'preparation_sha256': sha(work / 'PREPARATION.json'),
        'compressed_distributions_manifest_sha256': sha(stage / 'COMPRESSED-DISTRIBUTIONS.json'),
        'measured_export_bytes_before_manifest': export_bytes,
        'original_raw_audits_and_full_run_files_preserved_at_fixed_scratch_paths': True,
        'explicit_optional_preparation_artifacts_absent': optional_absent,
        'post_run_transport_verification': post_transport_binding,
        'parent_exporter_path': str(Path(__file__).with_name('preserve_g7_survival_run_20261010_v3.py')),
        'parent_exporter_sha256': '629d9401104f2bfa9de2bdf65c26b897488a7bdc3e9b25d74501ea5ec556e898',
        'exporter_derivation': 'Only require, authenticate and distribute the current successful run post-transport report and bind this unchanged parent.',
        'exporter_sha256': sha(Path(__file__))}
    save(stage / 'PRESERVATION-MANIFEST.json', manifest)
    evidence.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(stage, evidence)
    for p in stage.rglob('*'):
        if p.is_file():
            assert sha(p) == sha(evidence / p.relative_to(stage))
    result_path = ROOT / ('G7-FAMILY-NORMALIZATION-' + args.label.upper() + '-' + run.name + '-RESULT.json')
    assert not result_path.exists()
    save(result_path, manifest)
    print(json.dumps({'status': final['status'], 'evidence': str(evidence), 'result': str(result_path),
                      'preserved_files': len(rows), 'measured_export_bytes': export_bytes}))


if __name__ == '__main__':
    main()
