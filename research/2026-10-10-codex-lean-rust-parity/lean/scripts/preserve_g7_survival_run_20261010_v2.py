#!/usr/bin/env python3
"""Losslessly export bounded nonbinary G7 evidence; keep original scratch bytes.

Prior1497 sources remain at their already distributed immutable source paths.
Only seven additional source bodies are copied. Large JSON/loader evidence is
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
                 'MONITOR-REVIEW-CORRECTION.json', 'CACHE-SEED-RECEIPT.json', 'CACHE-TRANSPORT-PRE-USE-PLAN.json',
                 'CACHE-INSTALL-ALIASES.json', 'CACHE-INSTALL-TRANSPORT-DERIVATION.json']:
        source = work / name
        assert source.is_file()
        rows.append({**distribute_file(source, stage, Path('preparation') / name, force_gzip=source.stat().st_size >= 32768),
                     'original_path': str(source), 'original_sha256': sha(source)})
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
    evidence = ROOT / 'evidence/proof-extensions/g7-survival-integration' / work.name / (args.label + '-' + run.name)
    assert not evidence.exists()
    manifest = {'status': final['status'], 'workspace': str(work), 'actual_run': str(run),
        'evidence': str(evidence.relative_to(ROOT)), 'final_receipt': final,
        'preserved_files': rows, 'compiled_artifact_bytes_distributed': False,
        'original_attempts_overwritten': False, 'prior1497_sources_duplicated': False,
        'preparation_sha256': sha(work / 'PREPARATION.json'),
        'compressed_distributions_manifest_sha256': sha(stage / 'COMPRESSED-DISTRIBUTIONS.json'),
        'measured_export_bytes_before_manifest': export_bytes,
        'original_raw_audits_and_full_run_files_preserved_at_fixed_scratch_paths': True,
        'exporter_sha256': sha(Path(__file__))}
    save(stage / 'PRESERVATION-MANIFEST.json', manifest)
    evidence.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(stage, evidence)
    for p in stage.rglob('*'):
        if p.is_file():
            assert sha(p) == sha(evidence / p.relative_to(stage))
    result_path = ROOT / ('G7-SURVIVAL-' + args.label.upper() + '-' + run.name + '-RESULT.json')
    assert not result_path.exists()
    save(result_path, manifest)
    print(json.dumps({'status': final['status'], 'evidence': str(evidence), 'result': str(result_path),
                      'preserved_files': len(rows), 'measured_export_bytes': export_bytes}))


if __name__ == '__main__':
    main()
