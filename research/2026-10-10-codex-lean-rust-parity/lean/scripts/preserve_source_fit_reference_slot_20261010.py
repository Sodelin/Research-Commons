#!/usr/bin/env python3
"""Losslessly preserve a focused reference slot without distributing native ELF.

Original scratch files, source snapshots and executable paths remain unchanged.
Every omitted staged executable has its exact path/hash/size/inode recorded.
"""
import argparse
import json
from pathlib import Path
import shutil

from check_core import save, sha
from evidence_distribution import distribute_file

PACKET = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('workspace', type=Path)
    parser.add_argument('--label', required=True)
    args = parser.parse_args()
    assert args.label.replace('-', '').replace('_', '').isalnum()
    work = args.workspace.resolve(strict=True)
    plan = json.loads((work / 'PLAN.json').read_bytes())
    stage = work / ('lossless-reference-export-' + args.label)
    assert not stage.exists()
    stage.mkdir()
    preserved = []
    executables = []
    for source in sorted(work.rglob('*')):
        relative = source.relative_to(work)
        if relative.parts[0].startswith('lossless-reference-export-') or not source.is_file() or source.is_symlink():
            continue
        with source.open('rb') as stream:
            magic = stream.read(4)
        if magic == b'\x7fELF':
            st = source.stat()
            executables.append({'path': str(source), 'sha256': sha(source), 'bytes': st.st_size,
                'device_inode': [st.st_dev, st.st_ino], 'qualification': 'Preserved exact scratch executable; excluded from distributed text evidence.'})
            continue
        preserved.append({**distribute_file(source, stage, relative, force_gzip=source.stat().st_size >= 32768),
            'original_path': str(source), 'original_sha256': sha(source)})
    bytes_before_manifest = sum(p.stat().st_size for p in stage.rglob('*') if p.is_file())
    assert bytes_before_manifest <= 16 * 2**20
    assert shutil.disk_usage(PACKET).free > bytes_before_manifest + 16 * 2**20
    evidence = PACKET / 'rust/evidence' / (work.name.removeprefix('rc-') + '-' + args.label)
    assert not evidence.exists()
    phases = {}
    for phase in ['component', 'application']:
        receipt = work / phase / 'OUTER-RECEIPT.json'
        if receipt.exists():
            phases[phase] = {'path': str(receipt), 'sha256': sha(receipt),
                'status': json.loads(receipt.read_bytes())['status']}
    manifest = {'status': 'PASS_LOSSLESS_FOCUSED_REFERENCE_SLOT_PRESERVATION',
        'workspace': str(work), 'evidence': str(evidence), 'plan_sha256': sha(work / 'PLAN.json'),
        'phase_receipts': phases, 'preserved_files': preserved, 'excluded_ELF_inventory': executables,
        'raw_scratch_files_unchanged': True, 'old_native_or_source_bytes_modified_by_exporter': False,
        'native_or_compiler_processes_started_by_exporter': 0, 'measured_export_bytes_before_manifest': bytes_before_manifest,
        'exporter_sha256': sha(Path(__file__)), 'pinned_source_inventory': plan['pins'],
        'source_closure_qualification': 'Original immutable source-freeze snapshots and captured staged checker sources are bound by the pre/post runtime pins; no entire third-party interpreter verification is claimed.'}
    save(stage / 'PRESERVATION-MANIFEST.json', manifest)
    evidence.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(stage, evidence)
    for p in stage.rglob('*'):
        if p.is_file():
            assert sha(p) == sha(evidence / p.relative_to(stage))
    print(json.dumps({'evidence': str(evidence), 'preserved_files': len(preserved),
        'excluded_ELFs': len(executables), 'measured_export_bytes': bytes_before_manifest,
        'preservation_manifest_sha256': sha(evidence / 'PRESERVATION-MANIFEST.json'), 'phases': phases}))


if __name__ == '__main__':
    main()
