#!/usr/bin/env python3
"""Prepare only authored/public source for the new isolated native component.

No compiler, subprocess, Git operation, object adoption or runtime record is
created by this preparation. Execution still needs the record-writer binding.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
    'build_connected.py': 'f74f8e24dd6a61f627c42e4106de442f1ba0adecaf06442b6a0a4e70cbe681be',
    'AuditTemplate.lean': 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a',
    'guard.py': 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3',
    'hosted_guard.py': '9975d91624c8783a31b7e31a20cf2cf2f45ef625c51d9b2e4e0e6a49cced60c4',
}
CERTS = [
    ('776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939',
     '510c29496c8270f0dd2c36bbcad81fe73e72b2f73cd1638316d403d1cd651c79'),
    ('e49c1e3d6bffee594b99574d3364e700e8f25342933fe31add2aa6129729bc6b',
     '0136df5150a1eb3bdb32efabf785a9f6ad53a57770c9939acc6b471834a75542'),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination.exists() or any((p / '.git').exists() for p in [destination, *destination.parents]):
        raise ValueError('NEW_NON_GIT_SOURCE_DESTINATION_REQUIRED')
    for name, expected in PINS.items():
        if hashlib.sha256((HERE / 'pinned' / name).read_bytes()).hexdigest() != expected:
            raise ValueError('REUSED_SOURCE_CHANGED: ' + name)
    library = ROOT / 'intake/commons/research/2026-10-13-astra-unified-solver-0645z/lean/Astra/CommonCertificateKernel.lean'
    raw = library.read_bytes()
    if hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest() != 'bdb5472d06592cad4ad6511d7bb893cbac7cac99':
        raise ValueError('ORIGINAL_LIBRARY_CHANGED')
    selected = [('Astra.CommonCertificateKernel', raw)]
    for identity, expected in CERTS:
        body = (ROOT / 'lean/generated' / ('Certificate_' + identity + '.lean')).read_bytes()
        if hashlib.sha256(body).hexdigest() != expected:
            raise ValueError('ORIGINAL_EMITTER_OUTPUT_CHANGED')
        selected.append(('Astra.Generated.Certificate_' + identity, body))
    graph = {'targets': {'lean-certificate-component': {
        'roots': [name for name, _ in selected],
        'order': [name for name, _ in selected],
        'required_for_accepted_release': False,
        'modules': {name: {'sha256': hashlib.sha256(body).hexdigest(),
                          'imports': [line.split()[1] for line in body.decode().splitlines()
                                      if line.startswith('import ')]} for name, body in selected}}}}
    destination.mkdir(parents=True)
    (destination / 'scripts').mkdir()
    (destination / 'source-store').mkdir()
    for name, body in selected:
        (destination / 'source-store' / (hashlib.sha256(body).hexdigest() + '.lean')).write_bytes(body)
    for name in ['build_connected.py', 'AuditTemplate.lean']:
        shutil.copyfile(HERE / 'pinned' / name, destination / 'scripts' / name)
    (destination / 'DEPENDENCY-GRAPH.json').write_text(json.dumps(graph, indent=2) + '\n')
    (destination / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    (destination / 'lake-manifest.json').write_text(json.dumps({
        'version': '1.2.0', 'packagesDir': '.lake/packages', 'packages': [],
        'name': 'leanCertificateComponent', 'lakeDir': '.lake', 'fixedToolchain': True}, indent=2) + '\n')
    # Deliberately no runnable target before the inherited writers are bound.
    (destination / 'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage leanCertificateComponent\n\n'
        'target verify _pkg : Unit := do\n'
        '  Job.async do\n'
        '    error "SOURCE_PROPOSAL_ONLY: encrypt-before-persistence runtime writer is not bound"\n')
    manifest = {'status': 'SOURCE_LAYOUT_PREPARED_NOT_EXECUTED',
                'selected_sources': graph['targets']['lean-certificate-component']['modules'],
                'reused_builder_and_audit_byte_identical': True,
                'new_runtime_record_writer': 'UNBOUND', 'compiler_invoked': False,
                'mathlib_commit': '0df444a360eaa60ab8c11dca51a86af692955474'}
    (destination / 'PREPARATION.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'source_project': str(destination), 'modules': len(selected),
                      'compiler_invoked': False, 'runtime_record_writer': 'UNBOUND'}))


if __name__ == '__main__':
    main()
