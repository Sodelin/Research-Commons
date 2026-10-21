#!/usr/bin/env python3
"""Finite public-source check; RAM-only transport and existing-codec records.

The caller supplies its already verified record CLI; no identity is initialized
or exported. The Node process executes no local Lean compiler. Raw child output
is captured before projection and sealed before this program persists anything.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
KERNEL_AUDITS = [
    'squareTerm_nonnegative', 'square_identity_nonnegative',
    'supported_atom_is_root', 'joint_supported_bank_is_root',
    'singleton_generator_identity', 'singleton_generator_nonnegative',
    'singleton_generator_annihilates', 'singleton_generator_nonzero',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True, choices=['two', 'three', 'probe', 'reject-false', 'reject-sorry'])
    parser.add_argument('--record-codec', required=True, type=Path)
    parser.add_argument('--codec-sha256', required=True)
    args = parser.parse_args()
    codec = args.record_codec
    if not codec.is_absolute() or codec.is_symlink() or not codec.is_file():
        raise ValueError('VERIFIED_EXISTING_RECORD_CODEC_REQUIRED')
    if hashlib.sha256(codec.read_bytes()).hexdigest() != args.codec_sha256:
        raise ValueError('RECORD_CODEC_HASH_MISMATCH')
    inventory = json.loads((ROOT / 'SOURCE-FILES.json').read_text())['files']
    for row in inventory:
        path = ROOT / row['path']
        if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
            raise ValueError('PUBLIC_SOURCE_CHANGED')
    cases = {r['fixture']: r for r in json.loads((ROOT / 'lean/generated/SOURCE-MAP.json').read_text())['sources']}
    if args.case in cases:
        source = cases[args.case]['online_bundle']
        audits = ['Astra.CommonCertificateKernel.' + n for n in KERNEL_AUDITS] + cases[args.case]['audits']
    else:
        source, audits = {
            'probe': ('lean/OnlineTransportProbe.lean', ['online_transport_probe']),
            'reject-false': ('lean/controls/RejectFalse.lean', ['reject_false_control']),
            'reject-sorry': ('lean/controls/RejectSorry.lean', ['reject_sorry_control']),
        }[args.case]
    client = ROOT / 'online_lean.mjs'
    original = subprocess.run(['node', str(client), str(ROOT / source), *audits],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=130, check=False)
    payload = json.dumps({'case': args.case, 'client_sha256': hashlib.sha256(client.read_bytes()).hexdigest(),
                          'client_exit': original.returncode,
                          'original_stdout': original.stdout.decode('utf-8', errors='replace'),
                          'original_stderr': original.stderr.decode('utf-8', errors='replace')}).encode()
    # subprocess.PIPE supplies actual OS pipes; Node spawnSync socket stdio is
    # deliberately not used with the native codec's direct-network syscall guard.
    encrypted = subprocess.run([str(codec), 'seal-stdin'], input=payload,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               timeout=40, check=False)
    if encrypted.returncode:
        raise RuntimeError('RECORD_ENCRYPTION_REFUSED_NO_PLAINTEXT_FALLBACK')
    receipt = json.loads(encrypted.stdout)
    if receipt.get('state') != 'ENCRYPTED_AND_READ_BACK':
        raise RuntimeError('RECORD_ENCRYPTION_UNCONFIRMED')
    if hashlib.sha256(Path(receipt['record']).read_bytes()).hexdigest() != receipt['ciphertext_sha256']:
        raise RuntimeError('ENCRYPTED_READBACK_CHANGED')
    result = json.loads(original.stdout)
    print(json.dumps({'case': args.case, 'status': result['status'],
                      'record': receipt['record'], 'ciphertext_sha256': receipt['ciphertext_sha256'],
                      'local_lean_compiler': False, 'lake_build': False}, sort_keys=True))
    rejected = result['status'] == 'REJECTED_REMOTE_LEAN_CHECK'
    expected_rejection = args.case.startswith('reject-')
    return 0 if (rejected if expected_rejection else result['status'] == 'PASS_REMOTE_LEAN_CHECK') else 2


if __name__ == '__main__':
    sys.exit(main())
