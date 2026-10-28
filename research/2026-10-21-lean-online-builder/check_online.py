#!/usr/bin/env python3
"""Finite public-source check; RAM-only transport and existing-codec records.

The caller supplies its already verified record CLI; no identity is initialized
or exported. The Node process executes no local Lean compiler. Raw child output
is captured before projection and sealed before this program persists anything.
"""
import argparse
import json
from pathlib import Path
import sys
from online_capture import run_case

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
    return run_case(ROOT, args.case, source, audits,
        'online_lean.mjs', 'online_lean.mjs', args.record_codec,
        args.codec_sha256, Path(__file__).name)


if __name__ == '__main__':
    sys.exit(main())
