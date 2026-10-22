#!/usr/bin/env python3
"""Source companion: bounded hosted component checking, RAM capture, existing codec.

This wrapper has not itself been executed. Published actual evidence used the
same Node client through the pre-existing installed pipe binding. No local Lean,
identity initialization, key export, native build or plaintext fallback.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CASES = {
    'code-receiver': ('lean/OnlineOriginalCodeChartReceiver.lean', [
        'Astra.OriginalCodeChartReceiver.checked_original_witness',
        'Astra.OriginalCodeChartReceiver.checked_original_bank',
        'Astra.OriginalCodeChartReceiver.checked_original_bank_rates',
        'Astra.OriginalCodeChartReceiver.checked_original_bank_feasible',
        'Astra.OriginalCodeChartReceiver.checked_original_exclusion']),
    'code-chart': ('lean/OnlineOriginalCodeChartReflection.lean', [
        'Astra.OriginalCodeChartReflection.fieldReflection',
        'Astra.OriginalCodeChartReflection.decoded_emitRows_of_code',
        'Astra.OriginalCodeChartReflection.coefficient_lengths_of_code',
        'Astra.OriginalCodeChartReflection.decoded_emitRows_toFinset_of_code']),
    'aggregate': ('lean/OnlineNativeCellAggregateReflection.lean', [
        'Astra.NativeCellAggregateReflection.erase_emitRows_eq_encoded',
        'Astra.NativeCellAggregateReflection.decoded_emitRows_eq_compileCellList',
        'Astra.NativeCellAggregateReflection.emitted_coefficient_lengths',
        'Astra.NativeCellAggregateReflection.decoded_emitRows_toFinset']),
    'admission': ('lean/OnlineOriginalCodeBankLayout.lean', [
        'GProgram.G7.OriginalAdmission.sourceOfValid',
        'GProgram.G7.OriginalAdmission.decodedIDs',
        'GProgram.G7.OriginalAdmission.decoded_parent_exact',
        'Astra.OriginalCodeBankLayout.layout',
        'Astra.OriginalCodeBankLayout.hybrid_position',
        'Astra.OriginalCodeBankLayout.parent_occurrence']),
    'reject-false': ('lean/UnionCaptureRejectFalse.lean',
                     ['Astra.UnionCaptureControls.false_proof']),
    'reject-sorry': ('lean/UnionCaptureRejectSorry.lean',
                     ['Astra.UnionCaptureControls.sorry_proof']),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',required=True,choices=list(CASES))
    parser.add_argument('--record-codec',required=True,type=Path)
    parser.add_argument('--codec-sha256',required=True)
    args = parser.parse_args()
    codec = args.record_codec
    if not codec.is_absolute() or codec.is_symlink() or not codec.is_file() or digest(codec) != args.codec_sha256:
        raise ValueError('VERIFIED_EXISTING_RECORD_CODEC_REQUIRED')
    for row in json.loads((ROOT/'SOURCE-FILES.json').read_bytes())['files']:
        path = ROOT/row['path']
        if path.is_symlink() or not path.is_file() or path.stat().st_size != row['bytes'] or digest(path) != row['sha256']:
            raise ValueError('PUBLIC_SOURCE_CHANGED')
    source,audits = CASES[args.case]
    client = ROOT/'online_lean_quiet.mjs'
    before = digest(client)
    process = subprocess.run(['node',str(client),str(ROOT/source),*audits],
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=130,check=False)
    after = digest(client)
    payload = json.dumps({'case':args.case,'client_sha256':before,
        'client_sha256_after':after,'client_identity_unchanged':before == after,
        'client_exit':process.returncode,
        'original_stdout':process.stdout.decode('utf-8',errors='replace'),
        'original_stderr':process.stderr.decode('utf-8',errors='replace')}).encode()
    encrypted = subprocess.run([str(codec),'seal-stdin'],input=payload,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=40,check=False)
    if encrypted.returncode:
        raise RuntimeError('RECORD_ENCRYPTION_REFUSED_NO_PLAINTEXT_FALLBACK')
    receipt = json.loads(encrypted.stdout)
    if receipt.get('state') != 'ENCRYPTED_AND_READ_BACK' or digest(Path(receipt['record'])) != receipt['ciphertext_sha256']:
        raise RuntimeError('ENCRYPTED_READBACK_UNCONFIRMED')
    result = json.loads(process.stdout)
    status = result['status'] if before == after else 'UNVERIFIED_CLIENT_SOURCE_CHANGED'
    print(json.dumps({'case':args.case,'status':status,
        'record':receipt['record'],'ciphertext_sha256':receipt['ciphertext_sha256'],
        'local_compiler':False,'native_Lake':False},sort_keys=True))
    wanted = 'REJECTED_REMOTE_LEAN_CHECK' if args.case.startswith('reject-') else 'PASS_REMOTE_LEAN_CHECK'
    return 0 if status == wanted else 2


if __name__ == '__main__':
    sys.exit(main())
