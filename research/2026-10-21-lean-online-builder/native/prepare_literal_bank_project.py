#!/usr/bin/env python3
"""Prepare nine source modules for a NEW pinned native literal-bank context.

No compiler, Git, object cache or held job is invoked. The only source variant
changes RationalBankMoments' Real import path; hosted originals stay unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
from prepare_project import PINS, CERTS, install_outer_refusal

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BANKS = [
 ('4efaf02ca21e032cc08c26d2901d8fe3d11a5d2909894a3c0caea77bffe0c8e8',
  'c886167ec2a6ee3d94af103d74dfcb7172e4856db6bfc614c798c95373958968'),
 ('d71c2bf0e0153f8103feb7a65084e462c4b20ea5bc823ace0312057491697979',
  '919f5f8190adc9fcda1d8e00e84d7bbf000b3798c16aa976d279005e87a31e9d'),
]


def checked(path, digest):
    body = path.read_bytes()
    if hashlib.sha256(body).hexdigest() != digest:
        raise ValueError('CHECKED_SOURCE_CHANGED: '+path.name)
    return body


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination',type=Path)
    parser.add_argument('--packet-root',type=Path,required=True)
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination.exists() or any((p/'.git').exists() for p in [destination,*destination.parents]):
        raise ValueError('NEW_NON_GIT_SOURCE_DESTINATION_REQUIRED')
    packet = args.packet_root.resolve()
    selected = []
    for name, digest in [
        ('CMSparseSupplier','f5477531d3b79ed65c7eb0e549bd653e40a90ce5a710bdf745363287a339c9fd'),
        ('CMFoundations','f082c4b32e4ca0a6450d0bb009a2327c3386c38c31e0d7981fab7e2b26115945')]:
        selected.append((name,checked(packet/'lean'/(name+'.lean'),digest)))
    hosted = checked(packet/'lean/RationalBankMoments.lean',
        '3a09d2a5d30c0d346484802c5e18ecc20c33efe3aabb50849f0b3efcaf4976af')
    old_import = b'import Mathlib.Basic.Real.Basic\n'
    new_import = b'import Mathlib.Data.Real.Basic\n'
    if not hosted.startswith(old_import) or hosted.count(old_import)!=1:
        raise ValueError('EXACT_IMPORT_VARIANT_REQUIRED')
    pinned = new_import+hosted[len(old_import):]
    selected.append(('RationalBankMoments',pinned))
    selected.append(('CMRationalBank',checked(packet/'lean/CMRationalBank.lean',
        '879518802d5bbe0ce1e2cf6392a0a6cbe8b70fc9fedb421035ad129684f0530e')))
    selected.append(('Astra.CommonCertificateKernel',checked(packet/'lean/Astra/CommonCertificateKernel.lean',
        '1f35f9e11cef727b27ed30230a390ada2a32dfc50733ea0d4cb172fb7c053266')))
    for identity, digest in CERTS:
        selected.append(('Astra.Generated.Certificate_'+identity,
            checked(packet/'lean/generated'/('Certificate_'+identity+'.lean'),digest)))
    for identity, digest in BANKS:
        selected.append(('Astra.Generated.BankWitness_'+identity,
            checked(packet/'lean/generated'/('BankWitness_'+identity+'.lean'),digest)))
    for name, digest in PINS.items():
        checked(HERE/'pinned'/name,digest)
    modules = {name:{'sha256':hashlib.sha256(body).hexdigest(),
        'imports':[line.split()[1] for line in body.decode().splitlines() if line.startswith('import ')]}
        for name,body in selected}
    roots = [name for name,_ in selected[-2:]]
    graph = {'targets':{'literal-bank-new-pinned-context':{
        'roots':roots,'order':[name for name,_ in selected],'modules':modules,
        'required_for_accepted_release':False}}}
    destination.mkdir(parents=True)
    (destination/'source-store').mkdir()
    (destination/'scripts').mkdir()
    for _,body in selected:
        (destination/'source-store'/(hashlib.sha256(body).hexdigest()+'.lean')).write_bytes(body)
    for name in ['build_connected.py','AuditTemplate.lean']:
        shutil.copyfile(HERE/'pinned'/name,destination/'scripts'/name)
    (destination/'DEPENDENCY-GRAPH.json').write_text(json.dumps(graph,indent=2)+'\n')
    (destination/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    admission = install_outer_refusal(destination)
    (destination/'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage literalBankNewContext\n\n'
        'target verify _pkg : Unit := do\n  Job.async do\n'
        '    error "SOURCE_ONLY: native encrypt-before-persistence writers remain UNBOUND"\n')
    manifest = {'source_only':True,'native_record_writer_required':True,
        'admission':admission,
        'mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474','modules':modules,
        'separate_import_variant':{'module':'RationalBankMoments',
          'hosted_sha256':hashlib.sha256(hosted).hexdigest(),
          'pinned_sha256':hashlib.sha256(pinned).hexdigest(),
          'only_change':'Mathlib.Basic.Real.Basic -> Mathlib.Data.Real.Basic'},
        'scope':'Literal supplied-bank mathematics; not generic native refinement, physical source admission or previous job replay.'}
    (destination/'SOURCE-SELECTION.json').write_text(json.dumps(manifest,indent=2)+'\n')
    sys.path.insert(0,str(ROOT))
    from peer_message import seal
    receipt,_ = seal({'action':'LEAN-LITERAL-BANK-PINNED-PREPARE-20261021-r1',
        'selected_source_manifest':manifest,'graph_sha256':hashlib.sha256(
            (destination/'DEPENDENCY-GRAPH.json').read_bytes()).hexdigest(),
        'compiler_invoked':False,'native_writer':'UNBOUND'})
    print(json.dumps({'modules_source_prepared':len(selected),'compiler_invoked':False,
        'pinned_rational_bank_sha256':hashlib.sha256(pinned).hexdigest(),
        'native_record_writer':'UNBOUND','encrypted_receipt':receipt}))


if __name__ == '__main__':
    main()
