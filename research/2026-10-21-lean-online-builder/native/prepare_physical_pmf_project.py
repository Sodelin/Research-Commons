#!/usr/bin/env python3
"""Prepare one source-only physical/CM/certificate import context.

No compiler, object cache, Git command, native writer or historical job runs.
The original physical sparse supplier replaces its extracted duplicate only
through a separately identified CMFoundations import variant.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
from prepare_physical_project import GRAPH_SHA, COMMIT, SOURCE_PREFIX, PINS
from prepare_project import CERTS, install_outer_refusal
from prepare_literal_bank_project import BANKS

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PHYSICAL_ROOTS = ['G7RawCalendarRoot', 'G7OriginalCarrierCoverage',
    'G7OriginalFamilyCalendarNormalization', 'G6RationalNaturalCellWitness',
    'G6OriginalWholeEdgeChartConsumer', 'G4WholeProfileDetermination',
    'G6NaturalCellOrderedCompiler', 'G7OriginalAdmission']


def checked(path, digest):
    body = path.read_bytes()
    if hashlib.sha256(body).hexdigest() != digest:
        raise ValueError('SOURCE_CHANGED: ' + path.name)
    return body


def imports(body):
    return [line.split()[1] for line in body.decode().splitlines()
            if line.startswith('import ')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    parser.add_argument('--packet-root', type=Path, required=True)
    parser.add_argument('--graph', type=Path,
                        default=ROOT/'intake/DEPENDENCY-GRAPH-1138.json')
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination.exists() or any((p/'.git').exists() for p in [destination, *destination.parents]):
        raise ValueError('NEW_NON_GIT_DESTINATION_REQUIRED')
    packet = args.packet_root.resolve()
    original = json.loads(checked(args.graph, GRAPH_SHA))['targets']['current/connected']['modules']
    order, seen, active = [], set(), set()

    def visit(name):
        if name in seen:
            return
        if name in active:
            raise ValueError('PROJECT_IMPORT_CYCLE')
        active.add(name)
        for dependency in original[name]['imports']:
            if dependency in original:
                visit(dependency)
        active.remove(name)
        seen.add(name)
        order.append(name)

    for name in PHYSICAL_ROOTS:
        visit(name)
    modules = {name: {'sha256': original[name]['sha256'],
                       'imports': original[name]['imports']} for name in order}
    for name, digest in PINS.items():
        checked(HERE/'pinned'/name, digest)

    additions, variants = [], []
    foundations = checked(packet/'lean/CMFoundations.lean',
        'f082c4b32e4ca0a6450d0bb009a2327c3386c38c31e0d7981fab7e2b26115945')
    before, after = b'import CMSparseSupplier\n', b'import G4ActualSparseCertificateExistence\n'
    if not foundations.startswith(before) or foundations.count(before) != 1:
        raise ValueError('EXACT_CM_IMPORT_REQUIRED')
    physical_foundations = after + foundations[len(before):]
    additions.append(('CMFoundations', physical_foundations))
    variants.append({'module':'CMFoundations',
        'original_sha256':hashlib.sha256(foundations).hexdigest(),
        'variant_sha256':hashlib.sha256(physical_foundations).hexdigest(),
        'only_change':'import CMSparseSupplier -> import G4ActualSparseCertificateExistence'})
    rational = checked(packet/'lean/RationalBankMoments.lean',
        '3a09d2a5d30c0d346484802c5e18ecc20c33efe3aabb50849f0b3efcaf4976af')
    before, after = b'import Mathlib.Basic.Real.Basic\n', b'import Mathlib.Data.Real.Basic\n'
    if not rational.startswith(before) or rational.count(before) != 1:
        raise ValueError('EXACT_REAL_IMPORT_REQUIRED')
    pinned_rational = after + rational[len(before):]
    additions.append(('RationalBankMoments', pinned_rational))
    variants.append({'module':'RationalBankMoments',
        'original_sha256':hashlib.sha256(rational).hexdigest(),
        'variant_sha256':hashlib.sha256(pinned_rational).hexdigest(),
        'only_change':'Mathlib.Basic.Real.Basic -> Mathlib.Data.Real.Basic'})
    for name, rel, digest in [
        ('CMRationalBank','lean/CMRationalBank.lean',
         '879518802d5bbe0ce1e2cf6392a0a6cbe8b70fc9fedb421035ad129684f0530e'),
        ('CMFinitePMF','lean/CMFinitePMF.lean',
         'f23c4428e1f5bad8f2d3675caa1684b66377acf4cfe34451b6be767d4e97d4c7'),
        ('Astra.CommonCertificateKernel','lean/Astra/CommonCertificateKernel.lean',
         '1f35f9e11cef727b27ed30230a390ada2a32dfc50733ea0d4cb172fb7c053266')]:
        additions.append((name, checked(packet/rel, digest)))
    for identity, digest in CERTS:
        additions.append(('Astra.Generated.Certificate_'+identity,
            checked(packet/'lean/generated'/('Certificate_'+identity+'.lean'), digest)))
    for identity, digest in BANKS:
        additions.append(('Astra.Generated.BankWitness_'+identity,
            checked(packet/'lean/generated'/('BankWitness_'+identity+'.lean'), digest)))
    for name, digest in [
        ('NativeOrderedBankLayout',
         '00d0b83e92f5d182b25f590b005f6ef95879f79f5adba18b6997e20b33b4e51a'),
        ('OriginalCodeBankLayout',
         'ef18d6a1e282ba479f83db56339ecd4529f3ed2469995f9a674f5fc8ea5f0bb8')]:
        additions.append((name, checked(packet/'lean'/(name+'.lean'), digest)))
    for name, body in additions:
        if name in modules or any(dep not in modules and not dep.startswith(('Mathlib.', 'Init', 'Std'))
                                  for dep in imports(body)):
            raise ValueError('NEW_MODULE_COLLISION_OR_MISSING_IMPORT: '+name)
        modules[name] = {'sha256':hashlib.sha256(body).hexdigest(),'imports':imports(body)}
        order.append(name)
    if 'CMSparseSupplier' in modules or any('CMSparseSupplier' in row['imports'] for row in modules.values()):
        raise ValueError('DUPLICATE_EXTRACTED_SUPPLIER_REFUSED')

    destination.mkdir(parents=True)
    (destination/'source-store').mkdir()
    (destination/'scripts').mkdir()

    def acquire(name):
        digest = modules[name]['sha256']
        candidates = [ROOT/'intake/modules'/(name+'.lean'),
            ROOT/'native/prepared-physical-pmf-admission-project541/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-pmf-ordered-project540/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-pmf-project534/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-project230/source-store'/(digest+'.lean')]
        local = next((p for p in candidates if p.exists()), None)
        if local:
            body = checked(local, digest)
        else:
            result = subprocess.run(['gh','api','repos/Sodelin/Research-Commons/contents/'+
                SOURCE_PREFIX+digest+'.lean?ref='+COMMIT,
                '-H','Accept: application/vnd.github.raw+json'],
                stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=40,check=False)
            if result.returncode:
                raise ValueError('PUBLIC_SOURCE_READ_REFUSED: '+name)
            body = result.stdout
        if len(body)>1024*1024 or hashlib.sha256(body).hexdigest()!=digest:
            raise ValueError('PUBLIC_SOURCE_IDENTITY_REFUSED: '+name)
        (destination/'source-store'/(digest+'.lean')).write_bytes(body)
        return {'module':name,'sha256':digest,'bytes':len(body),'source':'original/current/connected'}

    original_order = [name for name in order if name in original]
    with ThreadPoolExecutor(max_workers=3) as pool:
        rows = list(pool.map(acquire, original_order))
    for name, body in additions:
        digest = hashlib.sha256(body).hexdigest()
        (destination/'source-store'/(digest+'.lean')).write_bytes(body)
        rows.append({'module':name,'sha256':digest,'bytes':len(body),'source':'explicit owned source or import-only variant'})
    for name in PINS:
        shutil.copyfile(HERE/'pinned'/name,destination/'scripts'/name)
    graph = {'targets':{'physical-pmf-certificate-new-context':{
        'roots':PHYSICAL_ROOTS+['CMFinitePMF']+
            ['Astra.Generated.BankWitness_'+identity for identity,_ in BANKS]+
            ['OriginalCodeBankLayout'],
        'order':order,'modules':modules,'required_for_accepted_release':False}},
        'original_source_commit':COMMIT,'original_graph_sha256':GRAPH_SHA,
        'scope':'Source-only proposed combined context; no historical acceptance transfer.'}
    (destination/'DEPENDENCY-GRAPH.json').write_text(json.dumps(graph,indent=2)+'\n')
    (destination/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    admission = install_outer_refusal(destination)
    (destination/'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage physicalPMFCertificateNewContext\n\n'
        'target verify _pkg : Unit := do\n  Job.async do\n'
        '    error "SOURCE_ONLY: native encrypt-before-persistence writers remain UNBOUND"\n')
    manifest = {'source_only':True,'sources':rows,'import_variants':variants,
        'admission':admission,
        'duplicate_extracted_supplier_present':False,
        'mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474',
        'native_record_writer_required':True,
        'full_import_elaboration_run':False,'native_compiler_invoked':False}
    (destination/'SOURCE-SELECTION.json').write_text(json.dumps(manifest,indent=2)+'\n')
    sys.path.insert(0,str(ROOT))
    from peer_message import seal
    receipt,_ = seal({'action':'LEAN-PHYSICAL-PMF-LAYOUT-CONTEXT-PREPARE-20261021-r3',
        'source_graph_sha256':hashlib.sha256((destination/'DEPENDENCY-GRAPH.json').read_bytes()).hexdigest(),
        'source_selection_sha256':hashlib.sha256((destination/'SOURCE-SELECTION.json').read_bytes()).hexdigest(),
        'modules_source_verified':len(rows),'source_bytes':sum(row['bytes'] for row in rows),
        'native_record_writer':'UNBOUND','compiler_invoked':False})
    print(json.dumps({'modules_source_verified':len(rows),
        'original_physical_modules':len(original_order),
        'source_bytes':sum(row['bytes'] for row in rows),
        'compiler_invoked':False,'native_record_writer':'UNBOUND','encrypted_receipt':receipt}))


if __name__ == '__main__':
    main()
