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
    'G6NaturalCellOrderedCompiler', 'G7OriginalAdmission', 'GParity.Chart',
    'G7EncodedMergerSupport']
ACCEPTED_MASTER_ROOTS = ['G1FullOriginalClassMasterAndSharpness',
    'UnifiedLean.Source.SourceUnrankedAllPanels', 'G2TimedOutputForgetting',
    'G5M3NormalizedClusterSplitIdentification']


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
    parser.add_argument('--include-accepted-masters', action='store_true',
                        help='Include the exact inherited G1/G2/G5 endpoint closures as SOURCE ONLY.')
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

    selected_roots = PHYSICAL_ROOTS + (ACCEPTED_MASTER_ROOTS if args.include_accepted_masters else [])
    for name in selected_roots:
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
         '9a8cb5634c358627aee56339206e97c1f2c0c2c2b393bdd4151a041a88366208'),
        ('NativeCellFormReflection',
         '29ed474cd1a291bc2855775b22b0726c8aae34113d62efcead283d487aa9a0de'),
        ('NativeCellAggregateReflection',
         '6df93dd4ae74f3b12adcda4c59bece901e7a6bacb47e8f27dedd52650d3657f2'),
        ('OriginalCodeChartReflection',
         '521b33b18a71aa45bd0b0064eebc81e5240aa31b6d20b07a057ca91dd4027d1a'),
        ('OriginalCodeChartReceiver',
         '6ef95d3610cecc5b35cb77a4e2a9964651e20bb09d00272772835d91debd07f1'),
        ('G7FinitePathBudgetBridge',
         '901ed36d65848fe0d1ac88a6b4bc70931273c7b043094fa9dc66b29fa422f5d2'),
        ('G7FinitePathGame',
         '0d48c2129e951f278c3c30e986fa6a054500cc0e7a9230a6cfe024d81da8a990'),
        ('G7ExactLawSourceTransfer',
         'e8f713f2f123ec55f97168c92b724b01af5b0835bbe90cc6308e8749ea31423a'),
        ('G7PaddedResponseCarrier',
         'b12c8626f6d9b2d6f1d35646f091cc04a682d25f482493ad2065242a70b1060d'),
        ('TwoTipSourceDeclarations',
         '1afa303d7ee2f28fba18fa719139acbf701ac24e10b4f00365cb2c6e69193a19'),
        ('TwoTipOriginalCodeReceiver',
         'b20f2ca4357c3edf626be2714901cb417425d7d904395f0757c3c149da2fd41d'),
        ('G7FixedCalendarPowerDomain',
         'b9fabd9e48c66f5e8a53ac43284f51c286c925147a66411dd6693dedd07e0892'),
        ('G7FiniteTargetReceiver',
         '8b62a562599b6cb7f4ecc64e9dc802ff150010f80463ec36356665d76e251357')]:
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
    # Reuse only immutable authored source bodies, never historical objects/jobs.
    retained_sources = {}
    for directory in (ROOT/'native').glob('prepared-*/source-store'):
        for path in directory.glob('*.lean'):
            retained_sources.setdefault(path.stem, path)

    def acquire(name):
        digest = modules[name]['sha256']
        candidates = [ROOT/'intake/modules'/(name+'.lean'),
            ROOT/'native/prepared-physical-pmf-form-project545/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-pmf-layout-project543/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-pmf-admission-project541/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-pmf-ordered-project540/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-pmf-project534/source-store'/(digest+'.lean'),
            ROOT/'native/prepared-physical-project230/source-store'/(digest+'.lean')]
        local = next((p for p in candidates if p.exists()), retained_sources.get(digest))
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
        if args.include_accepted_masters and name == 'build_connected.py':
            # The completed loader successor is installed after exact graph
            # and selection creation below. Preserve the older pin separately.
            continue
        shutil.copyfile(HERE/'pinned'/name,destination/'scripts'/name)
    graph = {'targets':{'physical-pmf-certificate-new-context':{
        'roots':selected_roots+['CMFinitePMF']+
            ['Astra.Generated.BankWitness_'+identity for identity,_ in BANKS]+
            ['OriginalCodeBankLayout','NativeCellFormReflection','NativeCellAggregateReflection',
             'OriginalCodeChartReflection','OriginalCodeChartReceiver','G7FinitePathBudgetBridge',
             'G7FinitePathGame','G7ExactLawSourceTransfer','G7PaddedResponseCarrier',
             'TwoTipOriginalCodeReceiver','G7FixedCalendarPowerDomain','G7FiniteTargetReceiver'],
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
    if args.include_accepted_masters:
        from install_retained_loader import install_loader
        install_loader(destination)
    sys.path.insert(0,str(ROOT))
    from peer_message import seal
    receipt,_ = seal({'action':'LEAN-PRIOR-SOLUTION-ENCODED-SUPPORT-REUSE-20261022-r34',
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
