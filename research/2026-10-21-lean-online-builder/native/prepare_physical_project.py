#!/usr/bin/env python3
"""Prepare a NEW source-only physical G6/G7 closure; never run a compiler.

Use the exact current/connected graph, not the union of historical targets.
Public source acquisition is bounded and each body is SHA256 checked before
its source-store write. The generated Lake target refuses while the native
first-persistence writers remain unbound. No Git command is executed.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
GRAPH_SHA = '768e587ffb189b3700aa4acc82853dcced49477b80c028d70e055d40cf65ff13'
COMMIT = '1138a5b1a281caa00b38e0976db95b586938754b'
SOURCE_PREFIX = 'research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/'
ROOTS = ['G7RawCalendarRoot','G7OriginalCarrierCoverage',
         'G7OriginalFamilyCalendarNormalization','G6RationalNaturalCellWitness',
         'G6OriginalWholeEdgeChartConsumer']
PINS = {
 'build_connected.py':'f74f8e24dd6a61f627c42e4106de442f1ba0adecaf06442b6a0a4e70cbe681be',
 'AuditTemplate.lean':'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a',
}


def selection(raw):
    if hashlib.sha256(raw).hexdigest() != GRAPH_SHA:
        raise ValueError('PINNED_GRAPH_CHANGED')
    original = json.loads(raw)['targets']['current/connected']
    modules = original['modules']
    visiting, finished, order = set(), set(), []
    def visit(name):
        if name in finished:
            return
        if name in visiting:
            raise ValueError('PROJECT_IMPORT_CYCLE')
        visiting.add(name)
        for dependency in modules[name]['imports']:
            if dependency in modules:
                visit(dependency)
        visiting.remove(name)
        finished.add(name)
        order.append(name)
    for name in ROOTS:
        visit(name)
    selected = {name:{'sha256':modules[name]['sha256'],
                      'imports':modules[name]['imports']} for name in order}
    return {'targets':{'physical-g6-g7-new-context':{
        'roots':ROOTS,'order':order,'modules':selected,
        'required_for_accepted_release':False}},
        'source_epoch':{'commit':COMMIT,'original_target':'current/connected',
                        'original_graph_sha256':GRAPH_SHA},
        'scope':'New source selection only; no historical build replay or acceptance transfer.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination',type=Path)
    parser.add_argument('--graph',type=Path,default=ROOT/'intake/DEPENDENCY-GRAPH-1138.json')
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination.exists() or any((p/'.git').exists() for p in [destination,*destination.parents]):
        raise ValueError('NEW_NON_GIT_DESTINATION_REQUIRED')
    graph = selection(args.graph.read_bytes())
    entries = graph['targets']['physical-g6-g7-new-context']['modules']
    for name, expected in PINS.items():
        if hashlib.sha256((HERE/'pinned'/name).read_bytes()).hexdigest() != expected:
            raise ValueError('REUSED_BUILDER_SOURCE_CHANGED')
    destination.mkdir(parents=True)
    (destination/'source-store').mkdir()
    (destination/'scripts').mkdir()
    for name in PINS:
        shutil.copyfile(HERE/'pinned'/name,destination/'scripts'/name)
    (destination/'DEPENDENCY-GRAPH.json').write_text(json.dumps(graph,indent=2)+'\n')
    (destination/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    (destination/'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage physicalG6G7NewContext\n\n'
        'target verify _pkg : Unit := do\n  Job.async do\n'
        '    error "SOURCE_ONLY: native encrypt-before-persistence writers remain UNBOUND"\n')
    # Acquire sources, not compiler objects, caches, tools or Git state.
    def acquire(item):
        name, entry = item
        local = ROOT/'intake/modules'/(name+'.lean')
        if local.exists():
            body = local.read_bytes()
        else:
            completed = subprocess.run(['gh','api','repos/Sodelin/Research-Commons/contents/'+
                SOURCE_PREFIX+entry['sha256']+'.lean?ref='+COMMIT,
                '-H','Accept: application/vnd.github.raw+json'],
                stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=40,check=False)
            if completed.returncode:
                raise ValueError('PUBLIC_SOURCE_READ_REFUSED: '+name)
            body = completed.stdout
        if len(body)>1024*1024 or hashlib.sha256(body).hexdigest()!=entry['sha256']:
            raise ValueError('PUBLIC_SOURCE_IDENTITY_REFUSED: '+name)
        (destination/'source-store'/(entry['sha256']+'.lean')).write_bytes(body)
        return {'module':name,'sha256':entry['sha256'],'bytes':len(body)}
    with ThreadPoolExecutor(max_workers=3) as pool:
        rows = list(pool.map(acquire,entries.items()))
    # The static source map is a reproducible build input. Runtime completion
    # evidence goes only through the existing encrypted phone record writer.
    (destination/'SOURCE-SELECTION.json').write_text(json.dumps({
        'commit':COMMIT,'original_graph_sha256':GRAPH_SHA,'roots':ROOTS,
        'sources':rows,'native_record_writer_required':True},indent=2)+'\n')
    sys.path.insert(0,str(ROOT))
    from peer_message import seal
    receipt,_ = seal({'action':'LEAN-PHYSICAL-SOURCE-PREPARE-20261021-r1',
        'source_graph_sha256':hashlib.sha256((destination/'DEPENDENCY-GRAPH.json').read_bytes()).hexdigest(),
        'source_selection_sha256':hashlib.sha256((destination/'SOURCE-SELECTION.json').read_bytes()).hexdigest(),
        'sources':rows,'compiler_invoked':False,'runtime_writer':'UNBOUND'})
    print(json.dumps({'modules_source_verified':len(rows),'compiler_invoked':False,
        'native_record_writer':'UNBOUND','encrypted_receipt':receipt}))


if __name__ == '__main__':
    main()
