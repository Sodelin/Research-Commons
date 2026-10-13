#!/usr/bin/env python3
"""Authenticate and materialize the exact accepted graph plus the new kernel.

No compiler is launched. The missing physical provider is never replaced.
Only a fresh destination is accepted; previously selected bytes are immutable.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT / 'research/2026-10-12-dot-accepted-connected-union1613-1737z'
BASE_COMMIT = '7239e89dea5caad68a54227cee3b44a7d9b96389'
GRAPH_SHA = '768e587ffb189b3700aa4acc82853dcced49477b80c028d70e055d40cf65ff13'
AGGREGATE_SHA = 'bb2e98be6151f3ee9379f247cc8e8f2e47bfcbaaff991c331ef6d3298a49bf19'
MISSING = dict(module='G4ProtectedCommonRepresentative',
               sha256='0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source_path(module):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', module):
        raise ValueError('unsafe module name: ' + module)
    return Path(*module.split('.')).with_suffix('.lean')


def selected_graph():
    raw = (BASE / 'DEPENDENCY-GRAPH.json').read_bytes()
    if sha(raw) != GRAPH_SHA:
        raise ValueError('accepted dependency graph identity changed')
    graph = json.loads(raw)['targets']['current/connected']
    modules = graph['modules']
    if len(graph['order']) != len(set(graph['order'])) or set(graph['order']) != set(modules):
        raise ValueError('invalid selected module order')
    seen = set()
    for name in graph['order']:
        row = modules[name]
        source_path(name)
        if row.get('module',name) != name:
            raise ValueError('module key mismatch')
        if any(dep in modules and dep not in seen for dep in row['imports']):
            raise ValueError('dependency order mismatch: ' + name)
        data = (BASE / 'source-store' / (row['sha256'] + '.lean')).read_bytes()
        if sha(data) != row['sha256']:
            raise ValueError('accepted source identity mismatch: ' + name)
        seen.add(name)
    aggregate = ''.join('import ' + name + '\n' for name in graph['roots']).encode()
    if sha(aggregate) != AGGREGATE_SHA:
        raise ValueError('accepted aggregate identity mismatch')
    return graph, aggregate


def package_lakefile(graph):
    names=['Accepted1613',*graph['order']]
    globs=',\n    '.join('.one `'+name for name in names)
    return '''import Lake
open Lake DSL
package astraUnifiedSources
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
@[default_target]
lean_lib AstraKernel where
  roots := #[`AstraKernel]
  globs := #[.one `AstraKernel, .submodules `Astra]
lean_lib Accepted1613 where
  roots := #[`Accepted1613]
  globs := #[%s]
lean_lib AstraUnified where
  roots := #[`AstraUnified]
''' % globs


def materialize(destination):
    graph, aggregate = selected_graph()
    # Authenticate all bodies before creating any output.
    kernel = {p.relative_to(HERE/'lean'): p.read_bytes() for p in (HERE/'lean').rglob('*.lean')}
    selected_paths = {source_path(name) for name in graph['modules']}
    if selected_paths.intersection(kernel) or Path('Accepted1613.lean') in selected_paths:
        raise ValueError('new source collides with accepted module')
    destination.mkdir(parents=True, exist_ok=False)
    for name, row in graph['modules'].items():
        target = destination / source_path(name)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((BASE/'source-store'/(row['sha256']+'.lean')).read_bytes())
    for path, data in kernel.items():
        target = destination/path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    (destination/'Accepted1613.lean').write_bytes(aggregate)
    (destination/'AstraUnified.lean').write_text('import Accepted1613\nimport AstraKernel\n')
    (destination/'lean-toolchain').write_bytes((HERE/'lean-toolchain').read_bytes())
    # A normal source package for downstream consumers. The guarded receipt
    # path is provided by this packet's custom Lake targets, not a naked build.
    (destination/'lakefile.lean').write_text(package_lakefile(graph))
    receipt = dict(schema='astra_unified_source_selection_v1',
                   baseline=dict(commit=BASE_COMMIT, packet=str(BASE.relative_to(ROOT)),
                                 graph_sha256=GRAPH_SHA, aggregate_sha256=AGGREGATE_SHA,
                                 modules=graph['modules'], order=graph['order'], roots=graph['roots'],
                                 external_imports=graph['external_imports'],
                                 component_execution='historical authenticated reuse; not rebuilt here',
                                 acceptance='ACCEPTANCE.json', verifier='verify_public_packet.py'),
                   new_sources={str(p): dict(bytes=len(data), sha256=sha(data)) for p,data in kernel.items()},
                   unified_aggregate_sha256=sha((destination/'AstraUnified.lean').read_bytes()),
                   lakefile_sha256=sha((destination/'lakefile.lean').read_bytes()),
                   toolchain_sha256=sha((destination/'lean-toolchain').read_bytes()),
                   unavailable_physical_provider=MISSING,
                   physical_consumer='../2026-10-13-dot-g3-certified-consumer-0631z/G3CertifiedCommonBoundedWitness.lean',
                   physical_consumer_status='not imported: exact required provider unavailable',
                   g2_scope='All 68 selected current sources retained with original bodies and imports.',
                   compiled=False)
    (destination/'SOURCE-SELECTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True)
    a = p.parse_args()
    r = materialize(a.out)
    print(json.dumps(dict(status='AUTHENTICATED_SOURCES_MATERIALIZED', destination=str(a.out),
                         aggregate_sha256=r['baseline']['aggregate_sha256'],
                         compiled=False, physical_provider_status='UNAVAILABLE')))


if __name__ == '__main__':
    main()
