#!/usr/bin/env python3
"""Add the support adapter to the complete authenticated1613 source package."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
PREVIOUS=HERE.parent/'2026-10-13-astra-unified-solver-0645z'
sys.path.insert(0,str(PREVIOUS))
import materialize as baseline
from verify_sources import verify as verify_baseline


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def selection():
    graph,_=baseline.selected_graph()
    selected=json.loads((HERE/'PROVIDER-SELECTION.json').read_text())
    seen=set();external=set()
    def visit(name):
        if name in seen:return
        seen.add(name)
        for imported in graph['modules'][name]['imports']:
            if imported in graph['modules']:visit(imported)
            else:external.add(imported)
    visit(selected['target'])
    owned=[dict(graph['modules'][n],module=n) for n in graph['order'] if n in seen]
    if selected['owned']!=owned or selected['external']!=sorted(external):
        raise ValueError('accepted provider selection differs from exact full graph')
    return selected


def lake_configuration(graph):
    lake=baseline.package_lakefile(graph).replace('@[default_target]\n','')
    lake=lake.replace('globs := #[.one `AstraKernel, .submodules `Astra]',
                      'globs := #[.one `AstraKernel, .one `Astra.CommonCertificateKernel]')
    modules=['.'.join(p.relative_to(HERE/'lean').with_suffix('').parts)
             for p in sorted((HERE/'lean').rglob('*.lean'))
             if p.relative_to(HERE/'lean')!=Path('Astra/CommonCertificateKernel.lean')]
    globs=', '.join('.one `'+m for m in modules)
    return lake+'\n@[default_target]\nlean_lib AstraPositiveSupport where\n  roots := #[`AstraPositiveSupport]\n  globs := #['+globs+']\nlean_lib AstraSupportUnified where\n  roots := #[`AstraSupportUnified]\n'


def materialize(destination):
    selected=selection()
    base=baseline.materialize(destination)
    verify_baseline(destination)
    (destination/'SOURCE-SELECTION.json').rename(destination/'BASELINE-SOURCE-SELECTION.json')
    new={}
    for source in sorted((HERE/'lean').rglob('*.lean')):
        relative=source.relative_to(HERE/'lean')
        target=destination/relative
        if target.exists() and target.read_bytes()!=source.read_bytes():
            raise ValueError('new source collides with unchanged baseline: '+str(relative))
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(source.read_bytes())
        new[str(relative)]=sha(source)
    (destination/'AstraSupportUnified.lean').write_text('import AstraUnified\nimport AstraPositiveSupport\n')
    graph,_=baseline.selected_graph()
    (destination/'lakefile.lean').write_text(lake_configuration(graph))
    receipt=dict(schema='astra_full1613_support_source_selection_v1',
                 accepted_graph_sha256=base['baseline']['graph_sha256'],
                 accepted_aggregate_sha256=base['baseline']['aggregate_sha256'],
                 baseline_manifest_sha256=sha(destination/'BASELINE-SOURCE-SELECTION.json'),
                 provider_selection_sha256=sha(HERE/'PROVIDER-SELECTION.json'),
                 provider_modules=selected['owned'],new_sources=new,
                 new_aggregate_sha256=sha(destination/'AstraSupportUnified.lean'),
                 lakefile_sha256=sha(destination/'lakefile.lean'),
                 toolchain_sha256=sha(destination/'lean-toolchain'),
                 full_accepted_source_graph_retained=True,all_68_g2_retained=True,
                 source_compilation_performed=False,
                 full_aggregate_compilation_claimed=False,
                 physical_provider_required=False,physical_conclusion_claimed=False)
    (destination/'SOURCE-SELECTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def verify(destination):
    graph,aggregate=baseline.selected_graph();selection()
    expected={baseline.source_path(n):r['sha256'] for n,r in graph['modules'].items()}
    expected[Path('Accepted1613.lean')]=hashlib.sha256(aggregate).hexdigest()
    expected[Path('AstraUnified.lean')]=hashlib.sha256(b'import Accepted1613\nimport AstraKernel\n').hexdigest()
    expected[Path('AstraKernel.lean')]=sha(PREVIOUS/'lean/AstraKernel.lean')
    for source in sorted((HERE/'lean').rglob('*.lean')):
        expected[source.relative_to(HERE/'lean')]=sha(source)
    expected[Path('AstraSupportUnified.lean')]=hashlib.sha256(b'import AstraUnified\nimport AstraPositiveSupport\n').hexdigest()
    receipt=json.loads((destination/'SOURCE-SELECTION.json').read_text())
    expected[Path('lakefile.lean')]=hashlib.sha256(lake_configuration(graph).encode()).hexdigest()
    original=json.loads((destination/'BASELINE-SOURCE-SELECTION.json').read_text())['baseline']
    if any(original[k]!=graph[k] for k in ['modules','order','roots','external_imports']):
        raise ValueError('baseline manifest selection changed')
    if receipt['provider_modules']!=selection()['owned'] or receipt['lakefile_sha256']!=expected[Path('lakefile.lean')]:
        raise ValueError('support selection/build manifest changed')
    for relative,digest in expected.items():
        if sha(destination/relative)!=digest:raise ValueError('source identity changed: '+str(relative))
    actual={p.relative_to(destination) for p in destination.rglob('*.lean') if '.lake' not in p.relative_to(destination).parts}
    if actual!=set(expected):raise ValueError('unexpected or missing source modules')
    if (destination/'lean-toolchain').read_bytes()!=(HERE/'lean-toolchain').read_bytes():
        raise ValueError('toolchain differs')
    return dict(status='FULL1613_AND_SUPPORT_SOURCE_BYTES_MATCH',
                full_accepted_source_graph_retained=True,all_68_g2_retained=True,
                accepted_aggregate_sha256=hashlib.sha256(aggregate).hexdigest(),
                source_compilation_performed=False)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--verify-only',action='store_true')
    a=p.parse_args()
    if not a.verify_only:materialize(a.out)
    print(json.dumps(verify(a.out)))
