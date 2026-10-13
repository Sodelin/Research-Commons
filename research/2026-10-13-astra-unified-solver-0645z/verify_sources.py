#!/usr/bin/env python3
"""Independently read back every selected source in a materialized package."""
import argparse
import json
from pathlib import Path

from materialize import HERE, AGGREGATE_SHA, source_path, selected_graph, sha


def verify(directory):
    graph,aggregate=selected_graph()
    expected={source_path(name):row['sha256'] for name,row in graph['modules'].items()}
    expected.update({p.relative_to(HERE/'lean'):sha(p.read_bytes()) for p in (HERE/'lean').rglob('*.lean')})
    expected[Path('Accepted1613.lean')]=AGGREGATE_SHA
    expected[Path('AstraUnified.lean')]=sha(b'import Accepted1613\nimport AstraKernel\n')
    for path,digest in expected.items():
        if sha((directory/path).read_bytes())!=digest:
            raise ValueError('source mismatch: '+str(path))
    actual={p.relative_to(directory) for p in directory.rglob('*.lean')
            if '.lake' not in p.relative_to(directory).parts}
    if actual != set(expected)|{Path('lakefile.lean')}:
        raise ValueError('unexpected or missing selected Lean source')
    manifest=json.loads((directory/'SOURCE-SELECTION.json').read_text())
    if manifest['baseline']['modules']!=graph['modules'] or manifest['baseline']['roots']!=graph['roots']:
        raise ValueError('selected dependency graph differs')
    g2=json.loads((HERE.parent/'2026-10-13-dot-g2-unified-integration-0238z/CHECK-1613.json').read_text())['g2']
    for row in g2:
        if row['module'] not in graph['roots'] or any(graph['modules'][row['module']][key]!=row[key]
                                                    for key in ['sha256','imports']):
            raise ValueError('original G2 source/import selection changed')
    return dict(status='ALL_MATERIALIZED_SOURCE_BYTES_AND_SELECTED_IMPORTS_MATCH',
                accepted_aggregate_sha256=sha(aggregate),all_68_g2_sources_preserved=len(g2)==68,
                original_selected_graph_preserved=True,compiled=False,
                physical_provider_substituted=False)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('directory',type=Path)
    a=p.parse_args()
    print(json.dumps(verify(a.directory),indent=2))


if __name__=='__main__':
    main()
