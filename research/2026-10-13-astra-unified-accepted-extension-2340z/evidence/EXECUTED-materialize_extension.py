#!/usr/bin/env python3
"""Materialize one pinned source package. No compiler, downloads or old writes."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = HERE.parent / '2026-10-13-astra-unified-solver-0645z'
BASE_HELPER = 'f10224c1948c00eba566984a893ed2222b536075ec5e52cab504f4403a79e6c8'
TOOLCHAIN = '3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def selected():
    helper = BASE / 'materialize.py'
    if digest(helper.read_bytes()) != BASE_HELPER:
        raise ValueError('baseline materializer identity changed')
    spec = importlib.util.spec_from_file_location('astra_pinned_materializer', helper)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    graph, aggregate = module.selected_graph()
    catalog = json.loads((HERE / 'SOURCE-CATALOG.json').read_text())
    if catalog['baseline_graph_sha256'] != module.GRAPH_SHA:
        raise ValueError('catalog baseline graph differs')
    bodies = {}
    for row in catalog['sources']:
        name = row['module']
        relative = module.source_path(name)
        path = ROOT / row['path']
        if not path.resolve().is_relative_to(ROOT):
            raise ValueError('source leaves research workspace')
        data = path.read_bytes()
        if digest(data) != row['sha256'] or len(data) != row['bytes']:
            raise ValueError('selected source identity changed: ' + name)
        if name in graph['modules']:
            raise ValueError('new module replaces accepted source: ' + name)
        if relative in bodies and bodies[relative] != data:
            raise ValueError('new module has conflicting bodies: ' + name)
        bodies[relative] = data
    kernel = {p.relative_to(BASE / 'lean'): p.read_bytes()
              for p in (BASE / 'lean').rglob('*.lean')}
    if any(bodies.get(path) != data for path, data in kernel.items()):
        raise ValueError('baseline kernel body is absent or changed')
    if digest((BASE / 'lean-toolchain').read_bytes()) != TOOLCHAIN:
        raise ValueError('toolchain identity changed')
    names = set(graph['modules']) | {'.'.join(p.with_suffix('').parts) for p in bodies}
    names |= {'Accepted1613', 'AstraUnified'} | set(graph['external_imports'])
    for external in catalog['new_external_imports']:
        module.source_path(external)
        if not external.startswith('Mathlib.'):
            raise ValueError('new external root is outside pinned Mathlib')
        names.add(external)
    imports = {}
    for path, data in bodies.items():
        name = '.'.join(path.with_suffix('').parts)
        imports[name] = re.findall(r'^import\s+(\S+)\s*$', data.decode(), re.MULTILINE)
        if any(dep not in names for dep in imports[name]):
            raise ValueError('new module imports unselected body: ' + name)
    return module, graph, aggregate, bodies, catalog, imports


def configuration(graph, bodies):
    groups = {
        'Accepted1613': ['Accepted1613', *graph['order']],
        'AstraKernel': ['AstraKernel', 'Astra.CommonCertificateKernel'],
        'AstraCertificates': [],
        'AstraPositiveSupport': ['Astra.PositiveSupportAdapter', 'Astra.EmittedSupportExamples', 'AstraPositiveSupport'],
        'AstraGeneratedSupport': ['AstraGeneratedSupport'],
        'AstraLegalRowSupport': ['Astra.ActualLegalRowSupport', 'AstraLegalRowSupport'],
        'AstraSelectedCopy': ['Astra.SelectedCopyReadout', 'AstraSelectedCopy'],
        'AstraUnified': ['AstraUnified'],
        'AstraIntegrationIncrement': ['AstraIntegrationIncrement'],
        'AstraAcceptedIntegration': ['AstraAcceptedIntegration'],
    }
    for path in sorted(bodies):
        name = '.'.join(path.with_suffix('').parts)
        if name.startswith('Certificate_'):
            groups['AstraCertificates'].append(name)
        elif name.startswith('Support_'):
            groups['AstraGeneratedSupport'].append(name)
    allocated = [name for values in groups.values() for name in values]
    expected = set(graph['modules']) | {'.'.join(p.with_suffix('').parts) for p in bodies}
    expected |= {'Accepted1613', 'AstraUnified'}
    if len(allocated) != len(set(allocated)) or set(allocated) != expected:
        raise ValueError('Lake ownership omits or repeats selected modules')
    text = ('import Lake\nopen Lake DSL\npackage astraAcceptedIntegration\n'
            'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "' + MATHLIB + '"\n')
    for library, names in groups.items():
        text += '\n' + ('@[default_target]\n' if library == 'AstraAcceptedIntegration' else '')
        text += 'lean_lib ' + library + ' where\n'
        roots = names if library == 'AstraCertificates' else [library]
        text += '  roots := #[' + ', '.join('`' + name for name in roots) + ']\n'
        text += '  globs := #[' + ', '.join('.one `' + name for name in names) + ']\n'
    return text


def materialize(destination):
    module, graph, aggregate, bodies, catalog, imports = selected()
    lakefile = configuration(graph, bodies)
    # Existing directories are refused by the authenticated baseline helper.
    baseline = module.materialize(destination)
    (destination / 'SOURCE-SELECTION.json').rename(destination / 'BASELINE-SOURCE-SELECTION.json')
    for relative, data in bodies.items():
        target = destination / relative
        if target.exists() and target.read_bytes() != data:
            raise ValueError('new body collides with baseline: ' + str(relative))
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    (destination / 'lakefile.lean').write_text(lakefile)
    expected = {module.source_path(name): row['sha256'] for name, row in graph['modules'].items()}
    expected.update({p: digest(data) for p, data in bodies.items()})
    expected[Path('Accepted1613.lean')] = digest(aggregate)
    expected[Path('AstraUnified.lean')] = digest(b'import Accepted1613\nimport AstraKernel\n')
    expected[Path('lakefile.lean')] = digest(lakefile.encode())
    actual = {p.relative_to(destination) for p in destination.rglob('*.lean')}
    if actual != set(expected) or any(digest((destination / p).read_bytes()) != pin for p, pin in expected.items()):
        raise ValueError('materialized sources differ from selected package')
    report = dict(schema='astra_unified_accepted_extension_v1',
        baseline=baseline['baseline'], catalog_sha256=digest((HERE / 'SOURCE-CATALOG.json').read_bytes()),
        new_sources=catalog['sources'], new_imports=imports,
        new_external_import_roots=catalog['new_external_imports'],
        sources={str(path): pin for path, pin in expected.items()},
        baseline_helper_sha256=BASE_HELPER, lakefile_sha256=digest(lakefile.encode()),
        toolchain_sha256=TOOLCHAIN, all_68_g2_retained=True,
        source_authentication='exact selected bodies retained; no compilation or object authentication performed',
        compiled=False, new_targets_compiled=False, physical_representative_proved=False,
        excluded_missing_provider=module.MISSING,
        excluded_consumer='G3CertifiedCommonBoundedWitness: required exact provider body unavailable',
        prose_only_incoming_results='Not converted into axioms or imported as machine proofs.')
    (destination / 'SOURCE-SELECTION.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    report = materialize(args.out.resolve())
    print(json.dumps(dict(status='PINNED_UNIFIED_SOURCE_PACKAGE_MATERIALIZED',
        compiled=False, catalog_sha256=report['catalog_sha256'],
        lakefile_sha256=report['lakefile_sha256'])))
