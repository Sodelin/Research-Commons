#!/usr/bin/env python3
"""Prepare the retained P1/P5 components; never construct or invoke a builder."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

from prepare_project import install_outer_refusal

HERE = Path(__file__).resolve().parent
INPUTS = '96c1a06b26ba27b51804b4e62b26f93d5f3b477eb93b72f8bc018c09ebd81922'
TEMPLATE = 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a'
SELECTED_AUDIT = '9ed8e5c886ffe2fd0965e6e33a5b6d95df885ab26693edb2db50844e396e51dd'
LABEL = 'materials-components-provisional'


def checked(path, expected):
    raw = path.read_bytes()
    if path.is_symlink() or hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError('EXACT_MATERIALS_SOURCE_REQUIRED: '+path.name)
    return raw


def document(value):
    return (json.dumps(value, indent=2)+'\n').encode()


def source_plan():
    """Only authenticated authored source inputs; no object or runtime admission."""
    inputs = json.loads(checked(HERE/'materials/SOURCE-INPUTS.json', INPUTS))
    checked(HERE/'pinned/AuditTemplate.lean', TEMPLATE)
    checked(HERE/'materials/SelectedEndpointAudit.lean', SELECTED_AUDIT)
    rows = inputs['sources']
    names = inputs['order']
    if (len(rows) != 10 or len(names) != len(set(names))
            or {r['module'] for r in rows} != set(names)):
        raise ValueError('COMPLETE_TEN_COMPONENTS_REQUIRED')
    by_name = {row['module']: row for row in rows}
    bodies, modules, selected, variants = {}, {}, [], []
    for name in names:
        row = by_name[name]
        raw = checked(HERE/'materials/lean'/(name+'.lean'), row['sha256'])
        original = checked(HERE.parent/'lean'/(name+'.lean'), row['original_sha256'])
        reconstructed = original
        for change in row['changes']:
            before = ('import '+change['from']+'\n').encode()
            after = ('import '+change['to']+'\n').encode()
            if reconstructed.count(before) != 1:
                raise ValueError('EXACT_IMPORT_REPLACEMENT_REQUIRED: '+name)
            reconstructed = reconstructed.replace(before, after)
        if reconstructed != raw or len(raw) != row['bytes']:
            raise ValueError('NONIMPORT_BODY_CHANGED: '+name)
        deps = [line.split()[1] for line in raw.decode().splitlines()
                if line.startswith('import ')]
        if deps != row['imports'] or any(d in by_name and d not in modules for d in deps):
            raise ValueError('INTERNAL_DEPENDENCY_ORDER_REQUIRED: '+name)
        if any(d not in by_name and d not in inputs['external_imports'] for d in deps):
            raise ValueError('UNREVIEWED_EXTERNAL_IMPORT: '+name)
        bodies[row['sha256']] = raw
        modules[name] = {'sha256': row['sha256'], 'imports': deps}
        selected.append({'module': name, 'sha256': row['sha256'],
                         'bytes': len(raw), 'source': 'explicit owned source or import-only variant'})
        if row['changes']:
            variants.append({'module': name, 'original_sha256': row['original_sha256'],
                             'variant_sha256': row['sha256'], 'changes': row['changes']})
    reachable = set()
    def visit(name):
        if name in reachable: return
        reachable.add(name)
        for dep in modules[name]['imports']:
            if dep in modules: visit(dep)
    for name in inputs['roots']: visit(name)
    if reachable != set(names):
        raise ValueError('UNREACHABLE_COMPONENT_REFUSED')
    graph = {'targets': {LABEL: {'roots': inputs['roots'], 'order': names,
        'modules': modules, 'required_for_accepted_release': False}},
        'original_source_commit': inputs['dot_commit'],
        'scope': 'Separate source-only P1/P5 component context; no master or native acceptance.'}
    selection = {'source_only': True, 'sources': selected, 'import_variants': variants,
        'mathlib_commit': inputs['mathlib_commit'], 'native_record_writer_required': True,
        'full_import_elaboration_run': False, 'native_compiler_invoked': False,
        'selected_endpoint_names': inputs['selected_endpoints'],
        'originals_preserved': True, 'physical778_target_unchanged': True,
        'scope': 'Historical hosted components; modular pinned imports remain unverified.'}
    return document(graph), document(selection), bodies


def prepare(destination):
    destination = Path(destination).resolve()
    if destination.exists() or any((p/'.git').exists() for p in [destination, *destination.parents]):
        raise ValueError('NEW_NON_GIT_SOURCE_DESTINATION_REQUIRED')
    graph, selection, bodies = source_plan()
    destination.mkdir(parents=True)
    (destination/'scripts').mkdir()
    (destination/'source-store').mkdir()
    for digest, raw in bodies.items():
        (destination/'source-store'/(digest+'.lean')).write_bytes(raw)
    (destination/'DEPENDENCY-GRAPH.json').write_bytes(graph)
    (destination/'SOURCE-SELECTION.json').write_bytes(selection)
    shutil.copyfile(HERE/'pinned/AuditTemplate.lean', destination/'scripts/AuditTemplate.lean')
    shutil.copyfile(HERE/'materials/SelectedEndpointAudit.lean', destination/'SelectedEndpointAudit.lean')
    (destination/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    install_outer_refusal(destination)
    (destination/'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage materialsComponentsProvisional\n\n'
        'target verify _pkg : Unit := do\n  Job.async do\n'
        '    error "SOURCE_ONLY: original-owner native first writers remain UNBOUND"\n')
    from install_retained_loader import install_loader
    manifest = install_loader(destination)
    for digest, raw in bodies.items():
        if (destination/'source-store'/(digest+'.lean')).read_bytes() != raw:
            raise ValueError('SOURCE_READBACK_MISMATCH')
    return {'components': len(bodies), 'source_bytes': sum(map(len, bodies.values())),
            'graph_sha256': hashlib.sha256(graph).hexdigest(),
            'selection_sha256': hashlib.sha256(selection).hexdigest(),
            'retained_loader_sources': len(manifest['scripts']),
            'compiler_invoked': False, 'native_controller': 'UNBOUND'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    print(json.dumps(prepare(args.destination)))
