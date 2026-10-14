#!/usr/bin/env python3
"""Unexecuted offline source materializer; never invokes Lean, Lake or Git.

Only a fresh fixed sibling source directory may be written. A successful copy
would authenticate selected source bytes, never compiled objects or theorems.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DESTINATION = Path('/workspace/scratch/astra-physical-fixture-sources-0300')
CATALOG_SHA = 'f2c986168ef41eeab5ea6eb27c2fbadc0a1dcbeee618e23fb5f4d3215a790c56'
LOADED_SHA = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def selected_body(record):
    relative = Path(record['path'])
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('selected input is not repository relative')
    path = ROOT/relative
    if path.resolve() != path or not path.is_file():
        raise ValueError('selected input is absent or symlinked: ' + str(path))
    data = path.read_bytes()
    if digest(data) != record['sha256'] or len(data) != record['bytes']:
        raise ValueError('selected input bytes changed: ' + str(path))
    return data


def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)


def write_json(path, value):
    write_new(path, (json.dumps(value, indent=2, sort_keys=True)+'\n').encode())


def selected_sources():
    data = (HERE/'SOURCE-CATALOG.json').read_bytes()
    if digest(data) != CATALOG_SHA or digest(Path(__file__).read_bytes()) != LOADED_SHA:
        raise ValueError('catalog or loaded materializer source changed')
    catalog = json.loads(data)
    selection = json.loads(selected_body(catalog['base_selection']))
    plan = json.loads(selected_body(catalog['base_owned_plan']))
    selected_body(catalog['intake'])
    if len(selection['sources']) != 1642 or len(plan['modules']) != 1641:
        raise ValueError('frozen original scope differs')
    if plan['source_selection_sha256'] != catalog['base_selection']['sha256']:
        raise ValueError('original source-plan binding differs')
    base = {row['module']: row for row in selection['sources']}
    if len(base) != 1642 or set(base)-{'lakefile'} != {r['module'] for r in plan['modules']}:
        raise ValueError('original module identity differs')
    for row in plan['modules']:
        if (row['source_sha256'] != base[row['module']]['sha256']
                or row['imports'] != base[row['module']]['imports']):
            raise ValueError('original source/import selection differs')
    saved = {row['module']: row for row in catalog['preserved_generated_sources']}
    if set(saved) != {'Accepted1613', 'AstraUnified'}:
        raise ValueError('original generated aggregate inventory differs')
    result = []
    for row in selection['sources']:
        if row['module'] == 'lakefile':
            continue
        expected_path = Path(*row['module'].split('.')).with_suffix('.lean')
        if str(expected_path) != row['destination']:
            raise ValueError('original module destination differs')
        origins = row['origins'] or [saved[row['module']]]
        for source in origins:
            data = selected_body(source)
            if digest(data) != row['sha256']:
                raise ValueError('original source provenance differs')
        result.append(dict(module=row['module'], destination=row['destination'],
            sha256=row['sha256'], bytes=row['bytes'], imports=row['imports'],
            origins=origins, selected_input=origins[0], kind='PRESERVED_BASE_SOURCE'))
    for row in catalog['added_sources']:
        if row['module'] in base:
            raise ValueError('supplement replaces an original module')
        if row['destination'] != row['module']+'.lean':
            raise ValueError('supplemental module route differs')
        selected_body(row)
        result.append(dict(module=row['module'], destination=row['destination'],
            sha256=row['sha256'], bytes=row['bytes'], imports=row['imports'],
            origins=[row], selected_input=row, kind='NEW_UNCOMPILED_SOURCE'))
    if len(result) != 1644 or len({x['module'] for x in result}) != 1644:
        raise ValueError('supplemental source inventory differs')
    original_config = selected_body(catalog['base_configuration'])
    if digest(original_config) != base['lakefile']['sha256']:
        raise ValueError('preserved original Lake configuration differs')
    config = selected_body(catalog['configuration'])
    if config != original_config + selected_body(catalog['configuration_appendix']):
        raise ValueError('new Lake configuration does not preserve the literal original prefix')
    result.append(dict(module='lakefile', destination='lakefile.lean',
        sha256=digest(config), bytes=len(config), imports=['Lake'],
        origins=[catalog['configuration']], selected_input=catalog['configuration'],
        kind='APPEND_ONLY_LAKE_CONFIGURATION'))
    selected_body(catalog['toolchain'])
    return catalog, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if (args.out != DESTINATION or args.out.resolve() != DESTINATION
            or args.out.exists() or args.out.is_symlink()):
        raise ValueError('only the absent fixed fresh sibling destination is admitted')
    catalog, rows = selected_sources()
    # No predecessor helper is imported or run; all selected inputs are public
    # repository source/configuration bodies authenticated above.
    DESTINATION.mkdir(parents=True, exist_ok=False)
    try:
        write_json(DESTINATION/'PREPARATION.json', dict(
            status='SOURCE_COPY_STARTED_NOT_COMPLETED', command=sys.argv,
            materializer_sha256=LOADED_SHA, catalog_sha256=CATALOG_SHA,
            no_compiler_no_lake_no_git_no_network=True))
        for row in rows:
            data = selected_body(row['selected_input'])
            if digest(data) != row['sha256']:
                raise ValueError('selected body changed before source copy')
            write_new(DESTINATION/row['destination'], data)
        write_new(DESTINATION/'lean-toolchain', selected_body(catalog['toolchain']))
        if {str(q.relative_to(DESTINATION)) for q in DESTINATION.rglob('*.lean')} != {
                row['destination'] for row in rows}:
            raise ValueError('unexpected or absent copied Lean source')
        for row in rows:
            if digest((DESTINATION/row['destination']).read_bytes()) != row['sha256']:
                raise ValueError('copied source bytes differ')
        report = dict(schema='astra_physical_fixture_materialized_sources_v1',
            status='EXACT_SOURCE_COPY_ONLY_NOT_COMPILED', source=str(DESTINATION),
            materializer_sha256=LOADED_SHA, catalog_sha256=CATALOG_SHA,
            base_selection_sha256=catalog['base_selection']['sha256'],
            sources=[{k:v for k,v in row.items() if k!='selected_input'} for row in rows],
            toolchain_sha256=catalog['toolchain']['sha256'],
            original_source_versions_and_full_targets_preserved=True,
            new_source_official_query='PENDING', actual_lean_compilation='PENDING',
            actual_lake_execution='PENDING', actual_type_axiom_audit='PENDING',
            old_fullowned0215_runner_compatible=False,
            physical_rows_proved=False, full_outer_admission_proved=False,
            protected_representative_proved=False, native_refinement_proved=False)
        write_json(DESTINATION/'SOURCE-SELECTION.json', report)
        print(json.dumps({k:v for k,v in report.items() if k!='sources'}))
    except BaseException as error:
        write_json(DESTINATION/'FAILURE.json', dict(
            status='INCOMPLETE_SOURCE_COPY_PRESERVE_WITHOUT_CLEANUP',
            exception_type=type(error).__name__, message=str(error),
            materializer_sha256=LOADED_SHA, compilation_claimed=False))
        raise


if __name__ == '__main__':
    main()
