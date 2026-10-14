#!/usr/bin/env python3
"""Unexecuted offline proposal: copy exact source to one fresh sibling only.

Never invokes Lean, Lake, Git or a process launcher. Byte authentication and
source copying do not elaborate a declaration or authenticate a compiled object.
"""
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DESTINATION = Path('/workspace/scratch/astra-physical-common-sources-0450')
CATALOG_SHA = '0fce5f7b0b4e0c02387f4e377414de55bf467857e9b20dbb3501d1bd6360d46b'
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (30, 30))


def digest(data):
    return hashlib.sha256(data).hexdigest()


def selected_body(record):
    relative = Path(record['path'])
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('input is not repository relative')
    path = ROOT / relative
    if path.resolve() != path or not path.is_file():
        raise ValueError('input is absent or symlinked: ' + str(path))
    data = path.read_bytes()
    if len(data) != record['bytes'] or digest(data) != record['sha256']:
        raise ValueError('selected source bytes changed: ' + str(path))
    return data


def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)


def no_active_build():
    names = {'lean', 'lake', 'guard.py', 'build_external_serial.py',
             'build_support.py', 'build_support_namespace.py', 'query_imports.py',
             'run_external_batches.py', 'run_external_batches_6g.py',
             'run_provider_batches.py', 'run_provider_namespace_batches.py',
             'one_guard.py', 'one_batch.py', 'one_batch_small.py',
             'one_owned_batch.py', 'diagnose_module.py', 'diagnose_thread_failure.py'}
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit() or int(proc.name) == os.getpid():
            continue
        try:
            state = (proc / 'stat').read_text().rsplit(') ', 1)[1].split()[0]
            argv = (proc / 'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
        except (FileNotFoundError, ProcessLookupError):
            continue
        if state not in ('Z', 'X') and any(Path(x).name in names for x in argv):
            raise RuntimeError('active compiler/query/guard blocks materialization')
    if (ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/PAUSE-BUILDS').exists():
        raise RuntimeError('PAUSE-BUILDS blocks materialization')


def main():
    if len(sys.argv) != 1:
        raise ValueError('no destination or execution override is accepted')
    no_active_build()
    if DESTINATION.exists() or DESTINATION.is_symlink():
        raise FileExistsError('fixed fresh destination already exists')
    if shutil.disk_usage(DESTINATION.parent).free < 8 * 1024**3:
        raise RuntimeError('8GiB disk floor')
    raw = (HERE / 'SOURCE-CATALOG.json').read_bytes()
    if digest(raw) != CATALOG_SHA:
        raise ValueError('catalog bytes changed')
    catalog = json.loads(raw)
    base = json.loads(selected_body(catalog['base_selection']))
    plan = json.loads(selected_body(catalog['base_owned_plan']))
    selected_body(catalog['fixture_catalog'])
    if plan['source_selection_sha256'] != catalog['base_selection']['sha256']:
        raise ValueError('parent plan/source binding differs')
    old = {x['module']: x for x in base['sources'] if x['module'] != 'lakefile'}
    if len(old) != 1641 or set(old) != {x['module'] for x in plan['modules']}:
        raise ValueError('parent module inventory differs')
    for row in plan['modules']:
        original = old[row['module']]
        if row['source_sha256'] != original['sha256'] or row['imports'] != original['imports']:
            raise ValueError('parent source/import selection differs')
    saved = {x['module']: x for x in catalog['preserved_generated_sources']}
    if set(saved) != {'Accepted1613', 'AstraUnified'}:
        raise ValueError('parent generated aggregate inventory differs')
    rows = []
    for row in old.values():
        origins = row['origins'] or [saved[row['module']]]
        for origin in origins:
            if digest(selected_body(origin)) != row['sha256']:
                raise ValueError('parent origin body differs')
        rows.append(dict(module=row['module'], destination=row['destination'],
                         bytes=row['bytes'], sha256=row['sha256'],
                         imports=row['imports'], selected_input=origins[0],
                         kind='PRESERVED_PARENT_SOURCE'))
    for row in catalog['added_sources']:
        if row['module'] in old:
            raise ValueError('proposal replaces a parent module')
        selected_body(row)
        rows.append(dict(row, selected_input={k: row[k] for k in ['path', 'bytes', 'sha256']},
                         kind='UNCOMPILED_PROPOSED_ADDITION'))
    if len(rows) != 1659 or len({x['module'] for x in rows}) != 1659:
        raise ValueError('proposed module inventory differs')
    for row in rows:
        if str(Path(*row['module'].split('.')).with_suffix('.lean')) != row['destination']:
            raise ValueError('module destination differs')
    base_config = selected_body(catalog['base_configuration'])
    config = selected_body(catalog['configuration'])
    old_config = next(x for x in base['sources'] if x['module'] == 'lakefile')
    if digest(base_config) != old_config['sha256']:
        raise ValueError('parent Lake configuration differs')
    if config != base_config + selected_body(catalog['configuration_appendix']):
        raise ValueError('Lake configuration is not a literal append')
    toolchain = selected_body(catalog['toolchain'])
    no_active_build()
    DESTINATION.mkdir()
    try:
        for row in rows:
            body = selected_body(row['selected_input'])
            if digest(body) != row['sha256'] or len(body) != row['bytes']:
                raise ValueError('source changed after preflight')
            write_new(DESTINATION / row['destination'], body)
        write_new(DESTINATION / 'lakefile.lean', config)
        write_new(DESTINATION / 'lean-toolchain', toolchain)
        receipt = dict(status='SOURCE_BYTES_COPIED_NOT_ELABORATED',
                       catalog_sha256=CATALOG_SHA,
                       materializer_sha256=digest(Path(__file__).read_bytes()),
                       library_source_count=len(rows), sources=rows,
                       configuration_sha256=digest(config),
                       compiler_invocations=0, compiled_objects_authenticated=0,
                       type_axiom_audit=False, lake_execution=False,
                       active_build_state_modified=False)
        write_new(DESTINATION / 'MATERIALIZATION.json',
                  (json.dumps(receipt, indent=2) + '\n').encode())
    except Exception as error:
        write_new(DESTINATION / 'FAILED.json',
                  (json.dumps({'status': 'FAILED_PARTIAL_SOURCE_PRESERVED',
                               'error_type': type(error).__name__, 'error': str(error)}) + '\n').encode())
        raise
    print(json.dumps({k: receipt[k] for k in ['status', 'catalog_sha256',
          'library_source_count', 'compiler_invocations', 'compiled_objects_authenticated']}))


if __name__ == '__main__':
    main()
