#!/usr/bin/env python3
"""Unexecuted bounded source copier; no Lean/Lake/query/process invocation."""
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DESTINATION = Path('/workspace/scratch/astra-certified-combined-sources-0730')
CATALOG_SHA = '506515845d13bc4a58c0ac0d27556163188f4623387b47ae1d4d01d282f17635'
HELPER = ROOT/'research/2026-10-14-astra-certified-common-integration-0600z/materialize_certified.py'
HELPER_SHA = '70005d43fd16b958dd729d83419b309a64b836d1adaa3ccd350b60396b4e80b1'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check_resources_and_pause():
    for directory in (HERE, ROOT/'research/2026-10-13-astra-positive-support-adapter-0830z'):
        if (directory/'PAUSE-BUILDS').exists():
            raise RuntimeError('PAUSE-BUILDS blocks source copying')
    if shutil.disk_usage(DESTINATION.parent).free < 8*1024**3:
        raise RuntimeError('8GiB disk floor')
    available = next(int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
    if available < 1024**3:
        raise RuntimeError('1GiB available RAM floor')
    if int(Path('/sys/fs/cgroup/memory.current').read_text()) >= 4*1024**3:
        raise RuntimeError('4GiB physical stop')


def no_other_copy():
    names = {'materialize_certified.py', 'materialize_combined.py', 'query_four.py', 'query_four_v2.py'}
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit() or int(proc.name) == os.getpid():
            continue
        try:
            state = (proc/'stat').read_text().rsplit(') ', 1)[1].split()[0]
            argv = (proc/'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
        except (FileNotFoundError, ProcessLookupError):
            continue
        if state not in ('Z', 'X') and argv and Path(argv[0]).name.startswith('python') and any(Path(x).name in names for x in argv[1:]):
            raise RuntimeError('other source copy/query is active')


def main():
    if len(sys.argv) != 1:
        raise ValueError('no destination or execution overrides')
    for key, bound in ((resource.RLIMIT_AS,256*1024**2), (resource.RLIMIT_CPU,30), (resource.RLIMIT_FSIZE,16*1024**2)):
        resource.setrlimit(key, (bound, bound))
    check_resources_and_pause()
    no_other_copy()
    source = HELPER.read_bytes()
    if digest(source) != HELPER_SHA:
        raise ValueError('pinned parent copier changed')
    helper = types.ModuleType('pinned_source_copy_helpers')
    helper.__file__ = str(HELPER)
    exec(compile(source, str(HELPER), 'exec'), helper.__dict__)
    helper.no_active_build()
    raw = (HERE/'SOURCE-CATALOG.json').read_bytes()
    if digest(raw) != CATALOG_SHA:
        raise ValueError('source catalog changed')
    catalog = json.loads(raw)
    if catalog['destination'] != str(DESTINATION) or DESTINATION.exists() or DESTINATION.is_symlink():
        raise FileExistsError('fixed destination must be fresh')
    if catalog['pinned_parent_copy_helper']['sha256'] != HELPER_SHA:
        raise ValueError('parent helper binding differs')
    parent_catalog = json.loads(helper.selected_body(catalog['parent_catalog']))
    parent = json.loads(helper.selected_body(catalog['parent_source_copy_receipt']))
    if parent['catalog_sha256'] != catalog['parent_catalog']['sha256'] or parent['materializer_sha256'] != HELPER_SHA:
        raise ValueError('actual parent copy/catalog identity differs')
    if parent['library_source_count'] != len(parent['sources']):
        raise ValueError('parent receipt count differs')
    if len(parent['sources']) != catalog['parent_expected_library_count'] or len(parent['sources']) != 1644:
        raise ValueError('parent selection must remain exactly1644')
    for record in catalog['source_inputs']:
        helper.selected_body(record)
    rows = list(parent['sources'])
    selected = {row['module']:row for row in rows}
    if len(selected) != 1644:
        raise ValueError('duplicate parent module')
    for duplicate in catalog['exact_generated_duplicates']:
        old = selected[duplicate['module']]
        if duplicate['sha256'] != old['sha256'] or duplicate['parent_input'] != old['selected_input']:
            raise ValueError('duplicate origin differs')
        if helper.selected_body(duplicate['generated_input']) != helper.selected_body(old['selected_input']):
            raise ValueError('same-name generated body differs from retained parent')
    if len(catalog['exact_generated_duplicates']) != 4 or len(catalog['additional_sources']) != 12:
        raise ValueError('fixed duplicate/addition count differs')
    for row in catalog['additional_sources']:
        if row['module'] in selected or not all(name in selected for name in row['imports']):
            raise ValueError('replacement or unresolved additive import')
        selected[row['module']] = row
        rows.append(row)
    if len(rows) != len(selected) or len(rows) != catalog['library_source_count'] or len(rows) != 1656:
        raise ValueError('complete union inventory differs')
    destinations = set()
    for row in rows:
        target = Path(row['destination'])
        if target.is_absolute() or '..' in target.parts or target != Path(*row['module'].split('.')).with_suffix('.lean') or str(target) in destinations:
            raise ValueError('noncanonical or duplicate source destination')
        destinations.add(str(target))
        body = helper.selected_body(row['selected_input'])
        if digest(body) != row['sha256'] or len(body) != row['bytes']:
            raise ValueError('selected source body differs')
    configuration = catalog['configuration']
    if configuration['parent'] != parent_catalog['configuration'] or configuration['parent']['sha256'] != parent['configuration_sha256']:
        raise ValueError('parent configuration binding differs')
    config = helper.selected_body(configuration['parent']) + b'\n' + helper.selected_body(configuration['wrapper_appendix']) + b'\n' + helper.selected_body(configuration['ten_only_appendix'])
    if digest(config) != configuration['sha256'] or len(config) != configuration['bytes']:
        raise ValueError('literal append bytes differ')
    if catalog['toolchain'] != parent_catalog['toolchain']:
        raise ValueError('toolchain record differs')
    toolchain = helper.selected_body(catalog['toolchain'])
    check_resources_and_pause()
    no_other_copy()
    helper.no_active_build()
    DESTINATION.mkdir()
    try:
        for index, row in enumerate(rows):
            if index % 32 == 0:
                check_resources_and_pause()
            body = helper.selected_body(row['selected_input'])
            if digest(body) != row['sha256'] or len(body) != row['bytes']:
                raise ValueError('source changed after preflight')
            path = DESTINATION/row['destination']
            helper.write_new(path, body)
            if path.read_bytes() != body:
                raise ValueError('copied source readback differs')
        check_resources_and_pause()
        helper.write_new(DESTINATION/'lakefile.lean', config)
        helper.write_new(DESTINATION/'lean-toolchain', toolchain)
        if (DESTINATION/'lakefile.lean').read_bytes() != config or (DESTINATION/'lean-toolchain').read_bytes() != toolchain:
            raise ValueError('configuration/toolchain readback differs')
        receipt = dict(status='SOURCE_BYTES_COPIED_NOT_ELABORATED', catalog_sha256=CATALOG_SHA,
                       materializer_sha256=digest(Path(__file__).read_bytes()), parent_copy_receipt=catalog['parent_source_copy_receipt'],
                       parent_helper_sha256=HELPER_SHA, library_source_count=len(rows), sources=rows,
                       configuration_sha256=digest(config), toolchain_sha256=digest(toolchain),
                       retained_duplicate_inputs=catalog['exact_generated_duplicates'], compiler_invocations=0,
                       compiled_objects_authenticated=0, type_axiom_audit=False, lake_execution=False,
                       active_build_state_modified=False)
        helper.write_new(DESTINATION/'MATERIALIZATION.json', (json.dumps(receipt,indent=2)+'\n').encode())
    except BaseException as error:
        helper.write_new(DESTINATION/'FAILED.json', (json.dumps(dict(status='FAILED_PARTIAL_SOURCE_PRESERVED', error_type=type(error).__name__, error=str(error)))+'\n').encode())
        raise
    print(json.dumps({key:receipt[key] for key in ['status','catalog_sha256','library_source_count','compiler_invocations','compiled_objects_authenticated']}))


if __name__ == '__main__':
    main()
