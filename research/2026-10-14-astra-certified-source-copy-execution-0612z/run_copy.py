#!/usr/bin/env python3
"""One exact coordinator-authorized source-copy invocation; no compiler/query."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import resource
import shutil
import subprocess
import time

ROOT = Path('/workspace/Research-Commons')
HERE = Path(__file__).resolve().parent
PACKET = ROOT / 'research/2026-10-14-astra-certified-common-integration-0600z'
DEST = Path('/workspace/scratch/astra-certified-common-sources-0600')
COMMAND = ['timeout', '60s', 'python3', '-B',
           'research/2026-10-14-astra-certified-common-integration-0600z/materialize_certified.py']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    raw = (json.dumps(value, indent=2) + '\n').encode()
    with (HERE / name).open('xb') as stream:
        stream.write(raw)


def main():
    expected = {
        'PACKET-MANIFEST.json': '490ca02c658fa59725720e6303bb48b9dc3f0433ab3940e3dd95e06160e7766e',
        'SOURCE-CATALOG.json': 'b0dee2beb1e76573a00237feeaca73e8df511b5327666619a826ec10c05e50fa',
        'materialize_certified.py': '70005d43fd16b958dd729d83419b309a64b836d1adaa3ccd350b60396b4e80b1',
    }
    for name, pin in expected.items():
        assert sha((PACKET / name).read_bytes()) == pin, name
    manifest = json.loads((PACKET / 'PACKET-MANIFEST.json').read_text())
    for row in manifest['files']:
        body = (PACKET / row['path']).read_bytes()
        assert len(body) == row['bytes'] and sha(body) == row['sha256'], row['path']
    assert not DEST.exists() and not DEST.is_symlink()
    assert not (ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/PAUSE-BUILDS').exists()
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    record = dict(schema='astra.authorized-source-copy-command.v1', cwd=str(ROOT),
                  argv=COMMAND, started_utc=start, runner_sha256=sha(Path(__file__).read_bytes()),
                  selected_inputs=expected, frozen_payloads_checked=len(manifest['files']),
                  command_executables={n: dict(path=shutil.which(n), sha256=sha(Path(shutil.which(n)).read_bytes())) for n in ['timeout', 'python3']},
                  inherited_resource_limits={n: list(resource.getrlimit(getattr(resource, n))) for n in ['RLIMIT_AS', 'RLIMIT_CPU', 'RLIMIT_FSIZE']},
                  selected_inherited_environment={n: os.environ.get(n) for n in ['PATH', 'LANG', 'LC_ALL', 'PYTHONDONTWRITEBYTECODE']},
                  copied_source_process_declared_limits=dict(address_space_bytes=256*1024**2, cpu_seconds=30, disk_floor_bytes=8*1024**3),
                  outer_timeout_seconds=60, outer_guard_invoked=False,
                  destination=str(DEST), compiler_invocations=0, import_queries=0,
                  scope='Source copying and byte authentication only; no compiled objects or declaration elaboration.')
    write('COMMAND.json', record)
    before = time.monotonic()
    with (HERE / 'stdout.log').open('xb') as stdout, (HERE / 'stderr.log').open('xb') as stderr:
        child = subprocess.Popen(COMMAND, cwd=ROOT, stdout=stdout, stderr=stderr)
        write('PROCESS.json', dict(pid=child.pid, command_sha256=sha((HERE / 'COMMAND.json').read_bytes()), launched_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), outcome='UNKNOWN_UNTIL_WAIT'))
        code = child.wait()
    result = dict(schema='astra.authorized-source-copy-result.v1',
                  command_sha256=sha((HERE / 'COMMAND.json').read_bytes()),
                  runner_sha256=sha(Path(__file__).read_bytes()), os_exit_code=code,
                  elapsed_seconds=time.monotonic()-before,
                  ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  logs={n: dict(bytes=(HERE/n).stat().st_size, sha256=sha((HERE/n).read_bytes())) for n in ['stdout.log','stderr.log']},
                  compiler_invocations=0, import_queries=0, compiled_objects_authenticated=0,
                  status='SOURCE_COPY_PROCESS_PASS_PENDING_READBACK' if code == 0 else 'FAILED_OR_INTERRUPTED_PARTIAL_PRESERVED')
    write('PROCESS-RESULT.json', result)
    if code != 0:
        print(json.dumps(result))
        raise SystemExit(code if code > 0 else 1)
    receipt_bytes = (DEST / 'MATERIALIZATION.json').read_bytes()
    with (HERE / 'MATERIALIZATION.json').open('xb') as stream:
        stream.write(receipt_bytes)
    receipt = json.loads(receipt_bytes)
    assert receipt['status'] == 'SOURCE_BYTES_COPIED_NOT_ELABORATED'
    assert receipt['materializer_sha256'] == expected['materialize_certified.py']
    assert receipt['catalog_sha256'] == expected['SOURCE-CATALOG.json']
    assert receipt['library_source_count'] == len(receipt['sources']) == 1644
    for row in receipt['sources']:
        body = (DEST / row['destination']).read_bytes()
        assert len(body) == row['bytes'] and sha(body) == row['sha256'], row['module']
    assert sha((DEST / 'lakefile.lean').read_bytes()) == receipt['configuration_sha256']
    assert not list(DEST.rglob('*.olean')) and not list(DEST.rglob('*.ilean'))
    write('READBACK.json', dict(status='SOURCE_COPY_AND_BYTE_READBACK_PASS',
          materialization_sha256=sha(receipt_bytes), process_result_sha256=sha((HERE/'PROCESS-RESULT.json').read_bytes()),
          library_source_count=1644, compiled_objects_authenticated=0, compiler_invocations=0,
          import_queries=0, actual_lean_types_printed=False, actual_axiom_audit=False,
          current_build_state_changed=False, historical_frozen_packet_changed=False))
    print(json.dumps(dict(status='SOURCE_COPY_AND_BYTE_READBACK_PASS', os_exit_code=code,
          elapsed_seconds=result['elapsed_seconds'], sources=1644,
          materialization_sha256=sha(receipt_bytes), compiler_invocations=0)))


if __name__ == '__main__':
    main()
