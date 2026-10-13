"""Thin exact-byte facade over the recovered, pinned RC1 native executable.

No solver, law compiler, parser for source graphs, or native certificate checker
is reimplemented here. AFFINE decisions concern one supplied matrix; LAW is a
formal joint forward table with native replay. Neither certifies source admission.
"""
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import tempfile
import time

from certificates import Refused, fields, require

HERE = Path(__file__).resolve().parent
BINARY_SHA = '235520d47eaa95873729f2aa60b6f596f41859f1b1807ee58aeb1bd2ab0f876a'
MANIFEST_SHA = 'c5c84b5fa1755ae05830059353c184a77c52bd236b4053fe2668e6e30f066da6'
BUILD_RECEIPTS = {
    'evidence/recovered-parity-core-build/RECEIPT.json':
        '9ac32bba0d4a4af529e17837d200d863953aee496badd714bdc30e22723c4562',
    'evidence/recovered-parity-population/RECEIPT.json':
        '5a9d3858a0d64cbec35c1158a7fefec21ba1ddf08e377f711f49aab6515ba06a',
}
MAX_REQUEST = 65536
MAX_CERTIFICATE = 4*1024**2


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def regular(path, maximum):
    path = Path(path)
    require(not path.is_symlink() and path.is_file(), 'regular nonsymlink runtime file required')
    with path.open('rb') as handle:
        raw = handle.read(maximum+1)
    require(len(raw) <= maximum, 'runtime file exceeds bounded read')
    return raw


def authenticate(binary, restored):
    binary_raw = regular(binary, 128*1024**2)
    require(sha(binary_raw) == BINARY_SHA, 'native binary differs from the selected executed build')
    manifest_raw = regular(Path(restored)/'RESTORED-SOURCES.json', 256*1024)
    require(sha(manifest_raw) == MANIFEST_SHA, 'recovered source manifest differs from selected inventory')
    manifest = json.loads(manifest_raw)
    for row in manifest['files']:
        raw = regular(Path(restored)/row['path'], 1024**2)
        require(len(raw) == row['bytes'] and sha(raw) == row['sha256'],
                'recovered selected source changed: '+row['path'])
    for path, expected in BUILD_RECEIPTS.items():
        raw = regular(HERE/path, 256*1024)
        require(sha(raw) == expected, 'selected build receipt changed')
        receipt = json.loads(raw)
        require(receipt['exit_code'] == 0 and receipt['stop'] is None,
                'selected native build did not complete')
    return binary_raw, dict(binary_sha256=BINARY_SHA, restored_manifest_sha256=MANIFEST_SHA,
                            selected_source_files=len(manifest['files']),
                            historical_decoder_pins=manifest['historical_inrepo_rust_pins_matched'],
                            build_receipts=BUILD_RECEIPTS,
                            source_to_binary_relationship='observed controlled build; compiler trusted')


def ascii_bytes(value, maximum, label):
    require(type(value) is str, label+' must be literal ASCII text')
    require(0 < len(value) <= maximum, label+' byte limit')
    try:
        raw = value.encode('ascii')
    except UnicodeError as error:
        raise Refused(label+' must be literal ASCII text') from error
    require(0 < len(raw) <= maximum, label+' byte limit')
    return raw


def child_limits():
    # Keep the native child in the enclosing guard's process group. The frozen
    # executable does not launch other processes. No compiler runs here.
    for key, cap in [(resource.RLIMIT_AS, 128*1024**2), (resource.RLIMIT_CPU, 8),
                     (resource.RLIMIT_FSIZE, 8*1024**2), (resource.RLIMIT_CORE, 0)]:
        _, hard = resource.getrlimit(key)
        bound = cap if hard == resource.RLIM_INFINITY else min(cap, hard)
        resource.setrlimit(key, (bound, bound))


def run_child(command, out, name, data=None):
    started = time.monotonic()
    receipt = dict(command=list(map(str, command)), timed_out=False, exit_code=None,
                   memory_bytes=128*1024**2, cpu_seconds=8, wall_seconds=10,
                   output_file_bytes=8*1024**2)
    with (out/(name+'.stdout')).open('xb') as stdout, (out/(name+'.stderr')).open('xb') as stderr:
        try:
            result = subprocess.run(command, input=data, stdout=stdout, stderr=stderr,
                                    timeout=10, preexec_fn=child_limits,
                                    env={'PATH': os.defpath, 'LANG': 'C.UTF-8'}, cwd=out)
            receipt['exit_code'] = result.returncode
        except subprocess.TimeoutExpired:
            receipt['timed_out'] = True
        except OSError as error:
            receipt['error'] = str(error)
    receipt['elapsed_seconds'] = time.monotonic()-started
    for kind in ['stdout', 'stderr']:
        raw = (out/(name+'.'+kind)).read_bytes()
        receipt[kind] = dict(bytes=len(raw), sha256=sha(raw))
    (out/(name+'.execution.json')).write_text(json.dumps(receipt, indent=2)+'\n')
    return receipt


def response_status(kind, request, response):
    prefix = ('RC1 RESULT '+kind+'\nBEGIN_REQUEST\n').encode()+request+b'END_REQUEST\n'
    require(response.startswith(prefix), 'native result does not preserve exact request identity')
    rest = response[len(prefix):]
    if kind == 'LAW':
        require(b'\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n' in rest,
                'native forward result omitted source-admission boundary')
    statuses = [line.removeprefix(b'STATUS ') for line in rest.splitlines() if line.startswith(b'STATUS ')]
    require(len(statuses) == 1, 'native result has ambiguous status')
    allowed = {b'SAT', b'UNSAT', b'UNKNOWN'} if kind == 'AFFINE' else {b'TABLE', b'UNKNOWN'}
    require(statuses[0] in allowed, 'unsupported native result status')
    return statuses[0].decode()


def consume(request, output, binary=None, restored_sources=None):
    """Produce/check one exact RC1 AFFINE or LAW operation in a fresh directory.

Request: schema=native_rc1_operation_v1, operation=solve|check, request=<RC1>;
check additionally requires certificate=<RC1 result>. Paths and caller proof
flags are not accepted inside the mathematical request. The caller selects the
runtime paths through separate process configuration; fixed pins still apply.
"""
    out = Path(output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    result = dict(schema='native_rc1_operation_result_v1', status='REFUSED_REQUEST',
                  source_feasibility_certified=False, unknown_size_exclusion_certified=False,
                  physical_source_admission_verified=False, native_refinement_proved=False,
                  full_joint_calendar_law_verified=False, general_G3_resolved=False)
    try:
        require(type(request) is dict, 'native operation must be an object')
        operation = request.get('operation')
        require(operation in ('solve', 'check'), 'native operation must be solve or check')
        fields(request, ['schema', 'operation', 'request'] + (['certificate'] if operation == 'check' else []))
        require(request['schema'] == 'native_rc1_operation_v1', 'unsupported native bridge schema')
        raw = ascii_bytes(request['request'], MAX_REQUEST, 'RC1 request')
        header = raw.split(b'\n', 1)[0].split(b' ')
        require(len(header) >= 2 and header[0] == b'RC1' and header[1] in (b'AFFINE', b'LAW'),
                'this bridge selects existing RC1 AFFINE or LAW only')
        kind = header[1].decode()
        result.update(operation=operation, native_kind=kind, request_sha256=sha(raw),
                      native_checker_algorithm_independent=kind == 'AFFINE',
                      checker_mode='original-row exact arithmetic' if kind == 'AFFINE'
                      else 'replay of the same bounded full joint forward compiler')
        (out/'REQUEST.rc1').write_bytes(raw)
        if binary is None or restored_sources is None:
            result.update(status='UNKNOWN', reason='pinned native runtime and recovered sources must be configured')
        else:
            binary_raw, identity = authenticate(binary, restored_sources)
            result['runtime'] = identity
            # Execute one captured, pinned byte buffer so later mutation of the
            # caller's binary path cannot affect this invocation. Only our own
            # temporary executable is cleaned up; all requests/results remain.
            with tempfile.TemporaryDirectory(prefix='astra-pinned-native-') as temporary:
                captured = Path(temporary)/'parity-solver'
                captured.write_bytes(binary_raw)
                captured.chmod(0o700)
                certificate_path = out/'RESPONSE.rc1'
                if operation == 'solve':
                    execution = run_child([str(captured), 'solve', '-'], out, 'solve', raw)
                    result['solve_execution'] = execution
                    response = (out/'solve.stdout').read_bytes()
                    require(len(response) <= MAX_CERTIFICATE, 'native response exceeds certificate cap')
                    certificate_path.write_bytes(response)
                    if execution['timed_out'] or execution['exit_code'] not in (0, 1, 2):
                        result.update(status='UNKNOWN', reason='native execution/resource limit')
                    elif execution['exit_code'] == 1:
                        result.update(status='REFUSED_REQUEST', reason='native parser/executor refused request')
                    else:
                        status = response_status(kind, raw, response)
                        require(execution['exit_code'] == (2 if status == 'UNKNOWN' else 0),
                                'native status/exit mismatch')
                        if status == 'UNKNOWN':
                            result.update(status='UNKNOWN', reason='native bounded search/forward compilation exhausted',
                                          native_status=status, certificate_checked=False)
                else:
                    response = ascii_bytes(request['certificate'], MAX_CERTIFICATE, 'RC1 certificate')
                    certificate_path.write_bytes(response)
                    status = response_status(kind, raw, response)
                    result['supplied_native_status'] = status
                if result['status'] == 'REFUSED_REQUEST' and (operation == 'check' or
                        result.get('solve_execution', {}).get('exit_code') == 0):
                    execution = run_child([str(captured), 'check', str(out/'REQUEST.rc1'), str(certificate_path)],
                                          out, 'check')
                    result['check_execution'] = execution
                    accepted = (execution['exit_code'] == 0 and not execution['timed_out'] and
                                (out/'check.stdout').read_bytes() == b'RC1 CHECK ACCEPT\n')
                    if accepted and status == 'UNKNOWN':
                        # The selected native checker never accepts UNKNOWN as
                        # a certificate. Preserve uncertainty even if a future
                        # runtime violates that contract; do not map it to YES.
                        result.update(status='UNKNOWN', reason='native checker unexpectedly accepted a non-certificate UNKNOWN result',
                                      mathematical_decision='UNKNOWN', certificate_checked=False)
                    elif accepted:
                        result.update(status={'SAT': 'CERTIFIED_AFFINE_WITNESS',
                                              'UNSAT': 'CERTIFIED_AFFINE_EXCLUSION',
                                              'TABLE': 'CHECKED_SYMBOLIC_FORWARD_TABLE'}[status],
                                      native_status=status, certificate_checked=True)
                    elif execution['timed_out'] or execution['exit_code'] not in (0, 1):
                        result.update(status='UNKNOWN', reason='native certificate check execution/resource limit')
                    else:
                        result.update(status='REFUSED_REQUEST', reason='native request-bound certificate rejected',
                                      certificate_checked=False)
                        if status == 'UNKNOWN':
                            result.update(reason='supplied UNKNOWN result is not a feasibility or exclusion certificate',
                                          mathematical_decision='UNKNOWN')
                result['response_sha256'] = sha(response)
    except (Refused, ValueError, OSError, KeyError, TypeError) as error:
        result.update(status='REFUSED_REQUEST', reason=str(error))
    (out/'RESULT.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    return result
