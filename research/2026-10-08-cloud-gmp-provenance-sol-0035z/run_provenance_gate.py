#!/usr/bin/env python3
"""One frozen-source build and one unchanged harness batch, with launch hash gates."""
import argparse
import ast
import ctypes
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import sys
import time
import traceback
import types

PINNED = {
    'include/certified_forward_gmp.hpp': ('1aea02e7310612e65a630d0f5d94d4f101971422b031dbb9825fc42ef95ea1db', 2235),
    'src/certified_forward_gmp.cpp': ('e13585e3c09cc39c20fcf282fa04ab4481ce8b23d017cb88fa842779d7594dc1', 5524),
    'src/interval_probe.cpp': ('ea13ab20c3268b68ae0c10d2ad9ab0d989fb71eadc4cfef38c7acd2880065b69', 6679),
    'Makefile': ('039a3398b51db2a829fcbc00a4022d31beb50a0186df8ba5c9563ccdd8ef5986', 427),
    'tests/differential.py': ('e5ee87aef378a298ece98b761e42025d5c5d31f993469375511ff163ff5a563f', 11399),
    'reference/certified_forward.py': ('c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace', 6604),
    'reference/test_forward.py': ('5d57db79b1df9bf1a29f07f05d15dd35b6ac0f5f2584c7aac63e4088c3c15ba3', 2929),
}
INPUT_SHA = '465ec1ed6d6a4225923fb399007770aab0473a3aaa029d76fd583a10f53d01d3'
OUTPUT_SHA = '6046f023aa7e18d8c451a36fb7d66f11fda4b709dd57c92c51d19d652d9b3697'
BUILD_LIMITS = {'cpu_seconds': 60, 'wall_seconds': 90, 'address_space_bytes': 1024**3, 'file_bytes': 64*1024**2}
HARNESS_LIMITS = {'cpu_seconds': 90, 'wall_seconds': 120, 'address_space_bytes': 512*1024**2, 'file_bytes': 16*1024**2}
PROBE_LIMITS = {'cpu_seconds': 45, 'wall_seconds': 60, 'address_space_bytes': 256*1024**2, 'file_bytes': 16*1024**2}
VERSION_LIMITS = {'cpu_seconds': 5, 'wall_seconds': 10, 'address_space_bytes': 256*1024**2, 'file_bytes': 16*1024**2}
WRAPPER_LIMITS = {'cpu_seconds': 180, 'wall_seconds': 240, 'address_space_bytes': 1024**3, 'file_bytes': 64*1024**2}


def identity(buffer):
    return {'sha256': hashlib.sha256(buffer).hexdigest(), 'bytes': len(buffer)}


def file_identity(path):
    return identity(Path(path).read_bytes())


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2)+'\n')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def snapshot(root):
    result = {rel: file_identity(root/rel) for rel in PINNED}
    for rel, (sha, size) in PINNED.items():
        require(result[rel] == {'sha256': sha, 'bytes': size}, 'source pin mismatch: '+str(root/rel))
    return result


def limits_fn(limits):
    def apply():
        resource.setrlimit(resource.RLIMIT_CPU, (limits['cpu_seconds'], limits['cpu_seconds']))
        resource.setrlimit(resource.RLIMIT_AS, (limits['address_space_bytes'], limits['address_space_bytes']))
        resource.setrlimit(resource.RLIMIT_FSIZE, (limits['file_bytes'], limits['file_bytes']))
    return apply


def command(args, name, output, limits, input_buffer=None, cwd=None):
    started = time.monotonic()
    record = {'argv': args, 'cwd': str(cwd) if cwd else None, 'limits': limits,
              'stdin': identity(input_buffer) if input_buffer is not None else None}
    try:
        completed = subprocess.run(args, input=input_buffer, capture_output=True, cwd=cwd,
                                   preexec_fn=limits_fn(limits), timeout=limits['wall_seconds'])
        stdout, stderr = completed.stdout, completed.stderr
        record['returncode'] = completed.returncode
    except subprocess.TimeoutExpired as error:
        stdout, stderr = error.stdout or b'', error.stderr or b''
        record.update(returncode=None, failure='TimeoutExpired')
    record['elapsed_seconds'] = round(time.monotonic()-started, 6)
    for stream, data in [('stdout', stdout), ('stderr', stderr)]:
        filename = name+'.'+stream
        (output/filename).write_bytes(data)
        record[stream] = {'path': filename, **identity(data)}
    dump(output/(name+'.json'), record)
    require(record['returncode'] == 0, 'command failed: '+name)
    return record


def harness_child(args):
    """Authenticate the received buffer; guard the actual single native subprocess."""
    buffer = sys.stdin.buffer.read()
    sha, size = PINNED['tests/differential.py']
    require(identity(buffer) == {'sha256': sha, 'bytes': size}, 'harness buffer pin mismatch')
    stage, output, binary = Path(args.stage), Path(args.output), Path(args.binary)
    expected_binary = {'sha256': args.binary_sha, 'bytes': args.binary_bytes}
    original_run = subprocess.run
    calls = 0

    def gated_run(argv, **kwargs):
        nonlocal calls
        calls += 1
        require(calls == 1 and argv == [str(binary)], 'unexpected native subprocess')
        record = {'argv': argv, 'call_count': calls, 'limits': PROBE_LIMITS,
                  'stdin': identity(kwargs['input']), 'harness_buffer': identity(buffer)}
        record['source_before'] = snapshot(stage)
        record['binary_before'] = file_identity(binary)
        require(record['binary_before'] == expected_binary, 'binary pin mismatch at native launch')
        try:
            result = original_run(argv, **kwargs)
            record['returncode'] = result.returncode
            for stream in ('stdout', 'stderr'):
                data = getattr(result, stream)
                name = 'native-probe.'+stream
                (output/name).write_bytes(data)
                record[stream] = {'path': name, **identity(data)}
            return result
        except BaseException as error:
            record.update(failure=type(error).__name__, message=str(error))
            if isinstance(error, subprocess.TimeoutExpired):
                for stream in ('stdout', 'stderr'):
                    data = getattr(error, stream) or b''
                    name = 'native-probe.'+stream
                    (output/name).write_bytes(data)
                    record[stream] = {'path': name, **identity(data)}
            raise
        finally:
            record['binary_after'] = file_identity(binary)
            record['source_after'] = snapshot(stage)
            dump(output/'native-probe-boundary.json', record)
            require(record['binary_after'] == expected_binary, 'binary changed across native subprocess')
            require(record['source_before'] == record['source_after'], 'stage source changed across native subprocess')

    subprocess.run = gated_run
    sys.argv = [str(stage/'tests/differential.py'), '--probe', str(binary), '--output', str(output/'batch')]
    namespace = {'__name__': '__main__', '__file__': str(stage/'tests/differential.py'),
                 '__package__': None, '__cached__': None}
    exit_code = 0
    try:
        exec(compile(buffer, 'sha256:'+sha, 'exec'), namespace)
    except SystemExit as error:
        exit_code = error.code if isinstance(error.code, int) else int(error.code is not None)
    finally:
        subprocess.run = original_run
        dump(output/'harness-buffer-execution.json', {
            'harness_buffer': identity(buffer), 'execution': 'compile/exec of the received authenticated buffer',
            '__file__': namespace['__file__'], 'argv': sys.argv, 'native_call_count': calls,
            'returncode': exit_code})
    require(calls == 1, 'expected exactly one native probe batch')
    return exit_code


def positive_taylor_check(stage, batch):
    """Check only existing batch records; never add native calls or fixtures."""
    targets = [F(1, 64), F(1), F(37, 8), F(55, 2)]
    lines = (batch/'differential-inputs.txt').read_text().splitlines()
    records = [json.loads(line) for line in (batch/'probe-output.jsonl').read_text().splitlines()]
    found = {}
    for index, (line, record) in enumerate(zip(lines, records)):
        tokens = line.split()
        if len(tokens) == 3 and tokens[0] == 'exp' and tokens[2] == 'i:64' and tokens[1][:2] in ('i:', 'q:'):
            x = F(tokens[1][2:])
            if x in targets:
                found.setdefault(x, {'index': index, 'command': line, 'record': record})
    result = {'oracle_sha256': PINNED['reference/test_forward.py'][0], 'n': 160,
              'requested': list(map(str, targets)), 'found': [str(x) for x in targets if x in found],
              'missing': [str(x) for x in targets if x not in found], 'native_calls_added': 0}
    if len(found) != len(targets):
        result.update(status='PENDING', oracle_executed=False,
                      reason='All four requested cases must already be in the unchanged corpus; no fixture additions')
        return result
    buffer = (stage/'reference/test_forward.py').read_bytes()
    tree = ast.parse(buffer, filename='sha256:'+PINNED['reference/test_forward.py'][0])
    function = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'positive_taylor_oracle']
    require(len(function) == 1, 'positive Taylor function identity')
    namespace = {'F': F, 'f': types.SimpleNamespace(Interval=lambda lo, hi: (lo, hi))}
    exec(compile(ast.Module(body=function, type_ignores=[]), 'positive_taylor_oracle', 'exec'), namespace)
    result['checks'] = []
    for x in targets:
        lo, hi = namespace['positive_taylor_oracle'](x)
        got = found[x]['record']
        require(got['status'] == 'ok' and F(got['lower']) <= lo <= hi <= F(got['upper']), 'Taylor bracket containment')
        result['checks'].append({'x': str(x), 'index': found[x]['index'], 'oracle_lower': str(lo), 'oracle_upper': str(hi)})
    result.update(status='PASS', oracle_executed=True)
    return result


def main(args):
    limits_fn(WRAPPER_LIMITS)()
    signal.alarm(WRAPPER_LIMITS['wall_seconds'])
    packet = Path(__file__).resolve().parent
    repository = packet.parents[1]
    plan_buffer = (packet/'gate-plan.json').read_bytes()
    plan = json.loads(plan_buffer)
    require(file_identity(Path(__file__)) == plan['wrapper'], 'wrapper does not match published plan pin')
    freeze_buffer = (packet/'source-freeze.json').read_bytes()
    require(identity(freeze_buffer) == plan['source_freeze'], 'source freeze does not match plan pin')
    freeze = json.loads(freeze_buffer)
    require(args.published_freeze_commit != '', 'pre-execution publication required')
    source_before = snapshot(packet/'freeze')
    buffers = {rel: (packet/'freeze'/rel).read_bytes() for rel in PINNED}
    require({rel: identity(data) for rel, data in buffers.items()} == source_before, 'frozen source changed during read')
    original_paths = {entry['original_path']: {'sha256': entry['sha256'], 'bytes': entry['bytes']}
                      for entry in freeze['artifacts']+freeze['original_receipts_to_remain_unchanged']}

    def originals():
        result = {path: file_identity(repository/path) for path in original_paths}
        require(result == original_paths, 'historical source or receipt changed')
        return result

    originals_before = originals()
    attempt = Path(args.attempt).resolve()
    attempt.mkdir()  # Exclusive: no stale binary and no rerun into this attempt.
    stage = attempt/'stage'
    for rel, buffer in buffers.items():
        path = stage/rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(buffer)
        path.chmod(0o444)
    output = packet/'results'
    output.mkdir()  # Exclusive: preserve prior attempts/results unchanged.
    record = {'status': 'RUNNING', 'published_freeze_commit': args.published_freeze_commit,
              'wrapper': file_identity(Path(__file__)), 'source_freeze': identity(freeze_buffer),
              'gate_plan': identity(plan_buffer), 'attempt': str(attempt), 'stage': str(stage),
              'wrapper_limits': WRAPPER_LIMITS,
              'frozen_source_before': source_before, 'stage_source_before': snapshot(stage),
              'historical_source_receipts_before': originals_before, 'commands': [],
              'claims': 'One author build and one finite unchanged fixture batch; hash snapshots, not hostile-host attestation or universal/binary reproducibility proof'}
    dump(output/'provenance.json', record)
    try:
        published_paths = ['run_provenance_gate.py', 'gate-plan.json', 'source-freeze.json'] + ['freeze/'+rel for rel in PINNED]
        for index, rel in enumerate(published_paths):
            argv = ['git', 'show', args.published_freeze_commit+':'+str(packet.relative_to(repository)/rel)]
            result = command(argv, 'published-source-'+str(index), output, VERSION_LIMITS, cwd=repository)
            record['commands'].append(result)
            require((output/result['stdout']['path']).read_bytes() == (packet/rel).read_bytes(), 'published source differs: '+rel)
        record['commands'].append(command(['git', 'merge-base', '--is-ancestor', args.published_freeze_commit, 'origin/main'],
                                          'published-source-ancestry', output, VERSION_LIMITS, cwd=repository))
        record['published_source_matches'] = True
        compiler = shutil.which('g++')
        require(compiler is not None, 'g++ unavailable')
        for argv, name in [([compiler, '--version'], 'compiler-version'),
                           ([compiler, '-dumpfullversion'], 'compiler-numeric-version'),
                           ([sys.executable, '--version'], 'python-version'),
                           (['pkg-config', '--modversion', 'gmp', 'gmpxx'], 'gmp-package-versions')]:
            record['commands'].append(command(argv, name, output, VERSION_LIMITS))
        library = 'libgmp.so.10'
        record['gmp_runtime'] = {'library': library, 'version': ctypes.c_char_p.in_dll(ctypes.CDLL(library), '__gmp_version').value.decode()}
        binary = attempt/'interval_probe'
        argv = [compiler, '-std=c++17', '-O2', '-Wall', '-Wextra', '-Werror', '-pedantic',
                '-I', str(stage/'include'), str(stage/'src/certified_forward_gmp.cpp'),
                str(stage/'src/interval_probe.cpp'), '-lgmpxx', '-lgmp', '-o', str(binary)]
        record['source_immediately_before_build'] = snapshot(stage)
        record['commands'].append(command(argv, 'strict-build', output, BUILD_LIMITS, cwd=stage))
        binary.chmod(0o555)
        record['stage_source_after_build'] = snapshot(stage)
        record['frozen_source_after_build'] = snapshot(packet/'freeze')
        record['binary_after_build'] = file_identity(binary)
        record['commands'].append(command(['ldd', str(binary)], 'binary-linked-libraries', output, VERSION_LIMITS))
        argv = [sys.executable, str(Path(__file__).resolve()), '--harness-child', '--stage', str(stage),
                '--output', str(output), '--binary', str(binary),
                '--binary-sha', record['binary_after_build']['sha256'],
                '--binary-bytes', str(record['binary_after_build']['bytes'])]
        record['commands'].append(command(argv, 'authenticated-harness', output, HARNESS_LIMITS,
                                          input_buffer=buffers['tests/differential.py'], cwd=stage))
        record['binary_after_harness'] = file_identity(binary)
        require(record['binary_after_harness'] == record['binary_after_build'], 'binary changed across batch')
        boundary = json.loads((output/'native-probe-boundary.json').read_bytes())
        execution = json.loads((output/'harness-buffer-execution.json').read_bytes())
        require(boundary['call_count'] == execution['native_call_count'] == 1, 'batch count differs from one')
        report = json.loads((output/'batch/differential.json').read_bytes())
        require(report['status'] == 'PASS' and report['failure_count'] == 0, 'differential batch failed')
        require((report['case_count'], report['primitive_comparison_cases'], report['separate_parser_contract_cases'],
                 report['exact_property_assertions']) == (2414, 2408, 6, 5204), 'frozen corpus/count mismatch')
        require(report['input_sha256'] == INPUT_SHA and report['cpp_output_sha256'] == OUTPUT_SHA, 'frozen input/output differs')
        record['differential'] = report
        record['positive_taylor_truth_gate'] = positive_taylor_check(stage, output/'batch')
        record['status'] = 'PASS'
    except BaseException as error:
        record.update(status='FAIL', error_type=type(error).__name__, error=str(error), traceback=traceback.format_exc())
    finally:
        try:
            record['stage_source_after'] = snapshot(stage)
            record['frozen_source_after'] = snapshot(packet/'freeze')
            record['historical_source_receipts_after'] = originals()
            record['wrapper_after'] = file_identity(Path(__file__))
            require(record['wrapper_after'] == record['wrapper'], 'wrapper changed')
            require((packet/'gate-plan.json').read_bytes() == plan_buffer, 'plan changed')
            require((packet/'source-freeze.json').read_bytes() == freeze_buffer, 'source freeze changed')
            require(record['stage_source_after'] == record['stage_source_before'] and
                    record['frozen_source_after'] == source_before and
                    record['historical_source_receipts_after'] == originals_before, 'source before/after differs')
            record['source_before_after_equal'] = True
        except BaseException as error:
            record.update(status='FAIL', final_pin_error=str(error), source_before_after_equal=False)
        dump(output/'provenance.json', record)
    print(json.dumps({'status': record['status'], 'receipt': str(output/'provenance.json'),
                      'error': record.get('error'), 'source_before_after_equal': record['source_before_after_equal'],
                      'positive_taylor_truth_gate': record.get('positive_taylor_truth_gate')}, indent=2))
    return int(record['status'] != 'PASS')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--harness-child', action='store_true')
    parser.add_argument('--published-freeze-commit', default='')
    parser.add_argument('--attempt')
    parser.add_argument('--stage')
    parser.add_argument('--output')
    parser.add_argument('--binary')
    parser.add_argument('--binary-sha')
    parser.add_argument('--binary-bytes', type=int)
    args = parser.parse_args()
    raise SystemExit(harness_child(args) if args.harness_child else main(args))
