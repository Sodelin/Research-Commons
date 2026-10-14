"""Bounded delegation to the existing runtime; no new solver or checker."""

import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
DEFAULT_REPOSITORY = HERE.parent.parent
RUNTIME = 'research/2026-10-13-astra-unified-runtime-2350z/runtime.py'
GUARD = 'research/2026-10-13-astra-unified-solver-0645z/guard.py'
MAX_REQUEST = 262144
MAX_RESULT = 8 * 1024 * 1024
PINS = json.loads((HERE / 'SOURCE-PINS.json').read_text())['providers']


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def interpreter_path(value):
    spelling = os.fspath(value)
    if not os.path.dirname(spelling):
        found = shutil.which(spelling)
        if found is None:
            raise ValueError('interpreter is not available on PATH: ' + spelling)
        spelling = found
    return str(Path(spelling).absolute())


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON field: ' + key)
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError('nonfinite JSON value: ' + value)


def load_json(raw):
    return json.loads(raw, object_pairs_hook=no_duplicates, parse_constant=reject_constant)


def bounded_file(path, maximum):
    with path.open('rb') as stream:
        raw = stream.read(maximum + 1)
    if len(raw) > maximum:
        raise ValueError('result artifact exceeds the connector size bound')
    return raw


class RuntimeBridge:
    def __init__(self, output_root, *, repository=DEFAULT_REPOSITORY,
                 python=sys.executable, rust_binary=None, parity_binary=None,
                 parity_sources=None, backend_python=None, native_generation=False,
                 emit_support=False, wall_seconds=45):
        if type(wall_seconds) is not int or not 1 <= wall_seconds <= 300:
            raise ValueError('wall seconds must be an integer from 1 to 300')
        self.repository = Path(repository).resolve()
        self.output_root = Path(output_root).resolve()
        # Preserve a virtualenv executable path; resolving its symlink would
        # silently switch interpreter environments.
        self.python = interpreter_path(python)
        self.wall_seconds = wall_seconds
        self.options = []
        for flag, value in [('--rust-binary', rust_binary), ('--parity-binary', parity_binary),
                            ('--parity-sources', parity_sources), ('--backend-python', backend_python)]:
            if value is not None:
                self.options.extend([flag, interpreter_path(value) if flag == '--backend-python'
                                     else str(Path(value).absolute())])
        if native_generation:
            self.options.append('--native-generation')
        if emit_support:
            self.options.append('--emit-support')

    def provider_pins(self):
        for relative, expected in PINS.items():
            path = self.repository / relative
            if path.is_symlink() or digest(bounded_file(path, 1024 * 1024)) != expected:
                raise ValueError('reviewed provider unavailable or changed: ' + relative)
        return dict(PINS)

    def capabilities(self):
        try:
            self.provider_pins()
            available, reason = True, None
        except (OSError, ValueError) as error:
            available, reason = False, str(error)
        return {'schema': 'research_solver_interop_capabilities_v1',
                'provider_sources_available': available, 'reason': reason,
                'request_schemas': ['unified_research_solver_v1', 'selected_native_common_readout_v1'],
                'unified_tasks': ['check_certificate', 'generate_singleton', 'common_menu',
                                  'native_rc1', 'source_search'],
                'maximum_request_bytes': MAX_REQUEST, 'serial_execution': True,
                'native_runtime_authenticated': False,
                'native_runtime_note': 'Operator settings are authenticated by the reused runtime at each call.',
                'support_emission_compiles_lean': False,
                'new_scientific_scope_claimed': False}

    def run(self, request_json):
        result = {'schema': 'research_solver_interop_result_v1', 'status': 'UNKNOWN',
                  'runtime_result': None, 'runtime_result_authenticated': False,
                  'artifacts': None, 'execution': {'guard_started': False},
                  'new_scientific_scope_claimed': False}
        try:
            if not isinstance(request_json, str):
                raise ValueError('request_json must be literal JSON text')
            raw = request_json.encode('utf-8')
            if len(raw) > MAX_REQUEST:
                raise ValueError('request_json exceeds 256 KiB in UTF8')
        except (ValueError, UnicodeError) as error:
            return {**result, 'status': 'REFUSED_BRIDGE_REQUEST', 'reason': str(error)}
        try:
            if sys.platform != 'linux':
                raise ValueError('the inherited execution guard requires a Linux host')
            self.provider_pins()
            self.output_root.mkdir(parents=True, exist_ok=True)
            folder = Path(tempfile.mkdtemp(prefix='call-', dir=self.output_root))
            incoming = folder / 'INPUT.json'
            incoming.write_bytes(raw)
            result['artifacts'] = {'directory': str(folder), 'request_sha256': digest(raw),
                                   'runtime_result_path': 'runtime/RESULT.json',
                                   'execution_receipt_path': 'guard/RECEIPT.json',
                                   'connector_receipt_path': 'CONNECTOR.json'}
            runtime_command = [self.python, '-I', '-B', str(self.repository / RUNTIME),
                               '--request', str(incoming), '--output', str(folder / 'runtime'),
                               *self.options]
            command = [self.python, '-I', '-B', str(self.repository / GUARD),
                       '--out', str(folder / 'guard'), '--cwd', str(self.repository),
                       '--wall', str(self.wall_seconds), '--cpu', '35',
                       '--memory-mib', '768', '--file-mib', '16', '--', *runtime_command]
            # The client cannot set paths, executables, flags or child environment.
            environment = {'PATH': os.defpath, 'LANG': 'C.UTF-8'}
            child = None
            with (folder / 'launcher.stdout').open('xb') as stdout, \
                    (folder / 'launcher.stderr').open('xb') as stderr:
                try:
                    child = subprocess.Popen(command, stdin=subprocess.DEVNULL,
                                             stdout=stdout, stderr=stderr, env=environment,
                                             start_new_session=True)
                    result['execution']['guard_started'] = True
                    child.wait(timeout=self.wall_seconds + 10)
                finally:
                    if child is not None and child.poll() is None:
                        # KeyboardInterrupt executes the inherited guard's finally,
                        # which kills its separately grouped runtime descendants.
                        os.killpg(child.pid, signal.SIGINT)
                        try:
                            child.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            os.killpg(child.pid, signal.SIGKILL)
                            child.wait()
            receipt_raw = bounded_file(folder / 'guard' / 'RECEIPT.json', 1024 * 1024)
            receipt = load_json(receipt_raw)
            result['execution'].update(guard_exit_code=child.returncode,
                                       runtime_exit_code=receipt['exit_code'], stop=receipt['stop'],
                                       receipt_sha256=digest(receipt_raw))
            if receipt['stop'] is not None or receipt.get('error') is not None:
                raise ValueError('inherited execution guard stopped or failed')
            output_raw = bounded_file(folder / 'runtime' / 'RESULT.json', MAX_RESULT)
            output = load_json(output_raw)
            result['runtime_result'] = output
            result['artifacts']['runtime_result_sha256'] = digest(output_raw)
            self.provider_pins()
            if (not isinstance(output, dict) or output.get('schema') != 'astra_unified_runtime_result_v1'
                    or not isinstance(output.get('status'), str)
                    or output.get('primary_request_sha256') != digest(raw)
                    or output.get('runtime_sha256') != PINS[RUNTIME]):
                raise ValueError('runtime result schema or request/provider identity differs')
            expected_exit = 2 if output['status'] == 'UNKNOWN' else 1 if output['status'] == 'REFUSED_REQUEST' else 0
            if receipt['exit_code'] != expected_exit or child.returncode != (0 if expected_exit == 0 else 1):
                raise ValueError('runtime outcome and execution receipt disagree')
            result.update(status=output['status'], runtime_result_authenticated=True)
        except (OSError, ValueError, subprocess.TimeoutExpired) as error:
            result.update(status='UNKNOWN', reason=str(error), runtime_result_authenticated=False)
        if result['artifacts'] is not None:
            try:
                path = Path(result['artifacts']['directory']) / 'CONNECTOR.json'
                with path.open('x') as stream:
                    json.dump(result, stream, indent=2, sort_keys=True, allow_nan=False)
                    stream.write('\n')
            except OSError as error:
                result.update(status='UNKNOWN', reason='connector receipt persistence failed: ' + str(error),
                              runtime_result_authenticated=False)
        return result
