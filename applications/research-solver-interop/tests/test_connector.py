"""Transport/identity checks plus real guarded calls to the unchanged runtime."""

import io
import json
from pathlib import Path
import sys
import shutil
import tempfile
import unittest

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
from bridge import RuntimeBridge, MAX_REQUEST, load_json
from server import Server, MAX_MESSAGE

REQUEST = json.dumps({'schema': 'unified_research_solver_v1', 'task': 'generate_singleton',
                      'input': ['1', '1/2', '1/8']}, indent=2) + '\n'
INITIALIZE = {'jsonrpc': '2.0', 'id': 1, 'method': 'initialize',
              'params': {'protocolVersion': '2025-06-18', 'capabilities': {},
                         'clientInfo': {'name': 'test-client', 'version': '1'}}}
READY = {'jsonrpc': '2.0', 'method': 'notifications/initialized'}


class TransportTests(unittest.TestCase):
    def run_messages(self, messages):
        with tempfile.TemporaryDirectory() as folder:
            server = Server(RuntimeBridge(Path(folder) / 'calls'))
            incoming = io.BytesIO(b''.join((m if isinstance(m, bytes) else json.dumps(m).encode() + b'\n')
                                          for m in messages))
            outgoing = io.BytesIO()
            server.serve(incoming, outgoing)
            return [load_json(line) for line in outgoing.getvalue().splitlines()]

    def test_initialization_list_and_notifications(self):
        result = self.run_messages([INITIALIZE, READY,
                                   {'jsonrpc': '2.0', 'method': 'notifications/cancelled', 'params': []},
                                   {'jsonrpc': '2.0', 'id': 2, 'method': 'tools/list'}])
        self.assertEqual([row['id'] for row in result], [1, 2])
        self.assertEqual(result[0]['result']['protocolVersion'], '2025-06-18')
        self.assertEqual({t['name'] for t in result[1]['result']['tools']},
                         {'research_solver_run', 'research_solver_capabilities'})

    def test_preinitialize_and_invalid_tool_arguments(self):
        result = self.run_messages([{'jsonrpc': '2.0', 'id': 0, 'method': 'tools/list'},
                                   INITIALIZE, READY,
                                   {'jsonrpc': '2.0', 'id': 2, 'method': 'tools/call',
                                    'params': {'name': 'research_solver_run',
                                               'arguments': {'request_json': REQUEST, 'output': '/tmp/chosen'}}}])
        self.assertEqual(result[0]['error']['code'], -32002)
        self.assertEqual(result[-1]['error']['code'], -32602)

    def test_parse_errors_do_not_desynchronize_stream(self):
        result = self.run_messages([b'{"jsonrpc":"2.0","id":7,"id":8}\n',
                                   b'\xff\n', b'x' * (MAX_MESSAGE + 20) + b'\n',
                                   INITIALIZE, READY,
                                   {'jsonrpc': '2.0', 'id': 'still-alive', 'method': 'ping'}])
        self.assertEqual([r['error']['code'] for r in result[:3]], [-32700] * 3)
        self.assertEqual(result[-1], {'jsonrpc': '2.0', 'id': 'still-alive', 'result': {}})

    def test_surrogate_identifier_is_echoed_as_escaped_json(self):
        result = self.run_messages([{'jsonrpc': '2.0', 'id': '\ud800', 'method': 'ping'}])
        self.assertEqual(result[0]['id'], '\ud800')


class RuntimeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.bridge = RuntimeBridge(self.root / 'calls')

    def test_existing_runtime_success_preserves_literal_request_and_uncompiled_flags(self):
        first = self.bridge.run(REQUEST)
        second = self.bridge.run(REQUEST)
        self.assertEqual(first['status'], 'GENERATED_AND_CHECKED')
        self.assertTrue(first['runtime_result_authenticated'])
        folder = Path(first['artifacts']['directory'])
        self.assertEqual((folder / 'runtime' / 'REQUEST.json').read_bytes(), REQUEST.encode())
        stored = load_json((folder / 'runtime' / 'RESULT.json').read_bytes())
        self.assertEqual(first['runtime_result'], stored)
        self.assertFalse(stored['source_feasibility_certified'])
        self.assertFalse(stored['general_G3_resolved'])
        emitted = stored['delegate']['result']['Lean_certificate_sources']
        self.assertTrue(emitted)
        self.assertTrue(all(row['compiled'] is False for row in emitted))
        self.assertNotEqual(first['artifacts']['directory'], second['artifacts']['directory'])
        self.assertEqual((folder / 'runtime' / 'REQUEST.json').read_bytes(), REQUEST.encode())

    def test_unknown_and_refusal_retain_delegate_distinction(self):
        unknown = self.bridge.run('{"schema":"unsupported"}')
        refused = self.bridge.run('{"schema":1,"schema":2}')
        self.assertEqual(unknown['status'], 'UNKNOWN')
        self.assertTrue(unknown['runtime_result_authenticated'])
        self.assertEqual(unknown['execution']['runtime_exit_code'], 2)
        self.assertEqual(refused['status'], 'REFUSED_REQUEST')
        self.assertTrue(refused['runtime_result_authenticated'])
        self.assertEqual(refused['execution']['runtime_exit_code'], 1)

    def test_missing_approved_native_binary_is_unknown(self):
        bridge = RuntimeBridge(self.root / 'native-calls', rust_binary=self.root / 'absent',
                               native_generation=True)
        result = bridge.run(REQUEST)
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertTrue(result['runtime_result_authenticated'])
        self.assertFalse(result['runtime_result']['source_feasibility_certified'])

    def test_transport_bounds_precede_output_creation(self):
        oversized = self.bridge.run('x' * (MAX_REQUEST + 1))
        invalid_utf8 = self.bridge.run('\ud800')
        for result in [oversized, invalid_utf8]:
            self.assertEqual(result['status'], 'REFUSED_BRIDGE_REQUEST')
            self.assertFalse(result['execution']['guard_started'])
        self.assertFalse((self.root / 'calls').exists())

    def test_changed_or_missing_provider_cannot_execute(self):
        bridge = RuntimeBridge(self.root / 'blocked', repository=self.root / 'absent-repo')
        result = bridge.run(REQUEST)
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertFalse(result['execution']['guard_started'])
        self.assertFalse((self.root / 'blocked').exists())

    def test_virtualenv_and_native_paths_are_not_rewritten(self):
        link = self.root / 'venv-python'
        link.symlink_to(sys.executable)
        bridge = RuntimeBridge(self.root / 'unused', python=link, backend_python=link)
        self.assertEqual(bridge.python, str(link))
        self.assertIn(str(link), bridge.options)

    def test_path_interpreter_names_are_resolved_for_operator_configuration(self):
        bridge = RuntimeBridge(self.root / 'unused', python='python3', backend_python='python3')
        expected = str(Path(shutil.which('python3')).absolute())
        self.assertEqual(bridge.python, expected)
        self.assertIn(expected, bridge.options)


if __name__ == '__main__':
    unittest.main()
