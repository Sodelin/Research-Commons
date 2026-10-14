#!/usr/bin/env python3
"""MCP 2025-06-18 stdio tools for the existing pinned research runtime."""

import argparse
import json
import signal
import sys

from bridge import RuntimeBridge, load_json

PROTOCOL = '2025-06-18'
MAX_MESSAGE = 2 * 1024 * 1024
TOOLS = [
    {'name': 'research_solver_capabilities',
     'description': 'Inspect supported request contracts and provider-source availability; no solver is executed.',
     'inputSchema': {'type': 'object', 'properties': {}, 'additionalProperties': False},
     'annotations': {'readOnlyHint': True, 'idempotentHint': True, 'openWorldHint': False}},
    {'name': 'research_solver_run',
     'description': 'Run the existing exact research runtime on literal original JSON. Writes fresh local evidence. '
                    'UNKNOWN is uncertainty, not exclusion; certificate success is not physical source admission. '
                    'No new model, native refinement or Lean compilation is supplied.',
     'inputSchema': {'type': 'object', 'properties': {'request_json': {'type': 'string', 'maxLength': 262144}},
                     'required': ['request_json'], 'additionalProperties': False},
     'annotations': {'readOnlyHint': False, 'destructiveHint': False,
                     'idempotentHint': False, 'openWorldHint': False}},
]


class RpcError(ValueError):
    def __init__(self, code, message):
        self.code = code
        super().__init__(message)


class Server:
    def __init__(self, bridge):
        self.bridge = bridge
        self.initializing = False
        self.initialized = False

    def dispatch(self, message):
        if (not isinstance(message, dict) or message.get('jsonrpc') != '2.0'
                or not isinstance(message.get('method'), str)
                or ('id' in message and type(message['id']) not in (str, int))):
            raise RpcError(-32600, 'invalid JSON-RPC request')
        method = message['method']
        params = message.get('params', {})
        if not isinstance(params, dict):
            raise RpcError(-32602, 'params must be an object')
        if 'id' not in message:
            if method == 'notifications/initialized' and self.initializing:
                self.initialized = True
            return None
        if method == 'ping':
            return {}
        if method == 'initialize':
            if self.initializing:
                raise RpcError(-32600, 'session is already initialized')
            if (not isinstance(params.get('protocolVersion'), str)
                    or not isinstance(params.get('capabilities'), dict)
                    or not isinstance(params.get('clientInfo'), dict)
                    or not isinstance(params['clientInfo'].get('name'), str)
                    or not isinstance(params['clientInfo'].get('version'), str)):
                raise RpcError(-32602, 'initialize requires protocolVersion, capabilities and clientInfo')
            self.initializing = True
            return {'protocolVersion': PROTOCOL, 'capabilities': {'tools': {'listChanged': False}},
                    'serverInfo': {'name': 'research-commons-solver', 'version': '0.1.0'},
                    'instructions': 'Scoped results and complete evidence are preserved. '
                                    'UNKNOWN is not NO. Tool execution does not compile Lean.'}
        if not self.initialized:
            raise RpcError(-32002, 'initialize and notifications/initialized are required')
        if method == 'tools/list':
            if params:
                raise RpcError(-32602, 'this fixed tool list has no pagination')
            return {'tools': TOOLS}
        if method != 'tools/call':
            raise RpcError(-32601, 'method not found')
        name = params.get('name')
        arguments = params.get('arguments', {})
        if name not in {tool['name'] for tool in TOOLS}:
            raise RpcError(-32602, 'unknown tool name')
        if not isinstance(arguments, dict):
            raise RpcError(-32602, 'arguments must be an object')
        if name == 'research_solver_capabilities':
            if arguments:
                raise RpcError(-32602, 'capabilities takes no arguments')
            value = self.bridge.capabilities()
            error = False
        else:
            if set(arguments) != {'request_json'} or not isinstance(arguments['request_json'], str):
                raise RpcError(-32602, 'only request_json text is accepted')
            value = self.bridge.run(arguments['request_json'])
            error = value['status'] in ('REFUSED_BRIDGE_REQUEST', 'REFUSED_REQUEST') or not value['runtime_result_authenticated']
        return {'content': [{'type': 'text', 'text': json.dumps(value, ensure_ascii=False, allow_nan=False)}],
                'structuredContent': value, 'isError': error}

    def serve(self, incoming, outgoing):
        while True:
            line = incoming.readline(MAX_MESSAGE + 1)
            if not line:
                return
            oversized = len(line) > MAX_MESSAGE
            if oversized:
                # Drain this one oversized message without retaining an unbounded line.
                while not line.endswith(b'\n'):
                    line = incoming.readline(MAX_MESSAGE + 1)
                    if not line:
                        break
            identifier = None
            notification = False
            try:
                if oversized:
                    raise RpcError(-32700, 'message exceeds 2 MiB')
                message = load_json(line.decode('utf-8'))
                notification = (isinstance(message, dict) and message.get('jsonrpc') == '2.0'
                                and isinstance(message.get('method'), str) and 'id' not in message)
                if isinstance(message, dict) and type(message.get('id')) in (str, int):
                    identifier = message['id']
                value = self.dispatch(message)
                if isinstance(message, dict) and 'id' not in message:
                    continue
                response = {'jsonrpc': '2.0', 'id': identifier, 'result': value}
            except RpcError as error:
                if notification:
                    continue
                response = {'jsonrpc': '2.0', 'id': identifier,
                            'error': {'code': error.code, 'message': str(error)}}
            except (ValueError, UnicodeError, RecursionError) as error:
                response = {'jsonrpc': '2.0', 'id': identifier,
                            'error': {'code': -32700, 'message': str(error)}}
            outgoing.write(json.dumps(response, ensure_ascii=True, allow_nan=False).encode('utf-8') + b'\n')
            outgoing.flush()


def stop(signum, frame):
    raise KeyboardInterrupt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-root', required=True)
    parser.add_argument('--repository')
    parser.add_argument('--python', default=sys.executable)
    parser.add_argument('--rust-binary')
    parser.add_argument('--parity-binary')
    parser.add_argument('--parity-sources')
    parser.add_argument('--backend-python')
    parser.add_argument('--native-generation', action='store_true')
    parser.add_argument('--emit-support', action='store_true')
    parser.add_argument('--wall-seconds', type=int, default=45)
    args = vars(parser.parse_args())
    if args['repository'] is None:
        args.pop('repository')
    try:
        bridge = RuntimeBridge(**args)
    except ValueError as error:
        parser.error(str(error))
    signal.signal(signal.SIGTERM, stop)
    try:
        Server(bridge).serve(sys.stdin.buffer, sys.stdout.buffer)
    except (KeyboardInterrupt, BrokenPipeError):
        return 0
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
