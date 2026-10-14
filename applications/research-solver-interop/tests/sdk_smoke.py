#!/usr/bin/env python3
"""Preserve official MCP SDK interoperability with the real pinned runtime."""

import argparse
import asyncio
import hashlib
import importlib.metadata
import json
from pathlib import Path
import sys

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent.parent


async def run(output):
    output.mkdir(parents=True, exist_ok=False)
    parameters = StdioServerParameters(command=sys.executable,
        args=['-B', str(HERE / 'server.py'), '--output-root', str(output / 'calls')])
    cases = [
        ('existing-generation', (REPO / 'research/2026-10-13-astra-unified-solver-0645z/examples/singleton-generator.json').read_text(),
         'GENERATED_AND_CHECKED', False),
        ('unsupported-schema', '{"schema":"unsupported"}', 'UNKNOWN', False),
        ('missing-native', json.dumps({'schema': 'unified_research_solver_v1', 'task': 'native_rc1',
            'input': {'schema': 'native_rc1_operation_v1', 'operation': 'solve',
                      'request': 'RC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLT 1/1 1/1\n'}}), 'UNKNOWN', False),
        ('duplicate-request-fields', '{"schema":1,"schema":2}', 'REFUSED_REQUEST', True),
    ]
    records = []
    async with stdio_client(parameters) as (read, write):
        async with ClientSession(read, write) as client:
            initialized = await client.initialize()
            assert initialized.protocolVersion == '2025-06-18'
            tools = await client.list_tools()
            assert {tool.name for tool in tools.tools} == {'research_solver_run', 'research_solver_capabilities'}
            capabilities = await client.call_tool('research_solver_capabilities', {})
            assert not capabilities.isError and capabilities.structuredContent['provider_sources_available']
            for name, request, expected_status, expected_error in cases:
                response = await client.call_tool('research_solver_run', {'request_json': request})
                value = response.structuredContent
                assert value == json.loads(response.content[0].text)
                assert value['status'] == expected_status and response.isError == expected_error
                assert value['runtime_result_authenticated']
                assert value['runtime_result']['source_feasibility_certified'] is False
                call = Path(value['artifacts']['directory'])
                assert (call / 'runtime' / 'REQUEST.json').read_bytes() == request.encode()
                if name == 'existing-generation':
                    emitted = value['runtime_result']['delegate']['result']['Lean_certificate_sources']
                    assert all(source['compiled'] is False for source in emitted)
                    assert 'native_generation' not in value['runtime_result']['delegate']['result']
                records.append({'name': name, 'status': value['status'], 'isError': response.isError,
                                'request_sha256': hashlib.sha256(request.encode()).hexdigest(),
                                'runtime_result_sha256': value['artifacts']['runtime_result_sha256'],
                                'call_directory': call.relative_to(output).as_posix()})
            invalid = await client.call_tool('research_solver_run', {'request_json': 'x' * 262145})
            assert invalid.isError and invalid.structuredContent['status'] == 'REFUSED_BRIDGE_REQUEST'
            assert invalid.structuredContent['execution']['guard_started'] is False
            records.append({'name': 'oversized-request', 'status': 'REFUSED_BRIDGE_REQUEST', 'isError': True,
                            'guard_started': False})
    evidence = {'schema': 'research_mcp_official_client_smoke_v1', 'status': 'PASS',
                'official_mcp_sdk': importlib.metadata.version('mcp'),
                'protocol': initialized.protocolVersion, 'cases': records,
                'fresh_existing_runtime_calls': 4, 'native_success_executed': False,
                'lean_compilation_executed': False,
                'limits': 'Finite transport/delegation execution, not universal client compatibility or native refinement.'}
    (output / 'SDK-RESULT.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'cases': len(records), 'evidence': str(output / 'SDK-RESULT.json')}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    asyncio.run(run(parser.parse_args().output.absolute()))
