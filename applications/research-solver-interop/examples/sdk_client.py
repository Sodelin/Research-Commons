#!/usr/bin/env python3
"""Official MCP SDK client; dependency only for this example, not the server."""

import argparse
import asyncio
import json
from pathlib import Path
import sys

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


async def run(args):
    server = Path(__file__).resolve().parents[1] / 'server.py'
    parameters = StdioServerParameters(command=sys.executable,
        args=['-B', str(server), '--output-root', str(Path(args.output_root).absolute())])
    async with stdio_client(parameters) as (read, write):
        async with ClientSession(read, write) as client:
            initialized = await client.initialize()
            tools = await client.list_tools()
            capabilities = await client.call_tool('research_solver_capabilities', {})
            response = await client.call_tool('research_solver_run',
                {'request_json': Path(args.request).read_bytes().decode('utf-8')})
            result = response.structuredContent
            if result is None:
                result = json.loads(response.content[0].text)
            print(json.dumps({'protocol': initialized.protocolVersion,
                              'tools': [tool.name for tool in tools.tools],
                              'capabilities': capabilities.structuredContent,
                              'tool_error': response.isError, 'result': result}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request', required=True)
    parser.add_argument('--output-root', required=True)
    asyncio.run(run(parser.parse_args()))
