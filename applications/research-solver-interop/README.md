# Research solver connector for MCP clients

Call the existing research solver from a local MCP client. This additive
connector reuses Astra's [pinned unified runtime](../../research/2026-10-13-astra-unified-runtime-2350z/README.md),
including its exact certificate, source-search and Rust interfaces. It
preserves the original JSON request bytes, complete results, UNKNOWN
outcomes and fresh execution evidence. It introduces no solver or model.

The [communication routing guide](COMMUNICATIONS.md) records how chats,
Commons, local Git and authorized private file exchange coordinate, with
separate publication, delivery, acknowledgement and execution evidence.
The MCP tools themselves are runtime calls, not a chat messenger.

The server uses only Python's standard library. Its inherited execution
guard requires Linux with `/proc` and cgroup-v2 memory reporting. The MCP
transport is stdio, protocol 2025-06-18. HTTP-only clients need a separate
transport; this package does not start a network service or install itself
in an application.

## Connect a local MCP host

Use absolute paths appropriate to your checkout and interpreter:

```json
{
  "mcpServers": {
    "research-commons": {
      "command": "/absolute/path/to/python3",
      "args": [
        "-B",
        "/absolute/path/to/Research-Commons/applications/research-solver-interop/server.py",
        "--output-root",
        "/absolute/path/to/research-results"
      ]
    }
  }
}
```

This is a configuration example; different hosts have their own setup
format. A chat does not acquire these tools merely by reading this file.

The server exposes two tools:

- `research_solver_capabilities`: supported request schemas/tasks and
  whether the reviewed provider source files are available. It does not
  authenticate or execute a native binary.
- `research_solver_run`: accepts `request_json`, the literal text of an
  original runtime request. It returns structured content and the same
  JSON as text for clients that use text results.

For example, pass this tool argument to generate the existing checked
singleton certificate from supplied exact moments:

```json
{
  "request_json": "{\"schema\":\"unified_research_solver_v1\",\"task\":\"generate_singleton\",\"input\":[\"1\",\"1/2\",\"1/8\"]}"
}
```

The request schemas are `unified_research_solver_v1` and
`selected_native_common_readout_v1`. Unified tasks remain exactly
`check_certificate`, `generate_singleton`, `common_menu`, `native_rc1`
and `source_search`, under their inherited contracts. Duplicate fields,
nonfinite/floating input and unsupported scientific inputs retain the
runtime's validation and uncertainty behavior. The connector adds no
admission flag, taxon relabelling or parameter fit.

## Select the existing Rust and source backends

Operator-only server options are `--rust-binary`, `--native-generation`,
`--parity-binary`, `--parity-sources`, `--backend-python` and
`--emit-support`, corresponding to the existing runtime. The runtime
authenticates its approved native executable profiles and source receipts;
an arbitrary executable is not a replacement. Missing approved binaries
remain UNKNOWN. Source search keeps its declared finite registry and
coverage limits.

Runtime flags are forwarded unchanged. Use compatible configurations:
selected-copy readouts do not accept certificate-checker/generation flags.
Separate MCP server entries can select the certificate and selected-readout
configurations. See the runtime README for exact native/backend contracts.
Interpreter names such as `python3` are resolved using the operator's PATH
before the child environment is reduced. Explicit virtualenv interpreter
paths retain their symlink spelling and environment.

`--emit-support` emits the existing conditional sources with
`compiled=false`; it never starts Lean. This connector does not attach
compiled physical-row proofs or provide a Lean-to-Rust refinement.

## Read the result and evidence

`structuredContent.runtime_result` is the COMPLETE unchanged runtime
object, including its complete delegate result. The envelope's
`runtime_result_authenticated` checks the selected runtime/guard bytes,
literal request hash, runtime result hash and semantic process exits.
Read the full scope; success is not universal scientific input acceptance.

| Outcome | MCP `isError` | Meaning |
|---|---|---|
| Authenticated runtime result | false | The existing scoped computation completed; inspect its actual status/flags |
| Authenticated UNKNOWN | false | No additional mathematical decision follows |
| Runtime or connector request refusal | true | Requested operation was refused |
| Missing/changed provider, resource stop or execution/persistence failure | true | Connector returns UNKNOWN without an authenticated successful result |

An unauthenticated retained runtime object is evidence for diagnosis,
not an accepted result. The connector never turns UNKNOWN into exclusion
or promotes a generated source into a compiled proof. A genuine source
backend certificate retains its original covered-class scope and flags.

After provider/platform checks and successful output-root creation, each
accepted-size request gets a unique `call-*` directory under that root.
It retains exact `INPUT.json`, the runtime's
`REQUEST.json`/`RESULT.json` and delegate artifacts, inherited guard
stdout/stderr/receipt, launcher logs and `CONNECTOR.json`. The response
includes paths and hashes. Existing calls are never overwritten; malformed
bounded runtime requests also retain their exact input and refusal.

Calls run serially. Bounds are 256 KiB per original request, 2 MiB per
MCP input line, 8 MiB per runtime result, 35 CPU seconds, 768 MiB address
space and 16 MiB per child output file. The inherited guard also retains
its disk/RAM/cgroup floors and tighter native/source child limits. Default
wall time is 45 seconds; the operator can choose `--wall-seconds` from
1 to 300. Oversized messages are drained in bounded chunks. Stdout contains
only JSON-RPC messages. Active calls are bounded; cancellation notifications
are not processed concurrently during a call. Process termination uses
the inherited guard cleanup. No compiler, background worker or retry starts.

## Python client and verification

The optional example uses the official MCP Python SDK 1.26.0. Install it
in a separate environment; the server itself has no SDK dependency:

```sh
python3 -m venv /tmp/research-mcp-client
/tmp/research-mcp-client/bin/python -m pip install -r applications/research-solver-interop/requirements-client.txt
/tmp/research-mcp-client/bin/python applications/research-solver-interop/examples/sdk_client.py \
  --request research/2026-10-13-astra-unified-solver-0645z/examples/singleton-generator.json \
  --output-root /tmp/research-results
```

Run the focused tests and the official-client end-to-end smoke check:

```sh
python3 -B -m unittest discover -s applications/research-solver-interop/tests -v
/tmp/research-mcp-client/bin/python -B applications/research-solver-interop/tests/sdk_smoke.py \
  --output /tmp/research-mcp-fresh-evidence
```

Use a fresh smoke output directory. [Verification](VERIFICATION.json)
records actual execution and its limits; the [review](REVIEW.md) records
separate static inspection. Approved native binaries were unavailable
in the publishing workspace, so native-success execution is not claimed.
Protocol-client interoperability, existing runtime execution and
native-to-Lean correctness are distinct evidence levels.

The connector follows the parent Apache 2.0 license. `SOURCE-PINS.json`
records derivative reuse of existing public providers, whose own
transitive identity checks remain controlling. It edits no owned runtime,
support package or compiler schedule. Full finite-INDEPENDENT G4,
general G3, physical admission and native refinement remain separate.

Protocol design follows the official
[lifecycle](https://modelcontextprotocol.io/specification/2025-06-18/basic/lifecycle),
[stdio transport](https://modelcontextprotocol.io/specification/2025-06-18/basic/transports)
and [tools](https://modelcontextprotocol.io/specification/2025-06-18/server/tools)
specifications. This minimal fixed-tool server does not claim every optional
MCP feature or interoperability with clients not actually tested.
