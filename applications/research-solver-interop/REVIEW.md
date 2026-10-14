# Static interface review

Reviewer: OpenAI Codex `rust_interface_inventory` subagent, separate from the connector implementation and execution coordinator. Reviewed 2026-10-14T05:42:20Z. This is an internal static review, not external certification. The reviewer previously inventoried the reused public runtime and native contracts and reported the interpreter-path issue below. The reviewer changed only this review file, and ran no connector, test, SDK client, compiler, native binary or Git mutation.

**Static acceptance:** no remaining concrete implementation blocker identified in the reviewed connector sources. Actual finite execution is the coordinator's separate evidence; this review does not independently establish its reported eleven focused test passes or five official MCP SDK 1.26.0 smoke cases. Approved native-success execution was not available in this publishing workspace and is not claimed here. Neither static review nor protocol execution establishes universal native correctness, physical admission or Lean/native refinement.

## Exact inspected source identities

Paths are relative to this directory. SHA256 values bind this observation; they are not signatures or a formal source-to-binary proof.

| File | SHA256 |
| --- | --- |
| `bridge.py` | `0d6202c61991693d24637f2eda1ae2ef757a5b7740d94702a186e809c0656628` |
| `server.py` | `8779dd29002166956e890f822997ad98c5b9081533446200484ec92b5ac510df` |
| `SOURCE-PINS.json` | `5fbef49e81257a244baba67fd8b6e84d82905b993077bddcc885e1332f9b1c02` |
| `tests/test_connector.py` | `6d993bb06b5ac1f36ab92a13a207d4a823eff75a9a976137b4727d069cb29435` |
| `examples/sdk_client.py` | `9be52106f4bf45e19e760e1cf00782a776e6641f0404e2c50125dcfb7af9dadb` |
| `README.md` (final routing-navigation readback) | `56b9a9dbf214b4509673100ec4d91be611427fb003626288824c056048accb97` |
| `COMMUNICATIONS.md` | `006d2fe26f2c7196ecd0410b5602812d580f0622eb0cc6b4bbde4e6bc9663c69` |
| `VERIFICATION.json` (coordinator's evidence inventory) | `03599b50582e4ed8da35900e0e0668843f3c321f8e6ce913d96f2940d1bc0ea2` |

The pinned reused runtime is SHA256 `07c9e49cd05eea2ac9fe590a0f3b01c922da08deefc55f1c5ca01da4711e7f4b`; the inherited guard is `f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3`. Runtime transitive provider and approved executable checks remain controlling. This additive wrapper does not change owned solver/support sources or compiler scheduling.

## Findings and readback

The initial P2 finding was that bare `--python python3` and `--backend-python python3` became nonexistent paths under the startup directory. Readback confirms `interpreter_path` now resolves bare names through `shutil.which` before environment reduction. Explicit paths and returned PATH selections retain their spelling without resolving virtualenv symlinks. The focused test source now includes operator PATH selection and virtualenv spelling cases; the reviewer inspected those controls without running them.

The bridge writes the original UTF8 request bytes without reserializing the scientific request, delegates to the existing authenticated runtime through its existing guard, and retains the complete runtime object. It checks literal request/runtime identities and semantic process exits. UNKNOWN and source-feasibility flags remain in that complete object; unauthenticated diagnostic objects are explicitly distinguished. Unique directories and exclusive receipt creation preserve earlier calls.

The 256 KiB scientific request bound precedes output creation. MCP input lines are bounded at 2 MiB and oversized lines are drained in bounded chunks; retained runtime results are bounded at 8 MiB. The inherited execution settings are 45 wall seconds by default, 35 CPU seconds, 768 MiB address space and 16 MiB per child file, with inherited resource floors and tighter native/source limits. These are process/file bounds, not a total persistent-storage quota or an aggregate memory proof.

The fixed MCP tools use newline JSON-RPC stdio, an initialize/initialized handshake, notification suppression, structured results and equivalent text content. Calls run serially; cancellation notifications are not processed concurrently during a call. Process termination invokes the inherited guard cleanup, with a bounded escalation path. This review did not execute interruption controls or claim support for every optional MCP feature.

README disclosures about stdio-only transport, unavailable native-success execution, operator-only backend selection, source-search scope, uncompiled support emission and cancellation limits fit the inspected implementation. One precise documentation correction was requested: the sentence promising a directory for every accepted-size request must exclude failures of platform/provider checks or output-root creation before `mkdtemp`. Final readback confirms the corrected wording: "After provider/platform checks and successful output-root creation, each accepted-size request gets a unique `call-*` directory under that root." The README hash above binds this corrected observation. Bridge, server and focused-test source hashes remained unchanged on final readback. Both the P2 implementation finding and the documentation qualification are closed for this static review; no new execution or scientific claim is introduced.

## Additive routing documentation readback

The later four-line README navigation addition and complete `COMMUNICATIONS.md` were inspected. The guide contains public role descriptions and Commons links, with placeholders rather than private endpoint bindings. It publishes no private repository locator, thread/host/device binding, SSH setting, key, UI receipt or private implementation. Its route instructions require actual callable transport, verified recipients, existing authorization and separate acknowledgement; publication is not represented as delivery, receipt or execution. MCP runtime calls remain separate from chat messaging and device operations. Its observed-route paragraph is an attributed coordinator report, not an independently verified transport event by this reviewer. No concrete documentation blocker was identified.

`VERIFICATION.json` labels focused tests as "coordinator-observed exec output; source identities below, not independent rerun" and inventories archived official SDK result and per-call request/runtime/guard evidence. Native-success execution and new Lean compilation are explicitly false, and the scope remains finite protocol/runtime controls. The reviewer read this evidence inventory but did not rerun or independently authenticate its entire archive. This update remains static source/document review only. The final hashes above bind the routing addition and inspected verification record; implementation and focused-test source hashes are unchanged.
