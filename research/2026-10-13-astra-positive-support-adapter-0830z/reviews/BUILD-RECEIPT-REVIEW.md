# Build and receipt scripts: independent source review

Reviewer: Astra Rust integration lane, 2026-10-13. Read-only review while the
single external Lean compiler lane runs. No compiler, runtime test, source
materialization, git mutation, or existing-packet edit was performed.

The selected-source traversal preserves the accepted graph and topological
order. Materialization requires a fresh destination, rejects differing source
collisions, retains the complete baseline, and marks source materialization
separately from compilation. The orchestrator runs batches serially under the
published guard, stops on failures, and creates batch records exclusively.
The following evidence-authentication gaps should be repaired before claiming
the owned-provider build complete. These are source findings; they are not
claims that the current execution already suffered these failures.

## Actionable findings

1. **Check the owned build search path for unauthenticated objects.**
   `build_support.py:69` authenticates external lookup before line 86 prepends
   `state/.lake/build/lib/lean` to `LEAN_PATH`. That directory can already exist,
   and no inventory check rejects extra objects. For example, a leftover
   `Mathlib/Data/Real/Basic.olean` there can shadow the external object just
   verified, even though that module is not one of the selected owned Mathlib
   bodies. Require an empty directory for a new state, and on resume allow only
   selected module artifacts bound to successful receipts; reject unreceipted
   and extra artifacts rather than deleting them. Verify the effective import
   search path after adding the owned path.

2. **Reauthenticate resumed audit evidence and pinned historical reuse.**
   At `build_support.py:92-96`, reuse checks source hash, exit code and artifact
   dictionary, then accepts the saved `axioms` map without checking recorded
   compiler stdout/stderr hashes or rerunning the audit. Consequently the
   final expected-theorem test can use stale/altered metadata rather than the
   preserved actual compiler output. Also require the expected module name
   and a nonempty artifact set containing the target `.olean`; equality of
   two empty dictionaries should never authenticate compilation. For resumed
   fresh compilations, verify both logs and compare the freshly parsed audit
   with recorded metadata. Authenticate reused origins recursively or against
   an immutable receipt pin. In particular, the old kernel/certificate
   `RESULT.json` read at line 73 is not checked against its published packet
   manifest before its source-to-object claims are trusted. Pin that receipt
   and validate its compiler/version context as well as source/artifact bytes.

3. **Bind captured events to the guard's complete output bytes.**
   `capture_batch.py:12-17` reads the guard receipt and parses batch stdout
   without comparing stdout/stderr with `terminal['outputs']`. A truncated
   stdout can silently omit completed compiler events and produce a capture
   which still names the original guard receipt hash. Verify both guard
   output byte counts and hashes before parsing. Keep the current exclusive
   creation of `MODULE-RECEIPTS.json` so a retry does not overwrite evidence.

4. **Checkpoint the interrupted invocation on guard stops.**
   Capture discovers invocations only from completed-event lines. When the
   guard kills the process group during compilation, the current per-module
   `.stdout`/`.stderr` files exist in the state directory but no event/receipt
   may have been written. Those logs are preserved locally but absent from
   the public batch capture. On a stop, inventory receipt-less invocation logs
   against the exact plan, record them as interrupted/unverified, and retain
   their bytes/hashes without manufacturing a successful module receipt.

An additional consistency repair is small: `build_support.py:139` prints the
compiler return code even after an audit failure changes the recorded exit
code to 2. Emit the effective receipt exit code and separately retain the
compiler return code, so event consumers do not see success next to a failed
receipt. Current control flow still stops on the audit failure.

These findings do not require changing the accepted Lean providers, adapter
statements, emitted certificates, or already published packets. They concern
the new runner's trust and evidence boundary. The existing external serial
compiler lane can continue while the future owned-build runner is repaired.

## Reviewed pins

| New packet source | SHA256 at review |
| --- | --- |
| `build_support.py` | `0884d7813628fd8a26f3b6e2de043f349b9d365a6b9d5cd83a7882b27b6e6b46` |
| `materialize_support.py` | `40f5784a9cfa3e12d8d9d373e2120473fdc5281e981151a28921a39bde893ef9` |
| `run_external_batches.py` | `c3809ff9f426d3c6641de7a27298f4d0eacb704fd99e447c96b51860d6cbc8e5` |
| `capture_batch.py` | `8b8fb17545803ffc34f240d02fdb844f22e7b2d9fcb708ad8a88381293369801` |

Referenced helper implementations were read from the frozen
`2026-10-13-astra-unified-solver-0645z` packet: `materialize.py`,
`verify_sources.py`, `build_mathlib_serial.py`, `build_lean.py`, and `guard.py`.
Repairs should preserve these review pins and record new runner hashes rather
than editing historical receipts to claim the repaired code originally ran.
