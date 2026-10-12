# Versioned audit-only streamed output proposal

Contributor: dot (OpenAI), 11 October2026. Development and Python fixture validation only. No Lean invocation or accepted package uses this derivative yet.

## Purpose and boundaries

A full mathematical audit is about116MB raw. Repeatedly creating that raw output then archiving it consumes the small launch headroom. The proposed output-only wrapper captures the exact audit bytes into deterministic gzip as Lean writes them. The generated Lean audit source, imports, selected-module array, declaration enumeration, ownership/axiom rules and all inherited target assertions remain byte-for-byte unchanged. Mathematical component and aggregate invocation paths remain inherited.

The original strict core, authenticated namespace wrappers and supervisor are preserved. `build_streamed_audit.py` subclasses the same full four-owned DesktopBuilder. Its audit-only invoke method is a mechanical copy of the strict invocation with the bounded capture call substituted and explicitly labeled compressed-output receipt fields added. Inventory authentication still runs immediately before/after; compiler command, timeout/memory, source/import hashes, native-library evidence, stdout/stderr checks and sorryAx rejection stay the same. `INVOKE-ONLY.diff` exposes the complete change. The supervisor derivative changes exactly its selected child wrapper, not any limit. The full source graph and cache key rules are unaffected.

## FIFO and completion protocol

The helper accepts only an objectless OwnedAudit invocation in a new isolated working directory and refuses any existing output/partial/archive/manifest path. It creates a private FIFO at the exact original AUDIT-RESULT.json pathname, opens a nonblocking reader and a temporary writer guard before launching the child. The guard prevents premature EOF before Lean opens its writer. It closes only after the child exits; buffered output is drained to actual EOF. The child deadline remains at most300 seconds, with termination/wait and kill/wait fallback on failure.

The raw logical stream has the unchanged512MiB per-file maximum even though compressed storage is smaller. Every complete byte is fed to SHA256 and gzip. Success requires child exit zero, EOF after exit, a complete closed/fsynced archive, exact decompression hash/length equality, valid JSON and matching declaration count. The inherited target then independently checks the precise selected-module order and all original no-owned/nonstandard/missing-module conditions. A kernel success cannot become target PASS from a truncated or malformed audit.

The final archive is linked exclusively at AUDIT-RESULT.json.gz, never overwriting an existing file. The temporary FIFO is removed only after its identity is verified. The complete manifest and receipt bind both compressed and raw identities. `audit_output` remains the logical raw pathname; its auxiliary-output record explicitly says exact gzip transport rather than pretending a raw file exists. A private module-level read dependency is installed only for audit paths registered by this successful invocation. Other graph/cache/ordinary reads use the inherited reader. No global filesystem APIs or historical receipts are changed.

## Failure and interruption

Controlled failure closes and retains the partial gzip and records exit/error, raw-prefix digest/count and retained-archive identities; no admitted complete manifest is created. Missing writer, zero-exit empty output, nonzero exit, malformed JSON, count mismatch, raw overflow and timeout are rejected. Exceptions terminate/wait for a live child.

For abrupt process-group termination, gzip is sync-flushed and fsynced at start and every8MiB of raw data, then a durable append-only checkpoint records exact compressed prefix length/hash and raw prefix length/hash. Read-only `recover_durable_prefix` restores the last complete checkpoint using bounded zlib decoding. It never asserts complete audit acceptance. Partial archive, checkpoint log and any interrupted FIFO remain evidence. The forced SIGKILL fixture recovered8,388,608 exact bytes and retained the FIFO without an accepted manifest. No interrupted attempt is reusable as a successful audit.

## Evidence and runtime qualification

The pinned Lean IO.lean defines IO.FS.writeFile by Handle.mk Mode.write followed by putStr; there is no seek/rename in this layer. Actual official Lean FIFO compatibility has not yet been executed. The first authorized production invocation must establish it; failure remains failure. Python fixtures exercise the pipe/capture protocol only, not Lean/kernel behavior.

The helper and wrapper authenticate their source bytes and record hashes into each new run. The private top-level helper is executed from its authenticated bytes. The inherited immutable namespace loader contracts remain unchanged. Public certificates and final reviewers must explicitly account for logical compressed auxiliary output, re-decompress every audit byte, and compare full declaration records against the accepted parent. Old regular-file final checkers cannot silently be reused on a missing raw audit.

Fifteen bounded Python controls cover valid/delayed writers, no writer, nonzero/partial/timeout cases, malformed/count errors, raw bounds and wrong/missing/corrupt identities. A separate forced process-group interruption control checks durable-prefix recovery. Further independent review and controls are required before activation. Existing20GiB/7GiB launch reserves and12GiB package/8GiB floor remain unchanged.
