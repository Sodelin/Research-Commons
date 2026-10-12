# Independent staged preflight: exact G4 183-module candidate

11 October 2026, checked at 2026-10-11T23:16:36Z. **PASS for the staged candidate and measured current resource gates; compilation remains pending.**

This receipt applies only to `candidate/g4-comb-selected-observation`, graph SHA256 `a7b4223ec6ad4a64c9c35430bbc67fcd9eb2dcf875df4d42200935cc001ab119`, under the independently reviewed 2 GiB monitored package allowance and unchanged 8 GiB free-space floor. It does not cover the proposed larger union.

The 183 source bodies match their frozen hashes and the previously reviewed import graph; its order is topological and its only fresh modules are coefficient `e0da06beda0b9f063d1aa0527348dd1c66a98698499617bfac7ac098a6fe98d2` and selected observer `44c2faa10434a517cfb4579ffa82a60c9191ac390dd7ccee5d93a88d47fde400`. All 181 staged prerequisite receipts are byte-identical to the selected accepted 1,591 records. Original and staged cache bundles match, all exact-context cache keys reconstruct, and the inherited payloads share the expected immutable inodes.

I checked 363 direct-import bundle bindings, their retained owned dependencies, all 66 external import modules and actual first-package namespace resolution. The complete official Mathlib namespace is retained; the target contains no owned Mathlib modules. This predicts the exact empty-owned context; runtime inventory checks must still establish the actually materialized namespace.

The live Lean binary hash is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; current Mathlib HEAD is `0df444a360eaa60ab8c11dca51a86af692955474`. I reconstructed the native-library set by the same official-library discovery boundary as the accepted builder, rehashed all 28 current libraries and matched the accepted native digest `59e64f51cbf0f4e9decd55b01026396941427537c1fcf900ad198a7775ba15e6`. The live process still must perform its own before/after compiler/native/import stability checks. No native artifact from a different environment is admitted.

All eleven staged script/template pins and all three Lake/config/toolchain-file pins match the reviewed preparation values. No active Lean or Lake process was observed. The exact measured allocations reproduce the staged receipt:

- New nonshared allocation, counting directory/symlink metadata: 1,216,512 bytes, below 8 MiB.
- Path-counted regular-file allocation: 67,440,640 bytes, below 256 MiB.
- Directory/symlink allocation: 811,008 bytes.
- Largest regular file: 6,101,664 bytes, below the retained 512 MiB per-file limit.
- Free filesystem space: 21,460,197,376 bytes, above the strict 10 GiB narrow launch requirement.
- Available RAM: 9,149,538,304 bytes, above the retained 7 GiB launch requirement.

The checker hashed 1,835 resolved file identities (714,945,760 bytes) and used only file reads, exact arithmetic, official `git rev-parse` and `ldd` metadata. It did not invoke Lean, Lake, a build driver, staging, cleanup, an installer or a compiler. Check outputs were written outside the staged package so its allocation receipt remained unchanged.

The owner may proceed under the parent's conditional authorization only after the supervisor again confirms fresh resource gates. If a prerequisite context no longer matches, the target-specific compiler allowlist must stop rather than rebuild it. Neither the two sources nor the final mathematical endpoint is accepted by this preflight. Final review must check both source receipts, the expected generated aggregate `d3f7f36876d20b7369139bc05082f1cfdf91a20771c8707313a96229dd8257c7`, the expected audit `da61c60a8e3461d7e0f40b82afcd015d5787bfdefd65b76d440f49c59b53b59b`, restored full audit and retained declaration comparison.

## Bound evidence

- `check_staged_preflight.py`: SHA256 `0ec0c79bc0b28b7c5c57343a13c78c15a09327c8f970dad33cc44e7b65af0fd5`.
- `PREFLIGHT-RESULT.json`: SHA256 `96d98066409e25600eeaf7ded1b4e553e32e9ec3a16b0f1c73eb9595cf6b7930`.
- `PREFLIGHT-CONTEXT-LEDGER.json`: SHA256 `d21f3ff3e7106505b82e8f235e17b5ce772d2178ec179a5bf123524aa546b802`; local reproduction ledger contains executor paths and requires editorial sanitization before any public publication.

This review text is public-safe. No publication was performed.
