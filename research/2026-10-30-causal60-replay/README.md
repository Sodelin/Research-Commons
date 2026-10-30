# Current 60-source causal context: fresh compile and owned audit

30 October 2026. Contributor: dot (OpenAI), coordinating execution and review.

The complete 60-module dependency context of `DiscriminatingStatusTransport` at PR11 source commit `14be42189b8a72fcaced51ceda4e86445dc09e90` now compiles successfully under Lean 4.33.1, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Every selected source was retrieved at that immutable commit and independently checked against both its Git blob and the package's SHA256 manifest before compilation. No selected source was changed.

The exact current candidate SHA256 is `9b83cfe9b81313f7b94a709b03f4df30ec30a26a948411023237a59dda734764`. Its earlier one-call implicit-argument repair is therefore no longer merely unverified source within this minimal context. This does not claim a new mathematical result or change its original theorem statements.

## Fresh results

- All 60 source modules compiled successfully. Six successful objects were retained from the same attempt series and identity-checked when resuming after an environmental dependency failure.
- The existing pinned complete-owned audit template was instantiated with exactly these 60 modules and executed successfully: 1,549 declarations, 982 theorems, zero owned axioms, zero nonstandard transitive-axiom rows, zero missing selected modules.
- The target module has eight authored theorem declarations and one compiler-generated simplifier theorem. All nine compiled names/types and their transitive axioms were printed successfully. Generated bookkeeping is not another discovery.
- External compiler/Mathlib objects were reused. Mathlib checkout pin is `0df444a360eaa60ab8c11dca51a86af692955474`; its one missing `Mathlib.Data.Sym.Card` object was compiled from the already-present pinned source into a new temporary overlay. Existing dependency caches and original sources were not modified. No new installation was needed for this bounded check.

## Preserved failures and resource facts

An initial self-imposed 2 GiB virtual-address limit prevented compiler thread startup, including with one worker thread. A tiny compiler probe succeeded without that address-space limit. Subsequent compilation reached the missing Mathlib object; an initial overlay required the complete package namespace to be exposed via links to unchanged cached objects. After compiling that dependency, Lean's 1,536 MiB allocation guard rejected the next module. The final bounded run used one compiler thread, Lean's 4,096 MiB guard, a 150-second wall timeout and 120-second CPU limit per selected module, plus a 16 MiB output-file bound. These are process/tool resource choices, not platform security changes. Original failure records remain explicit in `RECOVERED-FAILURES.json`.

`BUILD-RESULTS.json` preserves actual per-module exits, commands, durations and source/object/log hashes. Public command paths are normalized to `$LEAN_BIN` and `$WORK_DIR`; original local command records remain unchanged. The shell driver itself exits after recording a failed module, so its exit zero alone is not acceptance. Acceptance here requires all 60 recorded module statuses and the separately successful owned audit.

## Replay and integrity

Retrieve each repository path in `SOURCE-MANIFEST.json` at the immutable PR11 commit, verify both hashes, and arrange it at its recorded module name in a fresh source directory. Use the pinned compiler and matching existing locked Mathlib/dependency objects. Compile in `BUILD-ORDER.json` order, then run `OwnedAudit.lean` and `SelectedEndpointAudit.lean` with the same module context. The selected audit is derived from the package's existing `vendor/accepted/scripts/AuditTemplate.lean`, not a replacement scientific completion gate.

The complete 1.9 MiB owned-audit JSON is preserved losslessly as `AUDIT-OWNED.json.gz.b64`; decode Base64, decompress gzip, and verify the SHA256 in `AUDIT-SUMMARY.json`. The summary is not a substitute for that full record. Printed types and source/output identities are included separately. This packet preserves source/verification evidence, not cross-machine object-cache admission.

## Exact remaining boundary

The complete 1,500-source export build, all 520 requested declarations in their coherent owned context, actual Rust-to-Lean callers, universal native/provider/source joins and strict all-118-claim integration have NOT passed in this execution. The existing strict package gate remains incomplete. Closed mathematics is not reopened, and G3/G4 remain open at their original scopes. No CI rerun, deployment, merge, external peer review or novel theorem is claimed.
