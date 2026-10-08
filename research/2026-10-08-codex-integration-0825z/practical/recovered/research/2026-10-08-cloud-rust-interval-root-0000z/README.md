# Unfinished Rust interval pilot: Codex handoff

Transfer prepared by OpenAI dot on 2026-10-07 after Nolan assigned Rust application, integration and publication ownership to the Codex work team. This is a preserved unfinished engineering artifact, not an accepted arithmetic stage or a production change.

## Status

- Offline locked unit tests: **9 PASS, 1 FAIL**.
- Offline locked optimized build: PASS.
- Differential tests and independent arithmetic/exponential validation: NOT RUN.
- No code or test fix, new build, test execution or benchmark occurred during transfer preparation.

Read [the original handoff](HANDOFF.md) for the exact interfaces, frozen references, failed fixture diagnosis, actual commands and unresolved obligations. A subsequent successful build does not make the failed test pass. The proposed fixture diagnosis is not an executed repair. Only the receiving Codex team should resume implementation and validation.

## Exact copies and explicit derived copies

The 15-file original ZIP is SHA-256 `07b074bf471a9d8b077fe30bd68e45be9e8743d6fe43c29bbf48b4db285ea023`. Its `HANDOFF-MANIFEST.json` is preserved byte-for-byte at SHA-256 `c8b43a83aac626a4d609091675356b9744b8ca68322692697eabd8a87c06eb23`; its historical publication field remains unchanged.

Three transfer files are explicitly derived: each build/test log replaces one absolute local package path with `<package>`, and `scripts/env.sh` removes its executor-local default in favor of requiring the caller to set `TOOLCHAIN_BASE` to an approved existing Rust 1.90.0 toolchain/cache. No software is installed by that helper. This helper edit was not executed. The original handoff's discussion of its old absolute default is historical; use the derived helper's explicit variable requirement.

All Rust source, unit-test fixtures, frozen Python references, Cargo files, original handoff and original manifest are otherwise exact copies. [The transfer manifest](TRANSFER-MANIFEST.json) records actual transferred bytes and SHA-256s, along with both original and derived identities for the three changed files. Use that transfer manifest for the public files; the original manifest describes the original source snapshot and therefore differs for those three files.

Original local artifacts and raw logs are retained. No toolchain, cache, binary, private data, absolute local path or raw machine log is uploaded. Binary hashes identify earlier observed builds, not included executables. Count-pilot publication and all later integration remain separately owned by Codex. Existing Cloud providers, production defaults, workflows and the sole Lean owner's work are unchanged.

## Receiver's next action

Independently inspect the failed fixture and the frozen-reference contracts; preserve its original failure, develop the missing differential and independent controls, and validate any repair before accepting this stage. Do not claim full solver completion, source admission, formal verification, cross-platform portability or a performance gain from this packet.
