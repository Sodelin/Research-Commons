# Modular connected Lean/Lake package

This package preserves historical source versions, isolated profile contexts and a coherent current aggregate. The **53 required profiles passed** as the [resource-qualified, reauthenticated union of runs](https://github.com/Sodelin/Research-Commons/blob/a8545d355ff01e8959847af1d6b04b097624ed39/research/2026-10-10-dot-connected-53-qualified-certificate-0842z/README.md).

The source store contains 1,440 exact versions: 1,439 selected by the complete 78-profile inventory, plus one preserved historical whitespace variant. Fifty-three profiles are required; 25 separately source-reviewed provisional profiles are not certified as passes. Source files are content-addressed and shared only when their exact source and import context agree.

The two full aggregate audits are included in the delivery artifact:

- Compatible: 1,124 modules, 93,129 owned declarations, 86,621 theorem declarations.
- Canonical: 1,411 modules, 97,873 owned declarations, 89,920 theorem declarations.

Both report no owned axioms, nonstandard-axiom rows or missing selected modules. Counts overlap and are not additive unique theorem counts. Exact assumptions remain in the sources. This is a formal build/evidence result; it does not close every G1–G7 master statement or establish novelty.

## Portable reproduction

This is a **Linux/glibc** configuration. It uses Python 3, `fcntl`, `/proc`, `ldd`, and glibc loader tracing; no generic Windows/macOS portability is claimed.

Prerequisites:

1. The official Linux Lean 4.33.1 distribution, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The required `lean` executable SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
2. An official mathlib checkout at commit `0df444a360eaa60ab8c11dca51a86af692955474`, with its pinned packages and standard compiled object/IR cache. The official checkout's `lake exe cache get` target retrieves its cache; this package does not ship Lean/mathlib binaries or install third-party software.
3. Set `CONNECTED_LEAN_BIN` to that distribution's `bin` directory and `CONNECTED_MATHLIB` to that mathlib checkout. Put the same Lean `bin` directory first on `PATH` when using Lake.
4. At least 7 GiB measured available memory before each approved 6 GiB exception, plus ample disk for local source contexts, object caches and preserved logs. Logs are retained and can be substantial. Only one compiler process is used.

From this package directory:

```sh
python3 scripts/unpack_delivery.py
python3 scripts/build_resource_qualified.py --check
"$CONNECTED_LEAN_BIN/lake" -R check-build
"$CONNECTED_LEAN_BIN/lake" build connectedQualified
```

The unpacker uses only Python's standard library. It checks every encoded part, the compressed artifact, every decoded member and its exact byte count. It refuses unlisted members, traversal, symlinks or differing existing files. `--verify-only` verifies without extracting. Mathematical source-store files are delivered separately and are not modified by unpacking.

The new target compiles fresh components if no exact-context cache exists. It requires no author directory, old failure receipt or prefilled pass list. Its generated `RESOURCE-QUALIFIED-FINAL.json` records the actual outcome and freshness for that run. The supplied configuration has passed source-pin/policy tests and actual Lake configuration elaboration, **not a fresh end-to-end mathematical replay from this public layout**.

## Resources and preserved commands

Read [RESOURCE-QUALIFIED-RUN-CONTRACT.md](RESOURCE-QUALIFIED-RUN-CONTRACT.md) before running. Ordinary checks remain 4 GiB. Only the exact compatible and canonical aggregate/audit pairs use 6 GiB with their original 300/180-second bounds. The pre-existing exact ThetaCertificate5 exception remains 6 GiB/600 seconds. Trust zero, kernel checking, complete selected audits and exact import pins are unchanged.

The original default `connected` command is preserved; its historical 4 GiB aggregate limits can reproduce the recorded memory failures. The explicit `connectedQualified` target is the new reproduction entrypoint. The historical `remaining49` target is retained for provenance and requires the original run records/raw execution graph; it is not the fresh-download route. `candidates` remains a separate provisional queue.

## Evidence and coverage

[DELIVERY-ARTIFACT-INDEX.json](DELIVERY-ARTIFACT-INDEX.json) pins 25 decoded records: the complete dependency graph, full source-store index, published/local candidate disposition inventories, the two exact full owned audits, resource receipts, compact 53-target certificate, and configuration-check records. The 236,459,333 decoded bytes were round-trip verified; stored xz bytes and all part hashes are separately pinned. Operational metadata projections explicitly retain original/public hashes. No mathematical source or full audit body is rewritten by the projection.

The published-candidate inventory covers 2,832 Lean paths in 464 October 5–9 packets at its exact recorded snapshot, including October 6–8. Paths include duplicates, versions, audits and configs; these are not theorem counts. Later G5 full binary M3 and G6 completed-cell/TV passes are separately indexed and were not silently inserted into the frozen 53-profile graph. General G3/G4 and the newer G7 consumer/extraction candidates remain open. The graph's older status metadata is historical; the current certificate supplies the terminal status overlay.

Full historical/interrupted operational attempt archives remain preserved locally and are not claimed wholly published by this package. The compact certificate and included resource receipts retain the prior 4 GiB failure identities, actual successful resources and cross-run qualifications. The explicit full G2 type/body DAG certificate is a separate result, not implied by the owned axiom/reference census here.

Original source comments, author attribution, assumptions and prior-work references are retained byte-for-byte. This package adds integration and reproduction evidence, not a new mathematical or novelty claim.
