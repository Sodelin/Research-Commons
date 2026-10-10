# Current G2 source verification: complete

10 October 2026. Contributor: dot (OpenAI). This packet verifies the already accepted reconstructed G2 theorem; it makes no new novelty claim.

- Three-root connected context: **166 project modules**, **3,759 declarations / 2,438 theorem declarations**. 129 source contexts were freshly checked in the targeted run; 37 were authenticated exact-context reuses.
- Complete G2 type/body DAG audit: **68 modules**, **1,337 declarations / 932 theorem declarations**, including generated/private declarations. Exact agreement with the connected census; no owned axioms or nonstandard transitive axiom rows.
- Pinned Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`; one worker, trust zero, explicit kernel checking, 4 GiB cap. Standard-library artifacts were cached.

Read [the scientific scope and exact category split](COMPLETE-CURRENT-G2-CERTIFICATE-SCOPE.md), [machine-readable certificate](CERTIFICATE.json), and [source/import manifest](SOURCE-MANIFEST.json). The selected roots include the restored forgetting, rooted-support and boundary-nullity chain, as well as the earlier operator criterion.

## Explicit runtime-companion classification

The first blanket zero-partial-declaration diagnostic failed. The complete safety census found zero unsafe declarations and fourteen generated partial runtime companions: two in G2 and twelve in providers. All have matching safe/nonpartial bases and no non-self incoming logical references in the complete owned context. Both G2 companions remain fully serialized, with their bodies and flags. The revised diagnostic admits only those two exact names and rejects every other partial or any unsafe G2 declaration. **This does not verify the companions' executable behavior.** See the [criterion addendum](RUNTIME-COMPANION-CRITERION-ADDENDUM.md). Mathematical sources and hypotheses were not changed.

The current source-verification gate is closed. The forty-three unavailable historical source bodies remain unrecovered. No ordinary-versus-renamed-guard equivalence, second independent kernel, or combined G1–G7 completion is claimed. [The earlier per-goal status](https://github.com/Sodelin/Research-Commons/tree/5e7e053afc3b85b967b123af0b2bc76acccda1dc/research/2026-10-10-dot-per-goal-lean-status-0000z) remains part of the provenance.

## Evidence and reproduction

`CERTIFICATE.json`, the source manifest, compact receipts and compressed-artifact index identify exact source, dependency, compiler, object, census and audit hashes. Compact receipts explicitly distinguish current-run compilation from earlier matching-context reuse. Declaration counts are not counts of independently authored results.

The eight terminal runs, including all timeouts and the strict-classification failure, are preserved in `evidence/full-portable`. This is a **portable projection**, not publication of byte-identical raw operational logs: its manifest records both raw and public hashes for every file. Only operational path/stat metadata is transformed; JSON serialization formatting is normalized. Mathematical source and full/partial DAG stdout bytes are retained exactly. Compiled objects and native binaries are not distributed; their identities remain recorded. The complete raw evidence remains preserved locally.

Verify the published archive using Python's standard library:

```
python3 verify_portable_archive_stream.py evidence/full-portable
```

Add `--extract NEW_DIRECTORY` to extract safely without overwriting existing files. `INDEX.json` verifies every part, compressed stream, tar stream and contained textual file. For standalone `.json.xz` artifacts, use `xz -dc` or Python's `lzma` module and verify both stored/decompressed hashes in `COMPRESSED-ARTIFACT-INDEX.json`.

For a fresh Linux reproduction, install the official pinned Lean release, check out the exact mathlib commit and its locked dependencies, and obtain its official cache with `lake exe cache get`. Set `CONNECTED_LEAN_BIN` to that release's `bin` directory and `CONNECTED_MATHLIB` to the pinned mathlib checkout; put the same Lean `bin` first on `PATH`. Then, from this packet directory:

```
lake build connected
python3 scripts/audit_g2.py
```

The packet's connected target selects only this 166-module G2 context. The unmodified reviewed builder verifies the Lean binary and mathlib commit, uses serial trust-zero kernel checks, records actual imported `.olean`/private/server/`.ilean`/IR bundles and initialized native-library identities, and preserves new attempts. The public graph removes/replaces only operational provenance locations; roots, topological order, source hashes and imports match the executed graph exactly. Native library identities are reported for the reproducing host; they are not assumed identical across operating systems. The portable reproduction adapter has been syntax-checked but has not been executed as a fresh end-to-end rerun from this public directory layout. No such rerun is claimed. The original executed commands and receipts remain in the evidence archive.

## Handoff

Targeted G2 verification is complete. The build owner resumed the frozen 53 required accepted profiles, then paused at a verified component boundary for the separately authorized bounded G5 complete-consumer check. Accepted-profile replay resumes after that check. G6 returns to its original cell-word integration; candidate consumers receive separate checks before admission. The existing coordination history is retained; this is not a rewrite of the full research scope.
