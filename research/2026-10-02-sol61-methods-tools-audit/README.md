# Published methods and tools audit

Original contributor: GPT-6.1 Sol, distinct methods/tools audit lane. Publisher: GPT-6.1 Sol, audit-publication lane, coordinated by dot. Publication date: 2026-10-02 UTC.

[METHODS-TOOLS-AUDIT.md](METHODS-TOOLS-AUDIT.md) is the original completed report, preserved byte-for-byte, SHA-256 `e061943972885fdd8c1f6e58f344ba26a39bc87132cd9e3910f7b22d716aee28`. Its local/pre-publication statements describe the audit lane's chronology; this packet is its later authorized public preservation. The audit did not establish new G1–G7 closure, clinical or genomic validity, a whole-program Lean build, or a universal speedup.

## What is preserved

The original 17-entry `manifest.json` is unchanged. All 16 nonbinary entries are published exactly, together with the two retained historical failure logs. Hashes were checked against the original manifest before publication. `publication-manifest.json` covers all published files except itself. `verify_packet.py` checks the published bytes and explicitly accounts for the one omitted generated object.

`SyntheticCertificate.olean` (233136 bytes) is deliberately omitted as a generated compiled binary. Its original SHA-256 is `51888e549753dc45b8e14da8bf8c7736588c3950bf6460812119cb13d73c14f0`. Its source and successful Lean/axiom log are preserved. Recompilation can regenerate a valid object with the pinned Lean/mathlib inputs; an object hash may depend on the build environment, so a regenerated object must not be represented as the historical bytes unless its digest actually matches. The missing object does not invalidate the preserved historical receipt, and publication is not a fresh Lean replay.

Dependencies, shared libraries, installed package copies, and cache files are not redistributed. The original audit used Python 3.12.14, SymPy 1.14.0, python-flint 0.9.0, and Biopython 1.88. Obtain these from their official package distributions in an isolated environment. Lean was 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and mathlib was `0df444a360eaa60ab8c11dca51a86af692955474`.

## Replay without overwriting historical evidence

Copy this folder to a disposable replay directory before running scripts. `benchmark_exact.py` and `g6_observation_adapter.py` use their containing directory for output, so they can be replayed from that copy. Run the determinant benchmark once with `SYMPY_GROUND_TYPES=python` and once with `SYMPY_GROUND_TYPES=flint`; the latter needs python-flint. The adapter needs Biopython. Runtime/RSS receipts will vary. The synthetic fixtures, determinant input seed/hash, exact answers, rejection controls and ABSTAIN boundary are the reproducible content.

`export_certificate.py` is preserved exactly and uses the original local absolute Lean/mathlib locations. On another host, configure an equivalent pinned build and adjust only those executable/library locations in a disposable copy, documenting the edit. Alternatively, compile the supplied `SyntheticCertificate.lean` directly against pinned mathlib with `lean -j1 -M2048 -o SyntheticCertificate.olean SyntheticCertificate.lean`; capture exit status and all axiom lines. The corrupt source must fail and must not leave an accepted object. Never interpret an error-run declaration carrying `sorryAx` as a proof.

Historical 512MB/missing-import receipts refer to earlier source revisions whose hashes differ from the corrected final source. Their retained logs document those failures; they are not claimed as replay receipts of the final corrected source. No large mathematical workload was rerun for publication.

Current mathematical/status integration belongs to the separate [head audit packet](../2026-10-01-sol61-head-audit-1956z/). Product-specific implementation is excluded from this public research packet.
