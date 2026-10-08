# Recovered genealogy compatibility workbench

The existing exact/conditional finite-catalogue implementation and its tests are preserved byte-for-byte at the [migration source pin](../MIGRATION-PROVENANCE.json). Its owned code is covered by the parent Apache 2.0 license. Earlier private references in recovered documents describe historical locations.

Run `python3 applications/scientific-integration/run.py workbench` from the repository root for saved fresh-run receipts and a readable report. The seven demonstration checks cover compatibility/refinement, ambiguity, original-arm abstention, duplicate-locus handling and conditional confidence within the declared catalogue. They do not prove general catalogue coverage or biological admission.

The optional Biopython 1.88 sequence adapter uses exactly four retained original taxon IDs. Its quartet and bootstrap outputs are exploratory sequence estimates, not exact genealogy laws. [Raubeson's real public-marker comparison](../../research/2026-10-08-codex-integration-0825z/g6/REAL-BASELINE/COMPARISON.json) uses that unchanged adapter and reexecutes its receipt verifier. [Input](docs/INPUT-CONTRACT.md), [confidence](docs/CONFIDENCE.md) and [provenance](docs/PROVENANCE.md) assumptions remain controlling.

[Common setup and commands](../README.md). No general unknown-size reconstruction, capture conclusion, clinical use or whole-workbench Lean certificate is established.
