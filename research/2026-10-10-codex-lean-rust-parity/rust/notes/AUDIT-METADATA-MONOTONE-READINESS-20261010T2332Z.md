# Saved-report monotone copy/literal eligibility, 2026-10-10 23:32 UTC

Existing final 1497 and final 1504 reports were read to measure exact-byte reuse. The measurement creates no patch file, restored report or prospective 1505/1506 audit. It hashes and counts a candidate gzip stream, then discards that stream. This is a size/eligibility result, not restoration acceptance.

Each base line of at least 32 bytes is indexed by digest. A target line is copied only after direct byte comparison and only from an offset after every prior copied source range. Other bytes are literal. The target is streamed; the largest file is 14,193,645 bytes, and the largest line is 738,974 bytes. The process enforces 256 MiB address space, 20 MiB per file, 1 MiB per line, 500,000 lines and 32 MiB scratch. Peak RSS was 45,952 KiB; the small source/receipt/log scratch remains preserved unchanged.

| Saved report | Exact copied target bytes | Counted candidate gzip bytes | Existing 1504 gzip bytes |
|---|---:|---:|---:|
| RESULT.json | 630,286 | 1,111,296 | 1,260,699 |
| ACTUAL-IMPORTED-ARTIFACTS.json | 5,001,304 | 619,065 | 1,597,954 |
| NAMESPACE-RESOLUTION-CHECKS.jsonl | 0 | 1,939,005 | 1,917,903 |
| CACHE-INSTALL-TRANSPORT-CHECKS.jsonl | 0 | 203,052 | 200,335 |
| CACHE-INSTALL-ALIASES.json | 2,090 | 312,112 | 310,577 |
| DEPENDENCY-GRAPH.json | 2,613 | 266,320 | 263,116 |

The import-artifact report has the strongest simple reuse: 619,065 counted delta bytes against 1,597,954 existing gzip bytes. The result report yields 1,111,296 against 1,260,699. Whole-line copying finds no exact namespace or transport JSONL rows because run context/destination paths occur inside every line. Metadata fields are retained verbatim; no path substitution or semantic reserialization is performed. Those literal-only cases and the weaker alias/graph candidates should keep their existing ordinary compression strategy. Selecting the smaller existing-gzip/count result per file in this historical pair totals 4,422,292 bytes against 5,550,584 existing gzip bytes, a measured eligibility difference of 1,128,292 bytes. This is not a guaranteed saving for an unrun union.

The counted candidate streams use zlib gzip level 6. The accepted portable gzip files can use a different compression level/header; their actual byte sizes and digests are preserved separately. The same-level full-report counters are also recorded in the [measurement receipt](/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/evidence/audit-metadata-monotone-eligibility-1/RECEIPT.json). No candidate output was restored or independently replayed, so the exact copy partition establishes eligibility only.

A future approved exporter can retain the frozen copy/literal wire layout. For monotone ranges, a decoder can consume the base gzip once, hash skipped and copied bytes, and emit target bytes directly into a bounded compare/hash consumer. It need not allocate a second target file. For the unordered declaration-record reuse demonstrated separately, source offsets are not monotone: one-pass portable replay still needs approved raw-base storage for random reads, or an approved target file with random writes. The current 32 MiB experiment allowance does not authorize either additional 114 MiB file.

For a future 1506 producer, use only one authenticated old-base map/index and stream bounded new declaration records; do not map two large files. Compress the patch directly into a create-new file with a root-approved output-byte cap. Preserve every changed declaration, context string, count and envelope byte as literals. Actual new compiler output and its independent source/kernel receipts must exist before any export or acceptance claim. Separate family/G6 results cannot be combined into a synthetic owned-audit report.

Design's fixed-patch review identified an important qualification: the existing immutable prototype checks literal target overflow after writing. Its fixed saved patch is valid, but a generic decoder must authenticate frozen patch hashes, cap operation/copy counts, and check source/target ranges before writing. [READINESS.json](/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/evidence/audit-metadata-monotone-eligibility-1/READINESS.json) records those preconditions and the separate allocation gate. No production codec is inferred accepted from this measurement.

Attribution: the Rust implementation role authored this standard-library storage measurement under root's read-only allocation instructions. The exact accepted Lean reports and portable exports remain unchanged. No mathematical provider, compiler, native solver, law reference or new source engine was executed.
