# Accepted connected 1,568-source Lean/Lake union

Accepted 2026-10-11 after an actual pinned Lake build, fresh aggregate/full owned audit, and an independent source/artifact/evidence review. This is a formal integration result; general G3/G4 and other outstanding master obligations remain open.

## Exact result

- 1,568 selected source modules, 101,705 owned declarations, 92,153 theorem rows.
- Zero owned axioms, nonstandard axiom rows, or missing selected modules.
- All 100,985 records from accepted 1,504 and all 1,087 records in the G3 profile preserved exactly; their 367 shared records agree.
- Current successful run: 1,498 fresh component checks plus 70 authenticated components from the interrupted first attempt in this same restored executor; aggregate and full audit are fresh.
- These 70 interrupted-run components are a different set from the historical 70-module G3 profile (64 additions plus six shared providers).
- No proof bodies or hypotheses were changed to make the union build.

Exact graph SHA-256: 1a82a47a20257e9fa83bc88c786a55ca82d4dd245952cf4779a646f84a83d825.
Exact mathematical audit SHA-256 after gzip decompression: ee29bc1196c22fb27dd024e8593b0208aba5f4195edbf4895871235ee6e42e53.
Independent human review raw SHA-256: f6dadeee4ad65f8859718bdb474e9cb2baafdc0531a24a3634c3cdfd619d9594.

## Reproduce

Use official Lean 4.33.1 (commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6), binary SHA-256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550 for the reviewed Linux distribution. Check out official Mathlib at0df444a360eaa60ab8c11dca51a86af692955474, resolve its pinned dependencies and obtain its official cache. EXTERNAL-MODULES.txt lists the external roots used here. No custom compiled objects are included or required.

Set CONNECTED_LEAN_BIN to the absolute directory containing this Lean and Lake, and CONNECTED_MATHLIB to the absolute pinned Mathlib checkout; put the former on PATH. From this package run `lake build`. The Lake target invokes the unchanged strict checker through the reviewed namespace and guarded-storage adapters. `lake test -- current/connected` invokes the same target through the explicit working-directory adapter. Every mathematical source is present under source-store by its content SHA-256. SOURCE-BLOB-MAP.json preserves its original public Git object pin.

The guard uses a12GiB package allocation cap, an8GiB free floor, a512MiB individual-file cap, serial kernel checking, ordinary4096MiB/180-second checks, the one exact historical ThetaCertificate5 exception6144MiB/600seconds, and6144MiB/300seconds for the fresh aggregate/audit. Initial available memory must be at least7GiB. Current native libraries and companion artifacts are authenticated, so a different native environment never inherits unverified cache acceptance. Standard Mathlib cache may be reused; custom sources are checked in their selected contexts.

PREPARATION.json and the historical wrappers retain their original preparation-time status and earlier wrapper hashes; the final acceptance and final public manifest supersede those historical status fields. Diffs preserve every wrapper adjustment. `verify_public_result.py` checks a future terminal run against this package's exact complete mathematical audit.

## Public evidence boundary

The complete mathematical audit is published as ordered gzip parts without alteration; concatenate the parts in AUDIT-TRANSPORT.json to restore its exact gzip bytes. The verification script accepts either representation. Source bodies, graph, build scripts and Lake configuration retain exact bytes. Operational receipts/reviews replace execution-host path prefixes with descriptive tokens. PUBLIC-PROJECTIONS.json records raw and projected hashes; projected operational evidence is explicitly different bytes, not a claim that the original receipt hash hashes its public projection.

All1,570 exact loader trace payloads (about344MiB gzip), raw operational originals, interrupted/failed evidence and full local cache authentication are preserved locally. The public LOCAL-ONLY-TRACE-INDEX.json contains their verified raw/archive/receipt hash map; it does not include those payloads or make them publicly retrievable. Independent review actually rehashed/restored those local bytes. This packet supports source reproduction and exact audit comparison; the local native-trace authentication cannot be independently replayed solely from this smaller public distribution.

The previous accepted source commit is38f51fdff9ffa427ec7dabb591ef94711c322a7a; G3 additions are fromf1636499b963d3982b2dfff0f2757042b1796d21. Newer upstream G6/COMMON/compression additions and the two draft G4 source adapters are deliberately outside this frozen union and require separate exact-version reconciliation.
