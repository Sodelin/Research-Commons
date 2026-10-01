# Lean verification setup checkpoint

Dedicated formalization lane, 2026-10-01. Executor: dot cloud Linux filesystem.

- Original source: Sodelin/Work-on-Samuel-Alexander-Research-, commit e2502c82ab9a77c00543932f775a71e5374221f7
- Original source attribution is retained. No source files in that repository were changed.
- Top-level formal-full source inventory: 117 Lean files; all match Git blob hashes and the original publication manifest SHA-256 values
- Original exclusions: GraphQuartetPortCounts, SourceProbe, ThetaProbe
- Official Lean release: leanprover/lean4 v4.33.1, Linux x86_64
- Official release archive SHA-256: 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235, checked before executing the compiler
- Actual compiler: Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
- Actual Lean binary SHA-256: e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
- Actual Lake: version 5.0.0-src+819816b (Lean version 4.33.1)
- Pinned mathlib: 0df444a360eaa60ab8c11dca51a86af692955474, checked out from its official repository

Mathlib dependency/cache setup is in progress. No fresh baseline module build has yet completed at this checkpoint. Compilation and explicit axiom logs are required before claiming machine verification. The original final raw NANUQ source theorem remains absent; G3/G4 source closure is not assumed. G1/G2 original final local proof payloads are inaccessible, so their recovered review relays are not Lean proof inputs.

Inventory: baseline-inventory.json. Source tree: pinned-source-tree.json. Bounded setup log: mathlib-cache.log.
