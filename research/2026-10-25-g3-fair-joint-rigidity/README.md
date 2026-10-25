# G3 fair rigidity, joint relative-window rigidity, and global confinement blocker — v2

Author: dot (OpenAI-assisted research). 25 October 2026 UTC. Published source packet; preserves original problem scope.

## Scope

1. **Independently hand-reviewed fair theorem:** all finite counts, heterogeneous weak fair cells and arbitrary positive ordinary gaps; full commutation implies identical reference scales and exact paired integer phase. Read `fullcap-normal/WHOLE-WORD-FAIR-RIGIDITY.md` and `fullcap-normal/whole-word-independent-g4-review/REVIEW.md`.
2. **Independently hand-reviewed biased theorem:** arbitrary coins and counts, but only in one explicit uniform relative cell window. Coupled actual 8→4/10→5 transports exclude singular coin perturbations there. Read `biased-joint-normal/JOINT-RELATIVE-WINDOW-RIGIDITY.md` and its `independent-g4-review/REVIEW.md`.
3. **Global blocker:** exact paired clocks allow super-algebraically invisible microscopic biased insertions with merely approximate commutation. Read `biased-joint-normal/GLOBAL-CONFINEMENT-BLOCKER.md`. This is NOT an exact commuting counterexample.

Original arbitrary-coin AG-Pair/G3 remains OPEN. No full Lean verification, global confinement, historical novelty, or unrestricted G4 result is claimed. Earlier author-status headers are historical; the later independent reviews provide the scoped acceptance.

## Version clarification and preserved evidence

V2 changes metadata/comments ONLY: the DROP5 JSON now calls its stored sum `raw_f5`, explicitly declaring the theorem receiver `f5=-raw_f5`; its generator emits the same clarified metadata. The source generator's stale 8→4 comments now correctly say 10→5. No mathematical coefficients, orientation used by checks, or theorem is changed.

Exact pre-change copies of these three files are retained in `original-evidence/`. `ORIGINAL-SNAPSHOT-HASHES.json` records every original file. Existing nested MANIFEST.json files are frozen historical manifests for their original snapshots, NOT current v2 integrity claims. The root V2-MANIFEST.json alone lists the final packaged bytes. Earlier failed-control scripts/logs remain clearly named and are not counted as passing checks.

## Reproduction

Requires existing Python 3 with NumPy, SciPy and SymPy; no installation is performed. Run `bash replay.sh` from this directory. It reruns the complete exact coefficient generators, source/mixed-path controls, signs, contacts, scaled divisibility/Hessians, independent reviews and dust-clock controls. Logs are in `replay-logs/`. Checks of identities/signs over Q are distinguished from finite-field routing cross-checks in the proofs. Machine replay is not a replacement for the inherited projective/opaque-graft hand suppliers pinned in the papers.

Mathematical “private word” denotes a model object, not private user data. No credentials, local absolute workspace paths, or device data are intentionally included.


## Published archive

Decode [SOURCE-v2.tar.gz.base64](SOURCE-v2.tar.gz.base64) and verify decoded archive SHA-256 `baafd3589c9d2aab0f7c7a0e0d1b00a0f4bf0a2a61267804f3a3976b26ba2ad6`. Its internal source paths above are within that extracted archive. All 15 bounded replay steps passed in the prepared public copy; independent mathematical and exact checks have the narrower scopes stated above. The global source-weighted outlier defect bound remains unresolved. Do not repeat local-window tests as a substitute for global confinement.
