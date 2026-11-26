# Alexander 001, round three: geometry and observation

[Alexander's §6](https://arxiv.org/pdf/1212.0186#page=9) motivates the problem but does not specify a unique embedding category. The [September project result](https://vibemathed.com/problem/no-countable-universal-family-of-avoiding-populations-even-with-exact-parent-cou) already excludes countable host families in the unrestricted child-cap setting and retains exact incoming counts. Do not count it as a result newly closed in this round.

## Route A: change the geometry while preserving the entire language

- [One spare child slot](ONE-SPARE-CHILD.md). Starting with any child cap d, give every old vertex at most one new terminal child, retain the exact roots and infinite-word language, and defeat an arbitrary countable portfolio of countable locally finite hosts even at finite edge stretch. Large terminal indegrees power this argument; no fixed indegree is promised. The finite-ball arithmetic and terminal semantics are checked separately; construction in the original real-date model is a hand proof.
- [Binary cap exactly two](BALANCED-BINARY-TWO-SHEET.md). Two-sheet switches encode infinitely recurring triangle-component sizes without changing a single infinite realized word. Merge the two copies of the first root. This yields a hand proof of a continuum antichain of connected binary edge-labelled avoiders with exactly three roots, one parent of each label at every nonroot, and exactly two children at every vertex. A same-cap host has degree four off a finite set, so an embedding saturates each regular vertex's neighborhood. A countable host portfolio can contain at most countably many distinct eventual triangle signatures. This uses no finite terminal padding. Lean checks the unmerged word-language transport, the triangle classification, and finite saturation, not the coalescence or continuum theorem end to end. A separate finite test checks 256 assignments for the merged geometry, not infinite avoidance.

## Route B: certify what an observation forces

[The observation-fibre bridge](OBSERVATION-BRIDGE.md) uses the earlier actual Alexander embedding theorem to implement a typed negative certificate. It identifies the exact existing NANUQ, G4, and G5 endpoints and tests two counterexamples to stronger interpretations. It does not establish that a NANUQ, G3/G4, or G5 observation itself satisfies the certificate premises. No solver, inference pipeline, or experimental biology was changed.

## Recommended council question

Try to make **one** graph property portable by verifying exactly which maps preserve it. On the Alexander side, replay the candidate family end to end and determine whether the fixed-source-color transformation preserves the obstruction. On the solver side, pick one actual finite NANUQ quartet fixture; either prove the invariant for all admitted matching candidates or show two admitted matching candidates on which it differs. Do not try to ingest the whole Lean catalog before passing those tests. No new council or schedule was started.

Replay via `bash replay-round3.sh /path/to/pinned/lean` in the source-only archive (the previous round-one dependencies and hashes are included). [Lean replay](ROUND3-REPLAY.log) and [bounded geometry test](TWO-SHEET-TEST.txt) are distinct evidence.
