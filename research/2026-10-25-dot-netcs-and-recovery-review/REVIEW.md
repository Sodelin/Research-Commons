# NetCS prior work and recovery checkpoint
25 October 2026, 01:45 UTC. Attributed review: dot (OpenAI), requested by Nolan.

## Assessment of the supplied paper
Junyan Dai and Erin K. Molloy, [Is Level-1 Blob Reconstruction Under the Network Multispecies Coalescent Easy?](https://doi.org/10.4230/LIPIcs.WABI.2026.1), WABI 2026. [Publisher and PDF](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.1).

NetCS is useful practical prior work, not a general recognition theorem. It reconstructs level-1 blob structure with a supplied tree of blobs under independent-inheritance NMSC and generic quartet-concordance assumptions. Small blobs have identifiability exceptions. Its fast mode uses O(n log n) quartet subsets and O(n log n k) time for k gene trees; the robust implemented pivot variant has a different, cubic-in-n bound. Gene-count guarantees depend on a positive concordance gap. The experiments distinguish true from estimated trees of blobs: upstream estimation errors can dominate. Independently reconstructed blobs can also have incompatible hybrid placements.

Reading boundary: introduction, model, main algorithm/complexity and sampling statements, practical limitations and evaluation were inspected. This is not an independent verification of every appendix proof, nor a reproduced benchmark.

## Comparison with existing Commons results
Use the [canonical cards](../../docs/CLAIM-BOARD.md) and [machine-readable register](../../docs/claims.json), not title similarity.

- CB-NANUQ-001/002 concern distinct displayed quartet resolutions and structural split geometry in their admitted all-level class. Those arithmetic quantities are not NMSC quartet concordance probabilities.
- CB-EXACTQUERY-001 uses an exact displayed-resolution-set oracle, receives neither a circular order nor a tree of blobs, and outputs split union plus a compatible order. Its Theta(n log n) query result is not a noisy gene-tree reconstruction or native-runtime theorem.
- Consequently, neither result automatically subsumes the other. NetCS is a relevant statistical/implementation baseline and prior-work comparator, not evidence that Commons G3/G4 has closed. Existing quarnet-query antecedents must retain attribution.
- A future integration needs an explicit observation-to-oracle adapter, its error/sample assumptions, and an end-to-end tree-of-blobs acquisition account. This checkpoint does not authorize or claim that new project.

## What the recovery has actually finished
- The register contains **118 separately scoped cards**. Its declared coverage remains first-version/non-exhaustive.
- [Samuel coverage](../../docs/CORPUS-COVERAGE-ROADMAP.md): all 32 original families map to 27 published grouped cards. These are source mappings, not 32 solved programmes or 27 independent novel discoveries.
- [118-card duplicate review](../../docs/CLAIM-118-DUPLICATE-REVIEW.md): bounded statement/lineage comparison found no required merge/removal. It is not a transitive proof audit or complete novelty review.
- [Discovery coverage](../../docs/discovery/README.md) distinguishes indexed bodies from wider archive-path discovery. A searchable filename is not a read or verified proof.
- Completed hand mathematics remains completed regardless of whether formalization is pending. Source recovery is not a new discovery.

## New verification evidence, kept separate from recovery
At assembly commit 8940f035a0bbf2f7855a8247517fc3033ab59c7c, the published owner receipts record:
- [Calibration receipt](https://github.com/Sodelin/Research-Commons/blob/8940f035a0bbf2f7855a8247517fc3033ab59c7c/packages/research/integration/calibration-component-verification.json): complete original CB-MEMORY-004 formal binding for its known-rate IID binary-sample law and all randomized full-sample decisions, plus two checked literal Rust outputs. This supersedes the older blanket “not Lean” statement at that precise scope. It does not establish universal Rust/parser refinement or a dependent/unknown-rate model.
- [Count receipt](https://github.com/Sodelin/Research-Commons/blob/8940f035a0bbf2f7855a8247517fc3033ab59c7c/packages/research/integration/count-prefix-component-verification-v2.json): complete component and two actual proof documents, 92 declarations in three modules, 67 theorem rows, and 125 Rust tests. Generated/projection rows are not discoveries; the old engine is unchanged. Whole-claim binding and universal native refinement remain false.
- That count receipt records the combined 1500-target build rejected at MinimalPathOrderDependencies, with 1421 successful and 78 blocked. Scoped receipts do not certify the whole union or all 118 cards.

These receipts were read in this review; their compiler runs were not rerun here. The assembly is associated with [PR #11](https://github.com/Sodelin/Research-Commons/pull/11), not a claim that its entire package is merged or accepted.

## Precisely unfinished
The exact original p=q=2 companion and LCS continuation source packets still need recovery; wider corpus coverage and contribution chronology are not exhaustive. The combined package needs its failed dependency repaired and the actual union checks completed. Original G3/G4 master obligations remain open as recorded in the [current scope](../2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md). No theorem status, scientific novelty or empirical result is upgraded by this documentation checkpoint.

## Maintenance decision
README and Start Here should point to this same checkpoint, canonical register, current scope and exact receipts. The roadmap's leading 114-card snapshot is historical, not current. Preserve dated history while marking supersession; update substantive findings/corrections rather than rewriting the full scope on every small step.
