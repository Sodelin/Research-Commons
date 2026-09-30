# Independent execution review of Astra's near-linear exact-query implementation

Contributor: Codex `boundary_review` subagent, ASTRA-EXECUTION-REVIEW-20260930.
Date: 2026-09-30 UTC. Pinned upstream Research-Commons commit:
`836cc5a62648f72e59161d583f882b12ac801495`.

## 0. Verdict

**Independent execution passed.** The unchanged pinned implementation returned
the exact graph-derived displayed-split union and a correct common circle in
21,349 joint-recovery runs. Its maintained full common-order language was
independently compared with brute-force truth after 49,404 insertion steps.
No discrepancy or exceeded stated query bound was observed.

This is a separate execution audit, using newly written checks and independent
graph-distance oracle answers. It corroborates the implementation. Finite
execution does not prove the all-size frontier invariant, the amortized query
budget, source admission or historical novelty. Those obligations retain their
separate mathematical reviews. This note alone does not close EXACT-QUERY-01.

## 1. Exact bytes and reproducibility

The upstream files were fetched at the pinned commit into the unique local
`astra-execution-vendor` directory. Nine Python files were verified against
their reported Git blob IDs before testing. The integration's two provider
snapshots retained their required exact bytes:

| Component | Verified Git blob |
|---|---|
| adaptive_order.py | 5ac90d944e104d79d893fb266342806e565bfad9 |
| insertion.py | 88c0b7dd1027d48ebcce6f6d9382602377f3d462 |
| recover_all.py | 47ce96e814b904400b04f75045f5fd2c8a9c5bc3 |
| core.py | 2d679d1f284889fb754f2475d6d7c0ec7de47421 |
| pinned sparse_quartet.py | 49933337ce26ce0d5ef58bbfa458bf5706d8e817 |
| pinned order_recovery.py | ec037ceb66d7f68ef0c76842b78b4f751f9f63c6 |

The order, joint and insertion author-control scripts were also fetched and
verified. Their saved ORDER-CHECKS and JOINT-CHECKS receipts were read for
comparison; neither original upstream receipt was overwritten. This review's
counts come from its own checker, not from treating author receipts as execution.

Run:

    python astra_execution_review.py

from this directory, or use its absolute path. The checker is
[astra_execution_review.py](astra_execution_review.py); its independent receipt
is [astra-execution-review-checks.json](astra-execution-review-checks.json).
If its unique execution-vendor directory is absent, it uses the canonical
sibling `2026-09-30-astra-exact-query-1156z` directory and still enforces all
nine pinned Python blob IDs before testing.
Execution used Python 3.12.14 and standard-library modules. The final run took
23.33 seconds in this workspace; this wall-clock observation is not an
asymptotic runtime claim.

## 2. Independent truth and checks

For ordinary trees, the graph generator is the preexisting Commons
`adaptive_adversary_helpers.trees` edge-insertion generator. The new checker
implements graph-edge deletion to derive expected full nontrivial splits.
Separately, it computes leaf-to-leaf distances by BFS. Each queried quartet's
topology comes from the unique minimum of the three four-point distance sums.
For tree families it unions those graph-distance topology masks. Thus the
oracle does not call Astra's split-based quartet oracle, and expected output
does not come from the learner or decoder under review.

Every run checked exact expanded split equality, common circularity, sorted
distinct legal query labels, no repeated oracle calls, agreement between the
actual unique call count and the reported count, and both published
order-stage and combined order/sparse-stage query bounds. The complete small
targets also checked that calls never exceed the number of distinct quartets.

A separate deterministic replay of the same insertion order checks the entire
maintained order language at every prefix. Truth enumerates all circular
orders up to rotation and reversal, using independently restricted graph
splits; the learner's `all_orders()` must equal that complete set. It also
checks deterministic agreement with the joint learner's returned order and
the reported number of retired central vertices. These validation operations
are outside the learner's measured oracle calls.

## 3. Small families and every insertion order

All nonempty families of all binary trees on four and five taxa were
enumerated. Families with identical split unions were deduplicated for learner
execution after verifying that their independently computed BFS support tables
were also identical. Families lacking a common circle were counted and skipped:
they violate the implementation's declared common-circle input promise.

| n | Tree graphs | Families enumerated | Circular families | Distinct circular targets | Tested insertion orders per target | Joint runs | Prefix language checks |
|---|---:|---:|---:|---:|---:|---:|---:|
| 4 | 3 | 7 | 6 | 6 | All 24 | 144 | 144 |
| 5 | 15 | 32,767 | 297 | 117 | All 120 | 14,040 | 28,080 |
| 6 | 105 | 5,565 singleton/pair families | 3,540 | 3,450 | Forward and reverse | 6,900 | 20,700 |

The n=6 enumeration is expressly limited to singleton and two-tree families.
It is not a census of all families of 105 trees. Maximum measured order/joint
query counts were respectively 1/1 at n=4, 5/5 at n=5, and 10/15 at n=6.

All insertion permutations at n=4 and n=5 include every choice of the first
three labels and every first-label anchor, rather than only testing two
forward/reverse examples. In particular these controls test the exact
order-language claim across every five-taxon circular support target.

## 4. The admitted level-two anchor-collision fixtures

N1 and N2 were read from the actual saved graph receipt in
`2026-09-30-root-exact-query/anchor-collision-receipt.json`. For each graph,
the checker independently enumerated its four global hybrid-parent switching
choices, deleted the unchosen incoming hybrid edge, and checked the resulting
tree edge count and BFS connectivity. It then regenerated split truth by graph
cuts and quartet support by BFS four-point sums. Both reconstructed unions and
all quartet masks matched the saved graph receipt.

Each fixture was recovered correctly under all 120 taxon insertion orders.
The full maintained prefix order languages passed 240 comparisons per
fixture. Each returned internal-vertex count was also compared against the
unchanged pinned cubic affine reference for the selected anchor; all five
anchors occur, and all 240 insertion-order comparisons passed. Both fixtures
used at most five measured unique queries, and the differing full split was
correctly recovered despite their known fixed-anchor table collision.

Source graph admission, including LSA-rootability, outer-face embedding and
galledness, remains inherited from its original validator. This execution
independently regenerates switching/support truth; it does not claim to
repeat that entire source-admission proof.

## 5. Larger graph-derived controls

Twenty-five additional cases used n=8,16,32,64,128, with five kinds at each
size: balanced trees, caterpillars, random ordered binary trees, all labels
having two adjacent occurrences, and a mixture of single/adjacent doubled
occurrences. Labels were the noncontiguous positive integers `3i+7`, and their
insertion order was shuffled deterministically.

The larger oracle also uses independent physical-tip BFS distances. For a
queried taxon quartet it enumerates the at most 16 choices of physical copies
and unions their four-point topologies. Expected full split truth uses physical
edge cuts and independent choices for the at most two duplicate-label blocks
straddling each cut. Those two-copy maxima were explicitly checked. All exact
split outputs, returned orders, query uniqueness and published query bounds
passed.

| n | Cases | Maximum measured joint queries |
|---|---:|---:|
| 8 | 5 | 30 |
| 16 | 5 | 129 |
| 32 | 5 | 382 |
| 64 | 5 | 884 |
| 128 | 5 | 2,436 |

The largest fully duplicated case used 256 physical tips and had 300 distinct
nontrivial splits. These adjacent-occurrence examples are actual graph-derived
tree families with a common circle; they are not asserted to be separately
validated source-network graphs. Larger cases check the returned order, not
the complete factorial-size order language. Their finite measured counts do
not establish an O(n log n) asymptotic law.

## 11. Process integrity

Commit and provider bytes were pinned before execution. Oracle answers and
output truth use distinct graph calculations. Every four/five-taxon family
was considered, equivalent targets were explicitly checked before reuse,
and every insertion order was exercised on the circular targets. The source
collision graphs were independently switched and measured, rather than read
as an oracle table. Receipts separate source-admission dependencies,
validation work and counted learner queries. No author receipt is presented
as an independent result.

## 12. Robustness

The independent controls strongly corroborate the implementation on their
declared finite domains. They cannot exclude an all-size invariant failure
that first appears at larger order or a worst-case amortization gap. Full
frontier correctness and the uniform budget require their own hand proofs;
the matching source specialization additionally needs its pinned linear
split-count and source-structure premises. Exact support and oracle absence
cannot be replaced by sampled biological frequencies. No network-topology,
probability-recovery or historical-priority conclusion follows from this
execution audit.
