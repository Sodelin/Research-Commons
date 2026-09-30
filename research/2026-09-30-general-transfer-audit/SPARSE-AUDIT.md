# Independent scope and implementation audit: ASTRA-SPARSE-20260930-0938Z

Reviewer: /root/current_sparse_scope_audit, 2026-09-30 UTC. Reviewed Research Commons at commit baa4f424f98dbe32065e6c41c78c9d0b26814046. No canonical files or other contributor files edited; no GitHub publication by this reviewer.

## Verdict

The sparse-query contributor has adopted an arbitrary-size, arbitrary-level conditional target rather than substituting level one. Its theorem is for any nonempty family of binary displayed trees sharing a supplied circular order. The written proof supplies the general-size argument; its finite runs are implementation checks and are accurately labeled as such. I found no counterexample or proof defect in the rectangle equivalence, root partition, correctness induction, ancestor charge, or support-independent cap.

The packet is an exact-oracle component of ALLLEVEL-STAT-01, not an end-to-end statistical solution. Complete displayed support inferred from valid biological data, unknown-order recovery, source network identifiability, and source-specific linear split count are not proved by this component. Historical novelty is not established by this audit.

## Proof checks

1. For a<b<c<d, a circular split restricts to ad|bc iff its two gap positions lie in [a,b) x [c,d). In a displayed binary tree a resolved quartet has an internal-path edge witness, so existential support across a tree family preserves the equivalence.
2. Recursing over gap interval [0,n-1) partitions nonadjacent pairs into the two stated cross-half rectangles plus the half-subproblems. The sole omitted cross pair is adjacent. The n-3 nonwrap rectangles and n-3 wrap cells are disjoint and cover all n(n-3)/2 candidates; every queried endpoint is legal.
3. Recursive bisection strictly reduces a noncell dimension. Positive nodes retain exactly the supported cells, so all and only supported candidates are reported.
4. A supported cell has at most 2 ceil(log2(n-1)) positive internal ancestors. Charging nodes to a supported descendant gives P<=2k ceil(log2(n-1)); Q<=R+2P gives the reported output-sensitive bound. A forest with N candidate leaves and R roots contains 2N-R nodes, giving the prespecified dense cap.

## Exact-byte independent rerun

Downloaded sparse_quartet.py and verify_sparse_quartet.py into a unique scratch audit directory. Their SHA-256 values match the packet exactly:

- sparse_quartet.py: 2dd411db0ceb248cb42549eca06c0f1e8510f7ba1837fe544e9ef83e7cefc1fa
- verify_sparse_quartet.py: fb8e9ee60501cc3c68d161beaeab9458952ea407b3092881495ccf9aa8af0b0a

On Python 3.12.14, all three phases independently passed: abstract (16,932 families plus partition n=4..256 and 4,930 single-split cases), graphs (5,796 occurrence-tree instances / 96,299 global selections), and stress (22 scenarios, four invalid-input controls, one deliberately wrong valid oracle). Fresh receipts are verification-abstract.json, verification-graphs.json, and verification-stress.json in this directory. This reruns the author's checks; it is not an independently designed test suite or raw source-network admission certificate.

## Strongest remaining boundary

The broad common-order theorem does not imply k=O(n). The family of all circular binary trees in a fixed order contains every nontrivial circular split, because each such split can be extended to a compatible binary tree. Hence k=n(n-3)/2 is admissible in the general theorem. A linear bound must be proved for the exact parent network class, with constants independent of level/blob count; it cannot be imported from level-one intuition. The packet already marks that specialization conditional and reports a dense n=16 case with 181 queries vs 104 direct candidate tests.

Likewise, rejecting a crossing topology among visited queries is not a certificate that an unknown supplied order is globally correct. Complete support is an explicit promise; finite checks do not establish its biological identifiability. These obligations are the correct place to focus maximal-target work.

## Process and robustness

This is a bounded mathematical/implementation review, not a systematic literature review or meta-analysis. Accuracy confidence is strongest for the stated conditional theorem and exact-byte reproducibility, weaker for unreviewed source-class embedding, and absent for historical priority or end-to-end biological effectiveness. A genuine shared-order tree-family counterexample to rectangle support, a partition omission, or an invalid all-size charge would reverse the combinatorial verdict. Missing statistical premises block only the end-to-end claim, not the conditional theorem.


## Prior-work addition after scope update

Primary source inspected: Allman, Ané, Baños, and Rhodes, "Beyond level-1: Identifiability of a class of galled tree-child networks", arXiv:2504.21116v1 (29 Apr 2025), Definition 7 and Theorem 5.7. It already proves generic identifiability at arbitrary finite level: class C4 under NMSCind/NMSCcom with two samples per taxon, and C5 with one sample per taxon (with the stated data/model conditions). The classes impose galled/tree-child and small-cycle restrictions and can include nonplanar networks. Thus arbitrary-level identifiability itself is not a new contribution here. This prior result does not, by its theorem statement, give the present supplied-order O(n+k log n) quartet-query guarantee; a computational/query-complexity or finite-confidence improvement must be assessed separately. No exhaustive priority audit was conducted.
