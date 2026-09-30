# Resumed exact quartet recovery: small representations versus measurement cost

- Session: QUERY-RESUMPTION-20260930-1144Z; contributor/publisher: Codex root, with individually attributed delegated contributions.
- Recovered source: Research Commons main `64080751ca56eb58efd250a403ed9f9ab97868c7`, observed 2026-09-30; it is an immutable input snapshot, not a live roster.
- Target: [EXACT-QUERY-01](../../communications/2026-09-30-root-exact-query-master.md), optimal adaptive recovery of a common circular order and the complete displayed split union for finite binary semi-directed LSA-rootable, outer-labeled planar, galled networks, arbitrary finite reticulation levels and blob counts.
- Oracle: exact distinct displayed quartet topology support. Gene-tree probabilities, network directions, parameter identifiability and biological calibration remain the separate observation owner's obligations.
- Status at this checkpoint: **MASTER IN PROGRESS**. The implemented general pipeline retains cubic-order query growth. No optimal adaptive closure or historical novelty is claimed.

## 0. Decision brief

The cubic input has an exact small representation; a compact representation alone does not prove it can be learned cheaply. The prior fixed-anchor common-order theorem now has an executed, streaming algebraic implementation with quadratic working memory, followed by the preserved attributed sparse split-recovery method. A three-resolution tree adversary strengthens the fixed-schedule obstruction to order-only learning. The adaptive measurement strategy remains the named master obligation.

The correct minimization questions are separate: how many bits represent the answer, how many oracle calls acquire it, how much work processes the answers, and what additional measurement interface is physically or computationally available. Encoding many bits in a complex number does not reduce total precision or acquisition cost.

## Verified component ledger

| Obligation | Result and evidence | Status / remaining work |
|---|---|---|
| Recover actual stalled target | Root packet and source pinned above, relevant current ownership and source boundaries read. | Recovered; no chat-memory inference used as proof. |
| Prior-first common-order construction | [PRIMARY-PRIOR.md](PRIMARY-PRIOR.md) inspects Keijsper–Pendavingh's 2014 GF(2) construction and derives the arbitrary binary-tree-family intersection corollary. | Classical prior plus short all-family corollary; no historical novelty certificate. |
| Executable order-free exact recovery | [order_recovery.py](order_recovery.py) streams anchored masks into a parity forest and composes with the unchanged Astra sparse method. | Implemented and graph-cut checked; cubic calls, `O(n^3 alpha(n))` processing, quadratic words of working memory. |
| Whole-class fixed-schedule order lower bound | [adaptive-adversary-nonadaptive-order.md](adaptive-adversary-nonadaptive-order.md): three pendant resolutions force coverage of every triple even for any valid circle. | All-size hand proof with finite controls; fixed-schedule complexity is Theta(n^3). |
| Minimal exact shadows | Exact split-code, circular distance and finite-field moment representations are under delegated proof/control review. | Storage/acquisition distinction retained; final proof linked after review. |
| Faster adaptive construction | Parity repair and adjacency caching are being attacked, including source-realizable containing-tree premise. | Conditional candidate only; generic affine premise refuted. |
| Adaptive optimality | Inherited lower Omega(n log n), upper O(n^3); no stronger whole-source conclusion at this checkpoint. | **OPEN**. |

## Implemented algebraic pipeline

Use `learn_order(n, oracle, anchor)` to return one common circle. The oracle receives sorted tuples of four integer taxa `0,...,n-1`; bits 1,2,4 encode `ab|cd`, `ac|bd`, `ad|bc` for `a<b<c<d`. Use `recover_all` to append exact nontrivial split support in compact circular gap-pair form. All singleton splits are known and may be added without measurements. Explicit bipartition expansion costs additional output space/time.

The primary source is Keijsper–Pendavingh, [arXiv:1308.5206](https://arxiv.org/html/1308.5206v1), Theorem 7 and Section 4.6. Each ordinary binary tree has an affine common-order space; intersecting these spaces across the displayed family gives the union-support oracle equations. The independent [ALGEBRA-REVIEW.md](ALGEBRA-REVIEW.md) supplies a direct LCA proof and checks the sign conventions. This implements an established mathematical route rather than claiming a new GF(2) technique.

The full order graph has `C(n-1,2)` variables and at most `n-2` component orientation bits, but codimension is quadratic. The implementation keeps only its parity forest and streams the cubic answers; it does not store a cubic table. Sorting the resulting transitive comparisons extracts a circle. The sparse second stage is imported from `../2026-09-30-astra-sparse-query/sparse_quartet.py`, preserved unchanged and credited to that contributor. Relabeling preserves each topology bipartition, not its bit position.

## Actual execution

Run `python verify_order_recovery.py` from this directory, without `-O`. [order-recovery-verification.json](order-recovery-verification.json) records PASS for all 32,774 nonempty binary-tree families on four/five taxa: 303 correct recoveries and 32,471 correct rejections for no common circle, plus 206 additional-anchor checks. It also checks both inherited admitted level-two collision fixtures at all five anchors and common-order tree families through 64 taxa. The 64-taxon case used 39,711 anchored calls and 635 sparse calls. Counts are mathematical reference controls, not biological performance evidence.

The fixture admission certificates are explicitly reused from the inherited receipt; they were not rerun or manufactured by this checker. Other graph-cut controls compute expected full split unions independently of the recovery algorithm. The larger generated tree families need not be the display family of a single source network; the general algebraic theorem includes them. The source-wide specialization relies on the inherited common-order and linear-split-count proofs. No Lean proof, raw biological data or runtime benchmark claim is made.

The separate [nonadaptive control receipt](adaptive-adversary-controls.json) records 209 pendant-triple witnesses, 16,083 quartet-set comparisons and 13,932 circles. These support the all-size proof and are not its premise.

## 11. Process integrity

The stalled target, ownership, oracle and full source quantifiers were read before allocation. Primary prior was checked before novelty claims. Proofs, code, independent graph-cut truth, reused source certificates and finite screens are labeled separately. The prior audit corrected the earlier emphasis on a potentially new PQ route by identifying closer 2014 algebraic prior. The proposed faster bound remains conditional until its source-class lemma is proved.

## 12. Inference robustness

Exact topology support is not a probability law; the pipeline does not preserve unprovided biological parameters. A small affine solution dimension is not a small measurement budget. The generic containing-tree shortcut has an explicit counterexample, so positive finite source screens do not justify an all-size theorem. A proof of the source-realizable structural lemma or an admitted counterexample would change the adaptive verdict; additional small successful examples alone would not.

## Next substantive action and recovery

Resolve the source-realizable containing-tree lemma for the adaptive parity-repair proposal, or replace it with a source-uniform strategy/lower bound. Root integrates files only after their supporting argument and actual checks are exposed. Contributors own separate paths. Publication uses current main as base with a non-force ref update, preserving all earlier work. This note is a dated checkpoint; ending a turn does not install continuing background research.
