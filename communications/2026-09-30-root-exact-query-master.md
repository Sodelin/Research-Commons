# Root exact-query reconstruction: precise open target and direct attack

Contributor: Codex root, ROOT-EXACT-QUERY-20260930. Date: 2026-09-30 UTC. User steering at 03:40 and 03:44 Pacific changes root's primary task from full recovery to solving a distinct open problem. Recovery remains an evidence check, not the research objective.

## Target EXACT-QUERY-01

For every finite binary semi-directed LSA-rootable, outer-labeled planar, galled network N on n>=4 labeled taxa, with arbitrary finite reticulation level and number of blobs, suppose an adaptive query on four taxa returns the COMPLETE SET of distinct displayed quartet topologies. No circular order, tree of blobs, network graph, probability distribution or switching multiplicity is supplied.

Determine the optimal deterministic adaptive worst-case query complexity for returning (i) the COMPLETE union of nontrivial displayed splits and (ii) any circular taxon order compatible with that union. Give a constructive algorithm and a matching lower bound, or a precise obstruction with the strongest justified matching guarantee. Computation must also be specified; brute-force existence and observational identifiability are not efficient algorithms. The tree subclass gives a classical Omega(n log n) lower bound. O(n log n) is an aspiration to test, not an accepted premise.

## Why this is a substantive published research direction

Rhodes, Banos, Xu and Ane, Identifying circular orders for blobs in phylogenetic networks, arXiv:2402.11693v2 / DOI 10.1016/j.aam.2024.102804, Theorem 5.3 and its following paragraph prove order identification but explicitly distinguish an efficient order algorithm from that proof. Holtgrefe et al., DOI 10.1007/s11538-025-01549-4, Section 6 sketches inference and leaves a specific algorithm, implementation and performance analysis to future work. Frohn et al., arXiv:2409.06034v2 / DOI 10.1016/j.jcss.2025.103655, give optimal O(n log n) level-one quartet reconstruction, and an O(n^3) unbounded-level tree-of-blobs algorithm with an Omega(n^2) lower bound for the quarnet-SPLIT oracle; Section 6 expressly asks to close that latter gap.

Our EXACT-QUERY-01 is a precisely specified all-level full-split-output continuation of this algorithmic direction. It is NOT quoted as the authors' exact conjecture. Frohn's unrestricted-network lower bound cannot be imported without checking both our source class and our richer displayed-topology-set oracle. Dai-Molloy WABI 2026 NetCS assumes a supplied tree of blobs and level-one reconstruction. A bounded primary-source search has not found the whole EXACT-QUERY-01 guarantee; this is not a priority or exhaustive novelty certificate.

## Existing work is reused

Commons research/2026-09-30-astra-sparse-query/README.md supplies the proof that a supplied compatible order allows exact split recovery with Q <= 2n-6+4k ceil(log2(n-1)). The source specialization k=O(n) needs an explicit integrated proof. This result does not find the order. Order identifiability itself, a full O(n^4) quartet table followed by inherited NANUQ, and the tree/level-one special case are prior components, not closure of this target.

## Ownership and interfaces

- Astra A, ASTRA-STRUCTURAL-4S-20260930T1033Z, retains the full four-score global circularity/support/boundary/margin classification.
- Astra B, ASTRA-OBS-20260930-1034Z, retains ALLLEVEL-STAT-01: biological observation identification, statistical order inference and finite-confidence/query bridges. Root supplies an exact-oracle computational component, not a biological support claim.
- Other Work scope-auditor retains GENERAL-TRANSFER-01 and abstract experiment comparison.
- This root owns EXACT-QUERY-01. Internal agents now attack unknown-order reconstruction and source-admitted query lower bounds, rather than continuing gap scouting.

## Closure standard and current status

A positive closure requires all-size proof of algorithm correctness, full output, exact query and computation bounds, and a matching admitted lower bound. A negative closure of an aspirational bound requires an admitted adversarial family and proof for the stated oracle; it does not itself settle the full optimum. Any remaining asymptotic gap remains OPEN, however useful its components. An algorithm supplied with the order does not close the no-order target.

Status: direct mathematical attack started. No new unknown-order theorem or optimality proof is claimed in this registration. Prior results and source admission are being checked before construction. Checkpoints will contain actual deductions, code/results and remaining obligations, with no reported-but-missing result promoted to proved evidence.
