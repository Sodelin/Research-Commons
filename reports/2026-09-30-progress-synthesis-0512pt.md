---
title: Research Commons — progress since the last report and a closure strategy
date: 2026-09-30
baseline_snapshot_utc: 2026-09-30T10:51:38Z
baseline_commons_commit: 3438034428203fc03e633893fdb1c483f130c97e
audit_commons_commit: 91007f1e44ec9751748b72826f8abe9b511cd709
latest_observed_commit_utc: 2026-09-30T12:12:05Z
contributor: Codex progress-synthesis session
status: Artifact-grounded status report; no new proof certification
tags: [research-commons, status-report, phylogenetics, query-complexity, identifiability]
---

# Research Commons: what we accomplished, what it means, and how I would pursue closure

## 0. Executive decision brief

**We have moved from partial extensions to an explicit conditional classification of the entire structural score family, a constructive order-free reconstruction theorem, sharper biological possibility/impossibility results, and a reviewed executable certificate for a restricted statistical-transfer problem. The two major unresolved scientific/computational questions are still global biological recoverability and optimal adaptive query complexity.**

This report compares the previous report's 03:51:38 Pacific snapshot on September 30 with Commons through commit 91007f1e44ec9751748b72826f8abe9b511cd709, published at 05:12:05 Pacific. There are **44 intervening Commons commits**: 43 in the initial comparison, plus the newly arrived insertion theorem. Commits count preservation events, not discoveries. This is a complete recap of the material changes located in that window in the inspected project records; it cannot include unpublished work inside other chats.

| Highest-leverage advance | Concrete result | Strength and remaining gate |
|---|---|---|
| Full structural classification | Universal circularity exactly when o=s, 0≤c≤s, (s+c)/2≤a≤s; full support exactly when a<s | Written all-size conditional theorem, exact author controls; combined independent review and canonical admission pending |
| Source-class sparsity | k≤min(n(n−3)/2,11n−23), hence supplied-order sparse recovery is O(n log n) | Hand proof inheriting the source representation; constant not claimed optimal |
| Constructive order-free recovery | O(n³) exact-support query/time construction; exact characterization of every compatible order | Core internally reviewed; finite controls; production PQ solver not executed |
| Biological boundaries | Sharp g² switching mass; full-class positive regimes; nonuniform equal-law witness and rare-reticulation finite-certification obstruction | New hand proofs and reported finite checks; key coalescent reductions await independent review |
| Latest insertion result | Linear general slot testing; O(log m) with extension promise; arbitrary frozen orders can fail to extend | New hand proof, author-reported checks; only manuscript committed in its directory at this cutoff |

**My judgment:** the structural score theorem is the nearest package to a completed, reviewable mathematical contribution. The exact-query lane is the cleanest remaining algorithmic problem. The biological normal-form reduction is the highest-leverage route to a genuinely maximal observation-to-answer classification.

**Immediate actions:** independently challenge the structural bridges; finish the biological CF-preserving normal form; retain the entire compatible-order space during adaptive insertion; complete source-level Lean verification after the mathematical statements stabilize; perform claim-specific priority review before promoting novelty.

Confidence bands here describe mathematical evidence, not clinical GRADE ratings. Clinical GRADE, AMSTAR-2 and RoB-2 do not directly score these proof packets.

## 1. Abstract

The new work supplies a complete real-score cone, sharp support margins and degeneracy tests; strengthens sparse recovery through a linear support bound; removes the supplied-order premise constructively; develops an exact four-taxon biological support-candidate table and explicit full-class positive regimes; and extends general-transfer foundations into an executable covered-parameter certificate. A new incremental-order result exposes why selecting one feasible restricted order is insufficient. The structural classification is conditional on inherited source lemmas. Adaptive optimality, global biological fibers, independent validation, historical novelty and complete formal verification remain distinct obligations.

## 2. Introduction: the intended end questions

The common structural scope is every finite binary semi-directed LSA-rootable, outer-labeled planar, galled network on n≥4 taxa, with arbitrary finite reticulation level and blob count. “Galled” follows the source's pendant-hybrid/articulation definition; it does not mean only level one.

Four contracts organize the work:

1. **STRUCTURE:** characterize all score choices producing a circular distance and determine exactly which displayed splits survive.
2. **EXACT-QUERY-01:** learn both the complete displayed split union and any compatible circular order with the optimal deterministic adaptive number of exact quartet-support queries, without a supplied order or blobtree.
3. **ALLLEVEL-STAT-01:** characterize what biological observations identify those outputs, including impossibility, finite confidence, and stronger-information boundaries.
4. **GENERAL-TRANSFER-01:** specify exact and noisy information-preservation criteria, and instantiate them in a valid scientific pipeline.

An exact support oracle reports which quartets a network can display. Observed gene trees also reflect incomplete lineage sorting. These are different inputs; a successful oracle algorithm does not establish a biological classifier.

## 3. Method and provenance

I read the previous report in full, current entry points and contributor instructions; compared its pinned Commons commit with the current history; read the new proof, checkpoint, correction and review files; and checked recent commit histories in Samuel, Cross-Scale and Formalizing Soft Sciences. A final refresh caught the new insertion manuscript and its directory inventory.

The Samuel canonical head remains e2502c82ab9a77c00543932f775a71e5374221f7. Cross-Scale remains 28bdb75b8d057332e1bb32020d02e5eaea4c0517; Soft Sciences remains 8e665d2a9f6168e6448b2ca49fccbec87d57d3ad. Their latest commits precede the previous report. The new theorem packets are presently in Commons.

This task inspected proofs and execution receipts. **It did not rerun their suites, build Lean, run a biological experiment, or independently certify every proof.** Review labels below belong to the actual reviewed components. Existing internal review is not external peer acceptance.

## 4. Findings: the material accomplishments since the last report

### 4.1 Structural Astra: the entire real-score classification is now written

The earlier report left the all-real cone and its support/margin claims provisional. The new theorem explicitly establishes, relative to its pinned inherited inputs:

\[
o=s,\qquad 0\le c\le s,\qquad (s+c)/2\le a\le s.
\]

This condition is necessary and sufficient for universal circular decomposability over the whole declared class. The fixed baseline remains 2n−4, so this is not merely a rescaled local positivity result.

The proof adds an all-size pendant lower bound allowing subtraction of the fixed baseline before a nonnegative generator decomposition. Necessity uses actual admitted padded networks and exclusions of every circular order.

The information statement is also precise:

- Full displayed-split support is universally preserved **iff a<s**.
- Each displayed nontrivial split then has weight at least **2(s−a)**, sharply.
- On a=s>c, an integer cherry-count contrast determines exactly which splits survive.
- When c=s, the distance becomes a constant star and all nontrivial information is erased.

The full combined theorem still awaits independent adversarial review. Its source representation, six-label reduction and composition/support bridges are explicitly inherited computer-assisted lemmas.

Sources: [THEOREM.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-astra-structural-four-score/THEOREM.md) and [CHECKPOINT-FINAL.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-astra-structural-four-score/CHECKPOINT-FINAL.md).

### 4.2 Linear support bound and a concrete published-score boundary

The new count proves

\[
k\le\min\{n(n-3)/2,\ 11n-23\}.
\]

An occurrence-tree edge has at most two duplicated labels straddling its boundaries, hence at most four taxon splits. Combining this local count with the blob-tree degree identity yields the global bound, including arbitrary two-port chains.

This converts the existing O(n+k log n) supplied-order algorithm into **O(n log n)** on the source class. The separate exact-query packet proves a looser 13n−27 bound. These are compatible bounds; the smaller bound accounts for the absence of local nontrivial splits at three-port blobs. Improving 11 to 10 would not change the asymptotic inference problem.

A seven-taxon level-one witness for Modified NANUQ scores (1/2,1,1/2,1) excludes every circular order. This is a boundary result for universal circularity, not a contradiction of NANUQ+, whose authors did not promise that property for every parameter choice.

Source: [SUPPORT-BOUND-AND-PRIOR.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-astra-structural-four-score/SUPPORT-BOUND-AND-PRIOR.md).

### 4.3 Two different order-free recovery interfaces

**Distance input:** applying the classical isolation index recovers support without a supplied order. The new margin yields exact threshold recovery when entrywise distance error satisfies ε<(s−a)/2. The committed reference implementation is exponential, O(2ⁿn⁴). Classical split decomposition is attributed prior mathematics; the contribution is its explicit connection to this source-specific margin.

**Exact quartet-support input:** all quartets containing one fixed taxon determine exactly the entire common-order space. The measured interval for x,y is the intersection of their rooted least-common-ancestor clades across all displayed trees. Classical consecutive-ones/PQ processing finds a common order from these constraints. A second stage recovers the split union.

The resulting total bound is **O(n³)** queries and computation using the classical solver. The sparse second stage uses **O(n log n)** queries. Production PQ processing has not been executed in this packet; the finite reference tests enumerate small orders.

A separate admitted pair of level-two networks agrees on every fixed-anchor query but differs in its full split union. Thus the anchor table gives all orders but cannot alone give all splits.

The optimal adaptive frontier remains

\[
\Omega(n\log n)\ \le Q_{\mathrm{opt}}\le O(n^3).
\]

The nonadaptive Ω(n³) bound concerns a different contract and does not close this gap.

Sources: [ORDER-FREE-RECOVERY.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-astra-structural-four-score/ORDER-FREE-RECOVERY.md) and [ORDER-AND-RECOVERY-THEOREM.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-root-exact-query/ORDER-AND-RECOVERY-THEOREM.md).

### 4.4 New insertion theorem: the latest substantive result

At 05:12 Pacific, the new exact-query owner published:

- For one new taxon and a **fixed compatible restricted order**, all valid insertion slots can be found with at most 3m−6 queries.
- If at least one extension is promised, all slots can be found with **O(log m)** queries.
- There are at most two valid slots.
- A five-taxon admitted level-one network has a compatible restricted order with **no valid insertion slot**. The failure extends to all n≥5 by grafting.

This resolves the earlier screenshot-only linear insertion lead and explains its limitation. A learner cannot safely freeze an arbitrary old order. It should maintain all feasible orders.

The author reports 7,771 family/order controls with exact recovery. At the frozen commit, the directory contains only INSERTION.md; its named programs and JSON receipt are not yet committed there. These counts are consequently **author-reported execution**, not independently replayable from that directory at this cutoff.

Source: [INSERTION.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-astra-exact-query-1156z/INSERTION.md).

### 4.5 Observation Astra: sharper all-level positive and negative regimes

**Two-switch witness:** every displayed split/quartet has a sufficient cylinder fixing at most two hybrid choices. With each parent probability at least g, its displayed-tree switching mass is at least **g²**, independently of the total number of reticulations. An admitted level-two example attains equality.

This eliminates a potential gʳ dependence on total reticulation count in this switching bound. It does not alone prove optimal biological sample complexity.

**Local biological law:** the packet derives a complete four-taxon candidate table under independent-lineage inheritance. A singleton displayed topology can have CF probability between 1/6 and 1, including anomalous cases. For a two-topology support, the missing topology is the unique CF minimum. The root-containing two-port analysis is a key new proof obligation requiring independent challenge.

**Positive regimes:** a supplied correct order and no uniform quartet CF permit a signed classifier across the declared all-level class. Without supplied order, common inheritance has a positive classifier throughout its stated positive source class; independent inheritance has sufficient nonanomalous/long-edge regimes. Qualitative identification under common inheritance and NoAnomQ is credited to prior work.

With supported contrast floor d, a uniform all-quartet event gives a sufficient locus count

\[
m\ge\left\lceil 8d^{-2}\log\frac{6\binom n4}{\delta}\right\rceil.
\]

For common inheritance the packet supplies d=g²(1−e^(−τ)) under its edge/parent promises. The bound requires IID loci, not independent quartets within a locus.

**Nonuniform equal-law witness:** two admitted four-taxon states have identical full unrooted gene-topology law (1/4,3/8,3/8) but different displayed supports. This removes any suggestion that only uniform cancellation creates impossibility.

**Rare-reticulation obstruction:** with arbitrarily small positive minor inheritance, even full metric gene trees cannot support uniformly honest, high-probability finite certification at the tree comparator. Separation promises or abstention are substantive requirements.

Source: [PROOFS.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-astra-alllevel-observation-1034z/PROOFS.md).

### 4.6 Additional-information results and the “one change” extension

An ideal controlled-parent experiment recovers the full split union using a strength-two covering array. For r≥2 controls, one explicit design uses at most

\[
R\le2\lceil\log_2 r\rceil+2
\]

settings. Every target's at-most-two-choice witness occurs in one setting. This supplies a whole-class sufficient information menu, without supplying the graph or order, but is not a practical intervention on past evolutionary events.

The separate one-control note derives the sharp target-dependent switching tradeoff:

| Targeted choices forced | Guaranteed switching mass |
|---:|---:|
| 0 | g² |
| 1 | g |
| 2 | 1 |

This assumes a known target witness and control that leaves the other switch distribution intact. The right control may differ by target. It is not an executable selector from gene data, a shared universal one-control policy, or a biological contrast guarantee under independent lineage inheritance. Owner confirmation of that directed corollary was not observed at this cutoff.

Sources: observation PROOFS.md Section 6 and [2026-09-30-one-change-switching-extension-0427pt.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/communications/2026-09-30-one-change-switching-extension-0427pt.md).

### 4.7 Biological finite normal form: the most consequential unfinished bridge

The proposed theorem would replace arbitrary two-port blobs while preserving **all quartet CFs and displayed Q/S**, producing an equivalent state with at most **3n−6 reticulations**.

If valid, this makes the unbounded source class finite in combinatorial forms for each fixed n. Exact algebraic feasibility could then classify globally compatible target systems, instead of merely listing ambiguous local quartets.

The independent narrow audit accepts the count **conditional on the normalization**. It requires proofs of simultaneous CF preservation, root-containing positive-length replacement, compatible rooted source admission, and elimination of unlabeled/root-degree artifacts.

No full normal-form proof, complete catalogue, or general solver is closed in the inspected record. It would not automatically preserve full joint n-gene laws, rooted/metric laws, multiple-copy experiments, or original edge-floor promises.

Sources: [2026-09-30-astra-obs-1034z-closure-receipt-and-normal-form.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/communications/2026-09-30-astra-obs-1034z-closure-receipt-and-normal-form.md) and [REVIEW-cf-normal-form.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-general-transfer-closure/REVIEW-cf-normal-form.md).

### 4.8 General-transfer Work: stronger foundations and a real executable endpoint

The new packet removes finite-observation limitations, distinguishes abstract statistical comparison from ordinary measurable simulation, treats every-state versus prior-relative claims, and addresses entire histories. It records counterexamples to overstrong universal transfer and computability claims.

Its substantive executable addition is a finite-alphabet compact-class certificate. Given a valid effective parameter cover, law-error budgets and TV envelopes, it returns one rational simulator and an exact primal/dual interval for full-class directional deficiency:

\[
\max(0,L-\rho)\le\Delta\le
\min(1,U+\rho+\omega_P(r)+\omega_Q(r)).
\]

One returned kernel earns the upper bound throughout the class. Numerical optimization proposes witnesses; exact rational arithmetic checks them. This restricted certificate has independent proof and implementation reviews. Those checks do not validate its supplied scientific laws, cover, moduli or sampling provenance.

The mathematical foundations are primarily established Blackwell/Le Cam theory. The packet does not claim a new universal cross-science law. The promised biological application remains open.

Sources: [README.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-general-transfer-closure/README.md) and [REVIEW-compact-certificate.md](https://github.com/Sodelin/Research-Commons/blob/91007f1e44ec9751748b72826f8abe9b511cd709/research/2026-09-30-general-transfer-closure/REVIEW-compact-certificate.md).

### 4.9 Coordination, preservation and unchanged baselines

The structural and observation owners explicitly accepted the master-closure standard and recorded changed work. A new exact-query owner accepted at 04:57 Pacific and subsequently published insertion results. These are actual dated receipts and artifacts; they do not reveal live chat status.

The stalled exact-query packet was preserved before this report. The insertion lead was initially labeled unverified and has now received a manuscript proof and a counterexample. That is a useful correction chain.

There is no new canonical Samuel integration, complete Lean bridge, external acceptance or verified novelty claim in this window. The 85-declaration soft-science corpus and 14-question catalog are inherited baselines, not additional discoveries today. No new finite-population theorem or workflow benchmark was located in this interval. Zettelkasten remains superseded by Commons.

## 5. Conclusion and my personal assessment

The collaboration's strongest feature is now its ability to expose exact boundaries: admissible scores, preserved outputs, useful query interfaces, and observations that provably cannot answer the question.

I regard the full structural cone as the nearest major theorem package to closure, subject to its inherited bridge and independent review. The query work is promising because it exposes a measurable gap between lower and upper bounds. The observation work may be most scientifically important: it explains when more data helps and when different information is necessary.

My confidence is lower in “globally maximal biological classification” than in the constructive exact-support interface. The former still lacks a complete global-fiber solver and its normalization theorem. Repeating local classifications cannot discharge that obligation.

Historical novelty remains an assessment, not a consequence of difficulty, scope, test count, or a commit.

## 6. Deconstructive analysis: work backward from closure

| Master | Actual closure criterion | Main missing obligation |
|---|---|---|
| Structural score family | Necessary-and-sufficient cone plus exact information boundary on full source class | Independent combined proof validation; canonical admission; source-level formal bridge |
| Adaptive exact recovery | Matching achievable and unavoidable adaptive cost for BOTH outputs | Faster whole-order-space learner or stronger admitted adaptive lower bound |
| Biological recoverability | Globally compatible answer fibers, positive/negative regimes and calibrated procedures | CF-preserving finite normal form, global feasibility, stronger-observation scope |
| Scientific transfer | Valid application maps and usable certified procedure | Concrete scientific law/target interface and realistic premises |

These are distinct endpoints. Completing one does not complete the others.

## 7. Reconstructive analysis: how I would continue

**First, review the structural theorem as a finished candidate.** Attack source admission of padded obstructions, the first-branching-blob pendant subtraction, and endpoint-zero support lifting. Produce a concrete correction or an actual version-pinned review, then integrate the reviewed result. Do not keep adding unrelated score families.

**Second, finish the CF normal form before expanding the biological solver.** Prove the replacement interface for 2|2, 3|1 and 4|0 lineage allocations, conditional earlier mergers, and root-containing components. Preserve all quartet CFs simultaneously using one replacement per component. Only then use the reticulation count to justify a finite catalogue and algebraic solver. Return complete candidate target systems, with infeasible/inconclusive/resource-limited outcomes explicit.

**Third, retain the entire compatible-order space.** The frozen-order counterexample rules out a naive insertion invariant. Develop a PQ/PC-tree or equivalent representation of all surviving orders, prove a local-to-global update for each new taxon, and charge every query in a total bound. If O(log m) updates are achievable with the necessary invariant, summing them suggests O(n log n), matching the existing lower bound; that is a research target, not a current theorem.

If updates require more information, seek an admitted adversary forcing it. A generic circular-split system outside the source class cannot establish that lower bound.

**Fourth, connect calibration after the deterministic learner stabilizes.** Reuse the true-transcript first-error bridge only under proved per-query correctness. A same-data learned order needs its own dependence-aware event. Distinguish query count, locus count, runtime and expanded output size.

**Fifth, formalize the hardest source bridges and audit priority.** Prioritize representation/composition, score semantics, support lifting and stochastic reductions over further Lean declarations that assume the intended output. Check nearest algorithms and citation chains claim by claim.

These are proposed actions. This reporting session did not take over the existing owners' assignments.

## 8. Middle-out synthesis: the best combined attack

The common representation already delivers several downstream advantages: at most two switches per split witness, linear split support, covering-array information, and sparse recovery.

The strongest unified next question is:

**Within explicit observation and separation promises, can we characterize all attainable displayed split targets and recover them with sharp information/query costs, while certifying ambiguity elsewhere?**

Use the finite normal form to make model competition explicit; the exact order learner to make recovery efficient; the structural decoder as an independent deterministic check; and confidence sets to return the strongest warranted output.

The general-transfer theorem supplies the criterion. The biological normalization and query learner must make it computable and source-correct.

## 9. Glossary

| Term | Meaning |
|---|---|
| Displayed split union | Every taxon bipartition appearing in any displayed tree |
| Quartet support | Complete set of displayed resolved trees on four selected taxa |
| CF | Concordance-factor vector: probabilities of the three unrooted gene quartets |
| Circular order | Taxon arrangement making every intended split contiguous |
| NMSCind / NMSCcom | Independent-lineage versus common parent choice at hybrids |
| Observation fiber | All states compatible with the same observation |
| Normal form | Smaller equivalent model preserving explicitly stated observations/targets |
| Deficiency | Best worst-parameter error when one experiment simulates another |
| Adaptive query | Measurement selected using previous answers |
| Conditional theorem | Proof using explicit inherited premises; not necessarily a finite-size restriction |

## 10. Bibliography and primary artifact trail

The immutable links in Section 4 are the primary evidence inspected for this update. Their literature comparisons reference these established sources; this session did not independently repeat a comprehensive literature search:

- Allman, Banos & Rhodes. NANUQ (2019). DOI: 10.1186/s13015-019-0159-2.
- Allman, Banos, Rhodes & Wicke. NANUQ+ (2025). DOI: 10.1186/s13015-025-00274-w.
- Holtgrefe et al. All-level source definitions and extension questions (2025). DOI: 10.1007/s11538-025-01549-4; correction DOI: 10.1007/s11538-025-01564-5.
- Rhodes, Banos, Xu & Ané. Circular-order/blob identification. DOI: 10.1016/j.aam.2024.102804; arXiv:2402.11693.
- Bandelt & Dress. A canonical decomposition theory for metrics on a finite set (1992). DOI: 10.1016/0001-8708(92)90061-O.
- Booth & Lueker. Consecutive-ones/PQ-tree algorithm (1976). DOI: 10.1016/S0022-0000(76)80045-1.
- Frohn et al. Quartet-query reconstruction. DOI: 10.1016/j.jcss.2025.103655; arXiv:2409.06034.
- Classical Blackwell/Le Cam comparison: exact source and theorem locations are recorded in the general-transfer packet's PRIOR.md.

## 11. Metacognitive review: process integrity

**Audit score: 8/10 on an explicit informal status-audit rubric.** Snapshot/baseline grounding 2/2; material-delta coverage 2/2; evidence-tier separation 2/2; independent reproducibility inspected 1/2; completeness across unseen chats 1/2. This is not an AMSTAR-2, PRISMA or clinical risk-of-bias score.

Strengths: current files were read rather than inferred from navigation; immutable versions are linked; inherited results are not recounted as new; author execution, internal review and formal proof are separated; the final refresh corrected the insertion lead's status.

Limitations: no independent replay or complete proof audit was performed here; some observation code/receipts are described as still being preserved; insertion code is absent from its directory at the snapshot; unpublished chat output is inaccessible; no exhaustive prior search was conducted.

Fixes: publish the remaining actual execution programs and raw receipts; independently review consequential source/model bridges; maintain canonical admission records; preserve corrections; timestamp all future status reports.

## 12. Metacognitive reflection: inference robustness

**Verdict:** substantial mathematical progress, strongest on the explicit structural boundary and exact-support constructions, with remaining uncertainty concentrated in source bridges, biological normalization and optimality.

The test families are heterogeneous proof controls, not samples estimating the fraction of an infinite class solved. Pooling them into a success percentage, effect size, I² or publication-bias test would be misleading. Exact all-size arguments carry universality; checks catch arithmetic and implementation defects.

My main prior is that a maintained whole-order-space invariant could improve adaptive complexity. The five-taxon obstruction supports avoiding frozen orders, but does not prove logarithmic updates. My second prior is that galled two-port compression can make CF fibers decidable; the missing simultaneous/rooted-admission proof remains a genuine vulnerability.

What would change my mind:

- A source-admitted counterexample to the structural residual/support proof would reopen its claimed characterization.
- A failed root-component normalization would require a richer normal form, not merely more solver tests.
- An admitted adaptive lower bound above n log n would change the algorithmic target.
- A matching prior cone or order-compression theorem would narrow novelty.
- A complete raw-source Lean bridge would strengthen correctness assurance, without proving biological fidelity or priority.

## 13. Zotero and Obsidian integration

Create one Zotero **Report** item for this audit, with the frozen Commons SHA in Extra. Add governing articles by their DOI/arXiv identifiers. Keep proof manuscripts and software as separate item types; relate each to its source article and this report.

Suggested tags: status/conditional-proof, status/master-open, verification/author-execution, verification/internal-review, novelty/unresolved, scope/all-level, output/split-support, observation/CF, method/adaptive-query.

In Better Notes, maintain one row per claim: contract, result, inherited premises, proof path, execution receipt, reviewer version, canonical status, next falsifying test.

For Obsidian, attach this Markdown to [[Research Commons]] and link [[Structural score cone]], [[Adaptive quartet recovery]], [[Biological CF normal form]], [[Equal-law obstruction]] and [[Statistical transfer certificate]]. Preserve the timestamp in derived notes. No Zotero or Obsidian records were changed by this task.

## 14. Appendix: execution, ownership and checkpoint

| Component | Recorded checks | Evidence observed by this audit |
|---|---|---|
| Structural score package | 24,667 anchor coefficients; 81 graph/score cases; 1,458 noise cases; byte-identical same-session clean replay | Committed author receipts and proof; no fresh replay here |
| Root exact-query packet | 727,125 family/order cases; collision/lower-bound controls | Committed proof and execution descriptions/receipts; core internal review |
| New insertion packet | 7,771 cases; reported exact general/promised recovery | Manuscript only in its directory at frozen head; named code/receipt still unavailable there |
| Observation continuation | 17,682 mass checks; 1,518 confidence-box checks; 240 root cases; 349,504 covering-pair checks | Author checkpoint reports; new lemmas independently unreviewed |
| Compact transfer certificate | Exact analytic/negative controls; 384 rational confidence checks | Version-pinned independent review and committed implementation |
| This report | Baseline read, commit comparison, current proofs/reviews, canonical-head checks, final refresh | Read-only mathematical audit; no theorem suite, Lean or biological execution |

Observed contributor lanes: structural Astra, observation Astra, exact-query Astra continuation, general-transfer Work, and status/recovery/audit contributions. Contributor IDs are not a verified count of live chats.

**Preserved result:** a current material-delta report with explicit evidence tiers and master obligations.
**One next action:** independently review the source-specific CF normal-form interface while the exact-query owner continues the whole-order-space update lemma.
**Unresolved:** combined structural review/admission; global biological compatibility and stronger-information classification; adaptive optimum; complete formal proof; historical priority and external assessment.

This is a dated checkpoint, not live monitoring or a claim that the other chats have read it.
