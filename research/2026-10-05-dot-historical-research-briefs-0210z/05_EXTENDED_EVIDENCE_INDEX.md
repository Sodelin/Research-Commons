# Research evidence and verification status

Shared index for the two researcher briefs  
Draft dated 4 October 2026 · AI-generated research handoff prepared by dot (OpenAI)

## Release state

- **825 sources:** publicly preserved and combined-tested at commit 5d965cf4695e266352a7eeed1d1addae831ee058; recorded exit 0 on 3 October 2026, 20:05:54 UTC. The run reused checked component objects and freshly ran 16 aggregate imports and 32 complete audits.
- **127 successor sources plus 16 runtime sources:** separately frozen and accepted within the project, making 968 reviewed sources at draft time. A new combined receipt and final public links remain pending.
- **Final combined release:** PENDING. Do not interpret the source-count sum as a tested build. Finalize the two briefs only after the exact package, receipt and scope are verified.

## Full public archive and reading route

Start with the [shared handout](00_SHARED_RESEARCHER_HANDOUT.md). The two technical appendices cover [phylogenetic statements](01_PHYLOGENETIC_RESEARCH_BRIEF.md) and [formal verification](02_FORMAL_METHODS_RESEARCH_BRIEF.md).

- [Research Commons public research archive](https://github.com/Sodelin/Research-Commons/tree/main/research): the hand proofs, reviews, exact checks and Lean packages across this continuing programme. The [repository guide](https://github.com/Sodelin/Research-Commons/blob/main/README.md) supplies broader navigation. These are living pages; use pinned links below for the version reviewed here.
- [Earlier Samuel Alexander research repository](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-): labelled ancestry, sequence avoidance, specieslike clusters and the all-level NANUQ strand. Its [plain-language report](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/MATH-RESEARCH-REPORT.md), [coverage ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/research/publication-2026-09-29/COVERAGE.md) and [formalization guide](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/FORMALIZATION.md) navigate that public corpus. Dated historical status text is not automatically the latest status.

The archive links give access to the full public corpus; the focused map below identifies the primary evidence for the newest claims. Unpublished or unfinished work is not represented as publicly available proof.

## Primary evidence map

| Question | Evidence | What it establishes |
|---|---|---|
| Which baseline bytes and scope? | [825 package](https://github.com/Sodelin/Research-Commons/tree/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package), [manifest](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/SOURCE-MANIFEST.json), [scope](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/SCOPE-CHECKPOINT-20261004.md) | Frozen public source and explicit remaining gates |
| What actually ran? | [terminal receipt](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/certificate/G1-CANONICAL21-LAKE-TEST-TERMINAL-RECEIPT.json), [stdout](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/certificate/G1-CANONICAL21-LAKE-TEST.stdout), [audit index](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/certificate/AUDIT-SUMMARY.json) | Combined test with matching artifact reuse and fresh aggregate/audit checks |
| Can the record be checked or rebuilt? | [hash verifier](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/scripts/verify_public_certificate.py), [build driver](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/scripts/build_profiles.py) | Distinct integrity-check and Lean-check routes |
| What is the fair two-tip result? | [normalization](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/fair-g5-normalization-v1/NORMALIZATION-SCOPE.md), [sharpness](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-04-dot-verified-lean-825-0203z/package/fair-g5-sharpness-v1/SHARPNESS-SCOPE.md) | Normalized Q upper theorem and genuine max-one-panel lower pair |
| What is the stronger three-tip result? | [M3 source theorem](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-01-sol61-head-audit-1956z/G5-TRIPLE-CALENDAR-FULL-TARGET.md) | Hand-level C/S/Q identification under its richer calendar contract |
| Which structural theorem is being formalized? | [G1/G2 source review](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-01-sol61-head-audit-1956z/G1-G2-FRESH-SOURCE-REVIEW.md) | Contextual unranked replacement, exact core bounds and all-n sharpness |
| What are the G6/G7 finish lines? | [G6 review](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md), [nonplanar extension](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md), [G7 exact review](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md) | Scoped hand characterizations, separate whole-Lean and implementation debt |
| What supports a novelty claim? | [bounded prior comparison](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-02-sol61-hg-prior-art/G5-M3-PRIOR-ART-UPDATE.md) | Identifies close precedents and differences; establishes no worldwide priority |

## Reading the labels

A **hand characterization** is an argued mathematical theorem at its stated contract. A **component certificate** checks a bounded set of formal statements. A **combined test** checks the named integrated package. A **source-semantic review** examines correspondence and assumptions. The project’s separately authored AI reviews are not independent human peer review. Passing Lean checks do not determine novelty, biological realism or empirical calibration.

Primary research authorship is retained in each linked source. Earlier joint-law/G6 work credits GPT-6 Astra Pro; source-critical reviews and extensions credit GPT-6.1 Sol; the present formalization/integration package credits dot (OpenAI). Source counts measure coverage, not discoveries.

## All six public VibeMathed entries

Checked on 4 October 2026 through the [public profile](https://vibemathed.com/user/ZestyDingo473) and individual pages. Publication there is curation, not journal peer review; see the [site methodology](https://vibemathed.com/methodology).

1. [All-level NANUQ](https://vibemathed.com/problem/all-level-nanuq-circularity-and-exact-displayed-split-support): Resolved; Unreviewed; Preprint. The full theorem exceeds its formalized components.
2. [Exact Thue-Morse matching heights](https://vibemathed.com/problem/exact-thue-morse-matching-heights-in-an-avoiding-population): Candidate, review pending; Lean-checked, statement unaudited; Announced.
3. [Fixed founder-window clusters](https://vibemathed.com/problem/maximal-specieslike-clusters-with-a-fixed-real-founding-window): Partial result; Lean-checked, statement unaudited; Announced.
4. [Ordinal certificates and pruning](https://vibemathed.com/problem/ordinal-certificates-and-exact-pruning-characterize-sequence-realization): Partial result; Lean-checked, statement unaudited; Announced. An October 2 project comment requests eligibility reassessment because distinct novelty beyond classical source-specific formalization has not been established.
5. [No countable universal avoider family](https://vibemathed.com/problem/no-countable-universal-family-of-avoiding-populations-even-with-exact-parent-cou): Partial result; Lean-checked, statement unaudited; Announced.
6. [Reciprocal-triple-free maxima through 734](https://vibemathed.com/problem/reciprocal-triple-free-sets-the-finite-plateau-at-732): Partial result; Lean-checked, statement unaudited; Announced. The numerical baseline is imported from OEIS.

The six listings do not establish submission or acceptance of every newer result in this packet. No researcher outreach or external endorsement is implied.

