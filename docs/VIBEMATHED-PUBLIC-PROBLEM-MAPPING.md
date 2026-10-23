# Public problem mapping on VibeMathed: verified portfolio layer

Prepared by dot (OpenAI), 23 October 2026, 09:46 UTC. Read-only visibility audit. These are public pages retrieved today, not a new correctness review, submission, or execution. Retrieval may use indexed/cached page versions; explicit calendar dates below take precedence over inconsistent relative-age labels.

## Finding

The portfolio was already publicly mapped to named research questions, with source links, scoped claims and differentiated verification notes. This is a real evidentiary layer beyond files merely existing on GitHub. It is distinct from journal peer review. The Thue–Morse matching-height entry records submission on **25 September 2026**, 28 days before this audit; NANUQ records **30 September**. Thus “almost a month” is supported without converting catalogue inclusion into peer acceptance.

All entries below explicitly identify **ZestyDingo473** as submitter and link to the relevant Sodelin repositories; project attribution is based on those source links, not a guessed identity behind a username. Named catalogue editors, the submitter, internal AI reviewers and external mathematical referees are different roles. Approval of an entry is not automatically approval of its proof.

## Core entries requested

### 1. All-level NANUQ circularity and exact displayed-split support

[Live entry](https://vibemathed.com/problem/all-level-nanuq-circularity-and-exact-displayed-split-support).

- **Date:** submitted and entry-approved 30 September 2026; result date separately shown as 29 September.
- **Problem mapping:** Holtgrefe et al., *Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances*, Theorem 4.7 and §6, [DOI](https://doi.org/10.1007/s11538-025-01549-4). The all-level result retains the binary, semi-directed LSA, galled, outer-labeled planar class.
- **Site labels:** Resolved; Unreviewed; Preprint.
- **Reported checking:** the site inspected the artifact/evidence boundary on 30 September and records green hosted workflows. It reports the project's two implementations and support checks, but explicitly **did not rerun the verifiers**. Narrower Lean components are not described as a full all-level formal proof.
- **Visibility beyond a submission receipt:** public statement, named source problem, linked proof/audits, and a visible editor correction history. No unrestricted-network or uniqueness claim.

### 2. Exact Thue–Morse matching heights in an avoiding population

[Live entry](https://vibemathed.com/problem/exact-thue-morse-matching-heights-in-an-avoiding-population).

- **Date:** submitted 25 September; site check dated 27 September.
- **Problem mapping:** the quantitative question in §5 of the separate [avg-netizen classification manuscript, 10 September](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md), not a claim to originate that classification or Alexander's earlier theorem.
- **Site labels:** Candidate (review pending); Lean-checked, statement unaudited; Announced.
- **Reported checking:** green hosted run at `19544a4d`, inspection of actual-path/attained-maximum endpoints and allowed axioms; **no site rebuild or independent informal-to-formal audit**. The source is [Sodelin's pinned height proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d7608c8cc0d5a1205605c0f38631ca05f/notes/FULL-HEIGHT-PROOF.md).
- **Public continuation:** the submitter's 29 September, 20:25 UTC comment links exact finite-edit optimal allowance and phase-height results at `a2644182`. It explicitly preserves the original review boundary; it is not a new site verification of those extensions.

### 3. Thue–Morse: all three Joshi–Rust first-occurrence formulas

[Live entry](https://vibemathed.com/problem/thue-morse-all-three-joshi-rust-first-occurrence-formulas).

- **Date:** submitted 4 October 2026; site source inspection dated the same day.
- **Problem mapping:** Joshi–Rust, Conjecture 3.8, [arXiv:2501.05830v2](https://arxiv.org/abs/2501.05830v2), [journal DOI](https://doi.org/10.1016/j.tcs.2025.115391). The first formula's range explicitly excludes its false `n=1` extension.
- **Site labels:** Candidate (review pending); Lean-checked, statement unaudited; Announced.
- **Reported checking:** hand inspection of definitions, attained global maxima/earliest-start semantics, seven-module source and axiom log; numerical checks for differences 1, 3, 5, 7, 9, 15, 17, 31 and 63. **Not rebuilt**; the build receipt is the author's log, and no independent human statement audit is asserted.
- **Source identity:** links the [Research Commons package](https://github.com/Sodelin/Research-Commons/blob/3bb3cdc9992dd14369bc5b1299ca18fdfd9e93ed/research/2026-10-04-dot-thue-morse-first-occurrence-lean-0550z/package/README.md), distinct from the matching-height entry above.

### 4. Period-doubling prefix palindromic length is not 2-regular

[Live entry](https://vibemathed.com/problem/period-doubling-prefix-palindromic-length-is-not-2-regular).

- **Date:** submitted 4 October; site's rerun report dated 6 October.
- **Problem mapping:** Frid–Laborde–Peltomäki, published Conjecture 2 / [arXiv v2 Conjecture 17](https://arxiv.org/abs/2009.02934v2).
- **Site labels:** Candidate (review pending); Unreviewed; Announced.
- **Reported checking:** reran both submitted complete-state-closure checkers and separately computed finite prefix values through `2^20`. The site explicitly **did not check the all-length hand proof**. Its wording rejects treating the project's AI review as externally independent; no Lean claim is made.

## Additional entries with verified same-project source linkage

These are included as visibility evidence, not extra novel-discovery counts. Their public source links identify Sodelin's work rather than merely sharing a username.

| Public entry | Submission date and source question | Site status and actual evidence boundary |
|---|---|---|
| [MSci identifiability under homogeneous clock-JC](https://vibemathed.com/problem/flouri-et-al-msci-identifiability-transfer-under-the-homogeneous-clock-jc-observ) | 5 Oct; Flouri–Jiao–Rannala–Yang 2019/2020 conjecture, restated Yang–Flouri 2022; links Research Commons | Variant only; Unreviewed; Announced. Site verified source wording and reran the small rational event-compiler control, **not the identifiability proof**. Fixed finite models, specified observation channel and sufficiently long loci remain essential. |
| [Ordinal certificates and exact pruning](https://vibemathed.com/problem/ordinal-certificates-and-exact-pruning-characterize-sequence-realization) | 29 Sep; Alexander 2013 §6; links Work-on-Samuel-Alexander-Research- | Partial result; Lean-checked, statement unaudited; Announced. Manifest/CI inspected, not rebuilt. Crucially, the submitter's **2 Oct comment requests eligibility reassessment** because the construction is a source-specific formalization of classical rank/pruning methods, not established distinct theorem novelty. |
| [No countable universal family of avoiding populations](https://vibemathed.com/problem/no-countable-universal-family-of-avoiding-populations-even-with-exact-parent-cou) | 29 Sep; Alexander 2013 §6, explicit injective-embedding interpretation; same source repository | Partial result; Lean-checked, statement unaudited; Announced. Manifest and green CI recorded; no rebuild or independent statement audit. Does not cover every possible meaning of universality. |
| [Fixed-window maximal specieslike clusters](https://vibemathed.com/problem/maximal-specieslike-clusters-with-a-fixed-real-founding-window) | 29 Sep; Alexander 2026 §6 replacement-constraint direction; same source repository | Partial result; Lean-checked, statement unaudited; Announced. Eight-module/50-endpoint receipt and CI recorded, not rebuilt. Maximality stays within the specified fixed-window class. |
| [Reciprocal-triple-free finite maxima through 734](https://vibemathed.com/problem/reciprocal-triple-free-sets-the-finite-plateau-at-732) | 7 Sep, entry-approved 8 Sep; finite frontier attached to Erdős problem 302; explicitly credits Sodelin and links Sodelin/oldest-conjecture- | Partial result; Lean-checked, statement unaudited; Announced. Records Lean/axiom certificates and exact witness verifiers. The page does not separately say its staff reran them. Numeric values retain the external baseline `f(731)=606`; the parent asymptotic problem is not claimed solved. |

## Coverage and wording

Nine individual public entries and the relevant visible comments were retrieved. This is not an exhaustive catalogue/account census: the retrieved profile lists only six older entries although the October individual pages are available, so its aggregate count is not used. A failed initial height-page fetch succeeded via its verified profile link. The homepage exceeded the retrieval size limit; that did not block the individual-page audit.

Recommended description: **“These results have public, source-linked problem records on VibeMathed, some dating to September, with explicit verification notes and scoped comparisons to the original questions. That is more than unpublished repository storage, while remaining different from independent full-proof review or journal peer review.”** Do not collapse site labels, recorded project proof acceptance, public mapping and external expert acceptance into a single yes/no status.
