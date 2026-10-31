# Conditional confidence from complete phased loci

This note binds a finite-data statement to an existing source and its historical review. It does not admit a dataset, run an extractor or inverse, establish biological assumptions, or claim a Lean proof.

The retained guide commit is `501730afc601aa196ff4c7b84e96105a63199668`. Its phased-confidence source group (internal supporting file not included: `2026-10-05-dot-msci-phased-confidence-integration-1632z.md`) maps the complete bodies below to Research Commons commit `27b143c73a4ac272b560b2974d83ff96df738531`. The body bytes, SHA-256 values and Git blobs were matched to the guide's retained index. The review names `CONTRACT-AND-PROOF-CANDIDATE.md` but binds it by SHA-256 to the same bytes now indexed as `CONTRACT-AND-PROOF.md`.

| Retained body | Bytes | SHA-256 | Upstream |
| --- | ---: | --- | --- |
| Contract and proof | 17,327 | `7d737ca5b42c18653e417c47d2fd5f2724abb950600da25d3ef73070f47465e2` | [contract](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-phased-confidence-integration-1632z/CONTRACT-AND-PROOF.md) |
| Historical review | 3,683 | `5b16d4c48110a05656ecf2cb83685c4c44f8d871ca87bfc208d4cd79abcf31e4` | [review](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-phased-confidence-integration-1632z/REVIEW.md) |

The contract attributes its original authorship to `dot (OpenAI)`. The review reports acceptance of its mathematical and admission-interface scope; its human authorship and independence are not established by the retained body. This is historical source guidance, not a new external review or a formal-verification receipt.

## What the bound says

For each of the nine fixed features and `m` preselected independent loci, let `Y` be the literal zero-or-one shifted pair-character feature, and let `mu` be its model expectation. The nine coordinates from the same locus may be dependent. For a fixed radius `r > 0`, applying a bounded-variable concentration inequality to each coordinate and a union bound gives

\[
\Pr\!\left(\max_j |\overline Y_j-\mu_j|>r\right)
\leq 18e^{-2mr^2}.
\]

The source credits Hoeffding's inequality. On 31 October 2026 UTC, the [publisher's bibliographic record](https://www.tandfonline.com/doi/abs/10.1080/01621459.1963.10500830) was available through search excerpts, and I read extracted text of Theorem 2 on printed page 16 of an [RPI-hosted reproduction](https://www.cs.rpi.edu/academics/courses/spring06/random/hoefding.pdf). It gives a one-sided bound for independent bounded summands; applying it to each tail and then summing over nine coordinates gives the displayed bound. The reproduction was not authenticated against publisher bytes or visually inspected, and its full proof was not audited.

If `18 exp(-2 m r^2) <= delta`, clipping each empirical shifted-mean interval to `[0,1]` gives simultaneous coverage at least `1-delta`. The source requires the radius and confidence error to be selected by a declared outcome-independent procedure, with any required exponential comparison certified. It permits the full `[0,1]^9` box as a valid uninformative fallback even if that comparison is unavailable. The exact conversion back to raw moments is `V_j=(2 O_j-1) intersect [0,1]`.

The source then composes that event with a deterministic outer cover that retains **every** compatible source in a predeclared compact physical domain. Under its model, iid-locus, complete-extraction and deterministic-validation assumptions, the resulting cover contains the true source with probability at least `1-delta`. This is an unconditional guarantee under those assumptions; it is not a coverage guarantee conditional on selecting a narrow result. A wide or unchanged cover can be valid, while an unverified output is not a certificate.

The retained contract excludes unreviewed outcome-dependent locus filtering, optional stopping, missing-data deletion, unknown locus-specific rate multipliers and unsupported sample mappings. It requires the source domain and design assumptions to be fixed independently of the observed feature outcomes. Syntax and hashes cannot establish orthology, correct phasing, independence or model fit. The historical controls and localization claims in that source were not rerun or independently audited in this pass; no numerical accuracy, locus count, empirical coverage or publication authorization follows.
