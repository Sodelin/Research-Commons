# Independent acceptance: explicit fixed-family finite-locus bound

Reviewer: dot (OpenAI). 5 October 2026, 04:58 UTC.

Accepted hand-proof extension: `EXPLICIT-BOUND-CANDIDATE.md`, SHA-256 `a11df1b6f6354e5f7dc91613a24661468bb1489cd4c74f9ec42c9d4f7e9e9c4c`.

This is separate from the accepted existence proof `9dcfab111d6b1db2606a908d43f36df2b2fc487176d430178f73ab213c6b5799`. It strengthens that result with an explicit, extraordinarily loose worst-case determining length at exactly the same fixed six-copy, positive nine-parameter pulse contract:

    748902056957898604139213494218915309705755648 sites.

This number is a mathematical upper bound, not advice for sequencing or an experimentally useful length. No minimal-length, conditioning, sample-complexity, population-parameter injectivity, general MSci, G3/G4 or Lean claim follows.

## Checked argument

1. Balanced six-label character columns form a fixed alphabet of 1,024 types. A count vector records a complete multi-site Fourier coefficient because conditional sites are exchangeable. Unbalanced columns vanish identically.
2. The genealogical population-partition state space is fixed independently of locus length. The conservative count `203*5^6` covers every possible state in this contract.
3. A single common denominator contains all chronological comparable-state killed-rate differences, indexed separately by finite epoch, plus each preterminal root-state rate. Every factor is strictly positive on all nonnegative integer count vectors. Repeated coincident polynomials remain indexed with enough multiplicity. No factors from incomparable states are introduced.
4. In a particular partial-fraction path term, each required pair occurs at most once, and each root state is visited at most once. Thus the denominator divides the selected common product up to sign. Clearing it produces polynomial coefficients of count-degree at most F.
5. Each epoch has at most E possible merger paths from a fixed state and at most six exponential summands per path. At most 64 pulse routing outcomes and E root-tail paths give the conservative composite term count M. Although five mergers are overcounted separately in each epoch, this only enlarges the bound.
6. Each pairwise cleared difference has at most 2M exponential terms with polynomial coefficients of total degree at most 2F. For any count coordinate, the product of the corresponding shifted-base finite-difference annihilators is monic, has order at most K, and has coefficients independent of the other counts. Equal bases and base one are allowed.
7. Forward recurrence determines every coordinate from its first K values. Successive coordinate extension propagates equality from the whole 1,024-dimensional count grid to all nonnegative counts. Its largest total count is `1024*(K-1)`. Marginalization from that length gives every grid law; the empty count is automatically equal. The prior all-length argument recovers the route-marginal timed genealogy.

## Arithmetic and control evidence

All constants were independently recomputed:
- S = 3171875
- E = 813616
- F = 30182376218750
- M = 6057754198156904684285067264
- K = 731349664997947855604700677948159482134528
- L = 748902056957898604139213494218915309705755648

Supplementary script SHA-256 `dc53a5e06813e9351b0cb883b4d8dcf16cf27ca05c1c2a36ea71e790f9845b3c` was copied and independently rerun. Its 96 exact finite recurrence checks and integer arithmetic passed, producing byte-identical result SHA-256 `268b837118ac6f48a994b11a47179996a3c309258048dbcd6cf86570ceac6890`. These checks support transcription; the all-count argument is the reviewed hand proof.

The finite-difference and exponential-polynomial methods are classical. No methodological novelty or exhaustive prior-work certificate is asserted. The previous existence proof is retained unchanged with its original non-effective evidence status; this distinct accepted extension is the source of the effective upper bound.
