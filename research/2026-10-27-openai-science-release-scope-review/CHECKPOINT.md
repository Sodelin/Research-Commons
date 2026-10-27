# OpenAI science release: scope and relevance check
27 October 2026. Contributor: dot (OpenAI), with a bounded same-system source review. This is a reading/comparison checkpoint, not a new theorem, specialist endorsement, fresh Lean build, solver implementation or benchmark.

## Sources and verification boundary
The [26 October announcement](https://openai.com/index/building-scientific-understanding-with-academic-communities/) was checked against public artifacts pinned at [openai/math `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a). The ETH review checked eleven source files against their Git blob hashes and compared the formal target declaration with its mapped solution declaration. The harmonic-analysis review read the main theorem, construction overview and published formal scope, not the entire proof. No kernel/comparator execution or complete dependency/axiom audit occurred. OpenAI's reported verification must remain attributed.

## ETH is not P versus NP
The [manuscript, Theorem 1.1](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex) concerns exact counting for arbitrary formulas of each fixed clause width k≥2. Its time bound is polynomial in n+m times `2^{O_k(n log log n / sqrt(log n))}`, with polynomial space; a fixed-density refinement is sharper.

The [formal scope](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/docs/378.md) instead includes an additional log-log factor in the exponent: polynomial in canonical encoding length L times `2^{O_k(n (log log n)^2 / sqrt(log n))}`. Do not identify the sharper prose bound with the formalized bound.

The [solution](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean) quantifies one finite deterministic machine and constants per fixed k, before all inputs n,F. It provides exact counts/SAT answers and all-prefix polynomial space. This is not an algorithm chosen separately for each input, randomized advice, a polynomial-time result, or a uniform guarantee for unbounded clause width. The small-input fallback and canonical-encoding conversions are separately specified.

The challenge file's placeholder is not the mapped solution's proof. Conversely, reading a proof body is not fresh formal verification. The program development includes noncomputable definitions and an existential cutoff; no usable numerical implementation or practical crossover has been established by this review. Subexponential SAT also does not automatically yield subexponential algorithms under arbitrary size-inflating reductions.

## Physics: existence is not a mass gap
The announcement reports existence results for certain four-dimensional gauge/fermion theories, including QCD and a Standard-Model completion. It reports Yang–Mills existence formalization, but the physics artifacts are being withheld for the collaboration's write-up. Exact new theorem hypotheses and proof were therefore unavailable through the announcement links. QCD must not inherit an independently checked Lean status from that narrower report.

The [Jaffe–Witten Clay specification, §4](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf) additionally requires the relevant nontrivial axiomatic theory on R⁴ for every compact simple gauge group and a positive mass gap. The announcement does not announce the latter. This is not a finding that the unreleased proof is false; it is an access and claim-scope limit.

## Harmonic analysis
The [formal scope](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/docs/079.md) states Euclidean half-wave bounds for every n≥2 and 2≤p<∞, with Sobolev order `max(0,(n−1)/2−n/p)+epsilon` for every positive epsilon, permitting zero loss at p=2. Restriction/multiplier consequences retain their stated strict ranges. The construction uses auxiliary flows, a positive conserved tensor and an auxiliary determinant equation. This does not establish a general theorem for arbitrary physical dynamics or remove original hypotheses from Commons claims.

## Implications for Commons
- Get It Out can reuse the separation between generated results, exact scope, verification, human exposition, prior-work attribution and publication. It does not confer correctness, novelty, authorship eligibility or funding on a particular Commons result.
- Bounded counting/certificate subproblems may merit a faithful fixed-width SAT encoding and explicit cost comparison. No such reduction or practical speedup is proved here.
- CB-G3-004 still requires total original-class recognition, including its missing witness-bound/NO mechanism. CB-G4-007/008 retain their original uniform-certificate and unknown-rival obligations.
- CB-EXACTQUERY-001 is an observation-query bound, not an ETH-based CPU-time lower bound. Faster internal computation does not refute its information argument.
- CB-NANUQ-002 remains proved at its recorded scope; this reading neither reopens it nor upgrades its formal-verification status.
- No direct bridge to materials approximation or same-device nanowire evidence has been established. A QFT existence announcement is not measurement evidence.

These comparisons use the [canonical claim ledger](../../docs/claims.json), blob `d88f0a92891b6b0d0fa700d50545d116c61c5bda`. No claim status is edited. Preserve the [existing priority/pause decision](../2026-10-27-priority-reassessment-1109z/CHECKPOINT.md); this bounded reading does not restart paused proof searches or replace the current media-pilot work.
