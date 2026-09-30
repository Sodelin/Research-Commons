# Independent compact-certificate review

Reviewer: /root/stepchange_catalog_review, 2026-09-30 UTC.
Inputs: compact-certificate.md, compact_certificate.py and compact-certificate-verification.json. No implementation was duplicated; independent runtime controls exercised the supplied module and CLI. No GitHub changes, proof-assistant execution, actual IID sampling experiment or scientific validation.

**Verdict: accepted for the stated conditional finite-alphabet, covered-parameter, fixed-stage certificate endpoint.** No arithmetic or theorem-scope blocker found. This replaces the proposed-next status of that restricted endpoint; it does not complete unrestricted constructive or empirical transfer.

## Mathematical and executable correspondence

The direction is correct: source P is postprocessed by one K to imitate target Q. Exact finite-grid primal error U bounds the grid optimum above. The feasible simplex/box dual expression bounds it below. Law perturbation changes every feasible K's grid error by at most rho_P+rho_Q, hence also changes the optimized grid value by that amount. The full-class lower bound restricts to grid parameters; the upper bound uses the same returned K at every parameter and adds both covering moduli. The clipping to [0,1] is valid.

The dual witness has the stated finite-prior decision interpretation. A positive lower bound after subtracting rho certifies a true decision disadvantage; no numerical optimality claim is needed. A nonzero rational primal/dual gap remains explicit. The uniform-kernel/zero-dual fallback gives a valid loose interval, without claiming optimization accuracy.

SciPy only proposes candidates. The executable repairs stochastic/simplex constraints, clips dual entries into their exact box, and recomputes all errors, objectives and interval fields with Fraction. The floating objective is never the certificate. Verification rejects forged arithmetic fields. Float/bool probabilities and budgets are rejected. The exact count-denominator test establishes possible histogram arithmetic, not data provenance.

The integer concentration envelope is sound: its c satisfies 2^c >= 2J/alpha and therefore c >= log(2J/alpha); its upward rational square root bounds sqrt(c/(2N)). The coordinate union bound does not require independence across coordinates or grid blocks, but does require IID samples within each stated law.

## Independent controls actually run

| Control | Exact result |
|---|---|
| Binary source erased to singleton; reverse comparison | 0; 1/2 |
| Singleton source, three opposed deterministic target answers | 2/3 |
| Binary permutation | 0 |
| One center grid for constant source / Bernoulli(theta) target on [0,1], radius/modulus 1/2 | Interval [0,1/2], covering the true full-class value 1/2 |
| Both law errors 1/10 around opposed binary targets | [3/10,7/10] |
| Loose modulus saturation | Upper clipped to 1 |
| No-SciPy identity comparison | Valid loose interval [0,1/2] |
| Coarse denominator repair for three opposed targets | Exact 2/3 |
| Independent CLI generation/verification round trip | [2/5,4/5] |

Ten additional negative controls rejected: float or bool probability, negative error budget, floating alpha, noninteger empirical counts, conflicting error modes, negative kernel, float dual, forged confidence field and forged lower bound. Across 384 combinations of alphabet sizes, N and rounding denominator, exact rational comparisons confirmed the power-of-two envelope and upward square-root rounding. The supplied no-SciPy fixture suite also passed. These are analytic/module controls, not evidence of empirical sampling coverage.

Reviewed arithmetic code SHA-256: `40ab3add2ba6e1213657122a32723fcc7b100a6bee6fd31788b16df21bb15eb5`; manuscript: `5ef031264a34bd5b4816d6a5a8da5f253b36ea24f7b9bee59950f62bc113b86e`. Descriptive metadata additions were pending; arithmetic changes require a renewed review.

Metadata-update receipt: descriptive scope/model/grid metadata and a standalone example were subsequently added. All nine stored exact/automatic fixture certificates were independently reverified against the updated module. Current hashes: code `7ec14e3d80ed534ba35591b4b49ad1c70ff25706d9afb19b3352c5ff32d4b322`; manuscript `2fdb7504416618c10093d9779327b347435c08665ec8d620d2746bcde9ef75e2`; fixture receipt `87f67722bc114e93b2102602464faeb262ed9c20df39650817d31e71367b0ba8`. Acceptance is unchanged.

## Required limits retained

Every realized grid must cover the entire declared parameter class. Known moduli and grid law access are external contracts; finite tables cannot verify the absence of an off-grid spike. The checker does not validate these premises or causal meanings, even when it reports arithmetic verification.

Choosing K using the same estimates is valid because the simultaneous event controls every K. Choosing grid points using those data, optional stopping, or repeated refinement does not inherit fixed-stage coverage automatically. Fresh conditionally IID blocks with predictable sizes, simultaneous coverage over selectable points, or justified anytime bounds are needed. A summable stage failure budget protects repeated certification. Selecting a smaller model family after seeing data needs its own coverage argument.

The prototype consumes supplied tables and certifies them; it does not implement scientific sample collection, validate IID provenance, generate/verify the cover, infer moduli or prove a domain bridge. Rational K supplies an executable randomized rule, but physical implementation and resource usefulness remain application obligations. A discontinuous deterministic support target cannot silently satisfy a vanishing target TV modulus across its boundary. General law transfer still does not identify that hidden answer.
