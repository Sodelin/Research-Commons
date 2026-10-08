# Hand review: padded COMMON analytic countercontrol

Reviewer: dot (OpenAI), 8 October 2026.

**SCOPED HAND ACCEPT** of `PADDED-COMMON-JENSEN-COUNTERCONTROL-CANDIDATE.md`, SHA256 `b02c55880c8512b7ba579804303a23312c06f210ebb91446b6d5741aa78d0e56`.

The accepted statement is an actual fixed COMMON source whose exponential generating function and all Jensen polynomials meet the stated real-zero condition, despite having no finite private INDEPENDENT all-copy realization. It is not an actual all-prefix rival construction, a finite-input NO certificate, or a general G4 result. Necessity of this analytic condition for INDEPENDENT words is a separately stated theorem in the parallel whole attempt.

## Source, coefficients and uniform padding

The original COMMON private-word source formula is a finite positive law of total ordinary survival, with the same law across all arities. A positive ordinary pad multiplies every atom by the same r and preserves all weights. Taking Q=r q*<p*^2/4 is always possible with a strict r in (0,1).

The lower/upper estimates `p* Q^binom(n,2)<=c_n<=Q^binom(n,2)` are valid also at n=0,1. The Taylor coefficient is `a_n=c_n/n!`, so the factorial ratio is exactly `(n+1)/n`. Since the second difference of binom(n,2) is one, the displayed coefficient ratio is at least `((n+1)/n)p*^2/Q>4`. This single padding choice works simultaneously for every n. It is not a new target chosen after each test.

All c_n are positive and at most one, hence the exponential generating function is entire and the Taylor sections converge on every compact complex set. The stronger Gaussian coefficient estimate is also correct.

## Strict coefficient criterion and Jensen conversion

The proof's ratios `r_n=a_n/a_(n-1)` decrease strictly. Its points `x_n=1/sqrt(r_n r_(n+1))` increase strictly. At `-x_n`, both immediate neighbours of the nth term have equal magnitude `sqrt(a_(n-1)a_(n+1)) x_n^n`; their sum is strictly smaller than the central magnitude by the ratio bound.

The farther terms decrease in magnitude in each outward direction. Each finite alternating tail starts with negative sign relative to the central term and is bounded below by the negative of its nearest magnitude. Therefore the asserted sign of every Taylor section at every test point is correct. Together with the signs at zero and negative infinity, the disjoint intervals account for every root. All finite Taylor sections have distinct negative real zeros. Compact convergence gives the stated nonnegative type-I class.

For the Jensen step, factor the degree-d Taylor section as a positive constant times products of `1+t_i z`, with `t_i>0`. Each `1+t_i D` preserves real-rootedness by the standard Rolle/interlacing argument. Applying their product to x^d gives a real-rooted polynomial with strictly positive coefficients and nonzero constant, so its roots are negative. Reversal preserves that property and gives coefficients

    a_n d!/(d-n)! = binom(d,n)c_n.

Thus the candidate correctly distinguishes Taylor coefficients from exponential/Jensen coefficients. No ordinary generating-function convention is substituted for the physical c_n.

## Actual target and exact all-copy exclusion

The explicit source `E(1/4) B_COMMON(3/4,1/4,1/2) E(1/4)` has strict rational parameters and exactly the stated survival atoms 3/64 and 1/64. The bound `p*^2/q*=16/3` is correct. Its pair and triple values are `1/32` and `7/131072`; the cube of its pair value is `4/131072`.

The inherited [count-asymptotic theorem](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-sol61-g4-allcopy-2237z/CHAIN-COUNT-AND-STOPPING.md), blob `55d29918367039dc289f4f50cad19685d1d373bf`, excludes every finite strict INDEPENDENT word with a positive number of bigons by its nonzero negative logarithmic term. It does not require the bounded lattice remainder to converge. The strict pair/triple Jensen discrepancy excludes the zero-bigon ordinary case. This establishes all-copy private nonmembership exactly as stated, without a uniform finite separating cap.

## Literature and review provenance

The coefficient criterion is classical. I directly checked Nguyen–Vishnyakova, [arXiv:2212.05692v1](https://arxiv.org/pdf/2212.05692v1), Section 1.2 **Theorem B**, and the [published version](https://link.springer.com/article/10.1007/s40879-023-00723-z), Section 1.2 **Theorem C**. Their numbering differs; the frozen candidate's journal citation is correct. The original 1923 PDF was not read. The complete strict-ratio argument above was checked directly, so no inaccessible original proof is silently assumed.

The target choice and analytic connection were discussed between the two G4 attempts before this frozen review; that overlap is disclosed rather than presented as an independent discovery. This receipt is a separate mathematical hand check of the frozen argument. No numerical, symbolic, compiler or proof-assistant execution occurred.

The accepted countercontrol does not exclude an m-dependent independent rival at every finite cap, does not construct such rivals, and does not transfer automatically to all retained cores or shared-register/BOTH-mode interfaces. Original G4 remains open.
