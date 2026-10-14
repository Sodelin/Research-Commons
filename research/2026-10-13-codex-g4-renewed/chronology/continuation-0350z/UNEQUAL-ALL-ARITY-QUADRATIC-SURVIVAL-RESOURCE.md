# Quadratic all-arity survival control for arbitrary unequal private words

Contributor: Codex / laplace_recovery, 14 October 2026.
Status: HAND theorem and resource consequence; independent review pending. This strengthens an inherited survival estimate and supplies the quadratic normalization for general countable unequal carriers. It does not classify those carriers as finite or prove INDEPENDENT finite forcing. No historical novelty or formal verification is claimed.

## 1. Main conclusions and source scope

Let `d_n(W)` be the no-merger probability of n current opaque roots through one actual natural INDEPENDENT private word W. All cells have their original, shared arm and coin parameters; no arity-specific fit is made. For every n>=3,

    d_n(W) >= d_3(W)^[65 binom(n,2)].                         (1)

The estimate is uniform in the number of factors, arbitrary unequal finite positive arm durations, and all interior coins. It also holds for compatible source-closure kernels at every declared cap. The exponent is deliberately nonoptimal. Its relevant feature is quadratic rather than quartic growth in n.

A more local estimate supplies (1). Put `c0=1-exp(-1)` and let B be a single cell. If `delta=1-d_2(B)<=c0/16`, then at **every** n>=2,

    0 <= -log d_n(B) <= (4/c0) binom(n,2) delta.              (2)

This bound includes arbitrarily long rare arms. Consequently, for a countable chronological carrier of arbitrary unequal closed cells with finite total triple hazard, one may pass the n-to-infinity quadratic decay limit through the entire product. Section 5 states the resulting exact resource identity against a fixed finite strict target.

Closed parameters below are auxiliary limits of actual sources, not admitted rivals. Infinite arm duration means survival zero only in this compactification. No COMMON observation or bound on total physical arm duration is assumed.

## 2. Completed prior results reused

The accepted [three-lineage survival provider](../../../2026-10-04-dot-g3-new-reconstructions-1835z/THREE-LINEAGE-RECONSTRUCTION-R1.md) proves

    d_n(W) >= d_3(W)^[6 lambda_n²+lambda_n],
    lambda_n=binom(n,2).

Its elementary bare-cell lower bound `2*6^(-lambda_n)d_3^lambda_n` is reused below. The provider is pinned at SHA256 `b76a73adcbc1f52f855ff633571452f4f1a992f1e0e28b3dc59a26e82b6b083c`. That provider, the accepted G6 weak-cell TV bound, and the source's projectivity/composition are not new results of this note. The [fresh independent review](../../../2026-10-04-dot-g3-new-reconstructions-1835z/WEAK-AND-SURVIVAL-R1-INDEPENDENT-REVIEW.md), SHA256 `c42d23e4473eff9f540f8ac41115f2539794a95bf6fab8d64a1d9a6b03474e29`, accepts their source contracts. The change here is the arity-uniform weak-pair estimate (2), yielding the exponent in (1).

The complete general unequal-arm pair-hazard compactification already appears in [ORDERED-CLOSURE-RECONSTRUCTION-R1.md](../../../2026-10-04-dot-g3-new-reconstructions-1835z/ORDERED-CLOSURE-RECONSTRUCTION-R1.md), SHA256 `fe478d5bd68471a39e6cfa39d91a1e152d3196e0f2f9e6e895ab3906fee66eb8`, with [independent review](../../../2026-10-04-dot-g3-new-reconstructions-1835z/SECOND-ORDER-AND-CLOSURE-R1-INDEPENDENT-REVIEW.md), SHA256 `b1e827ccce036dbeadc50f7d3cda347929d688a685185ee2bcbb6015c0bc72cc`. It allows countably many closed-parameter cells on a chronological pair-hazard interval, plus an ordinary complement. The proof selects source parameters and interval positions; applying that same selection once before choosing a cap gives one compatible carrier for an all-cap convergent array. No new compactification construction is claimed here.

The finite-unequal/countable-equal phase problem is also completed already: [UNIFORM-LAPLACE-PHASE-REMOVAL.md](../continuation-2110z/UNIFORM-LAPLACE-PHASE-REMOVAL.md), SHA256 `14dc61fa433ed9ecb5307b93fbdf40dabc870f39a2324263a4c57cfa7cfe9fc8`, handles all real finite arm balances and resonances under its displayed scalar premise. That theorem is not a theorem about countably many unequal factors. The latter distinction is the remaining persistence problem addressed only partially here.

## 3. Uniform weak-pair bound, including long rare arms

Write the cell arm durations as a,b in `[0,infinity]`, with routing weights g and q=1-g. The no-merger formula is

    d_n=E exp[-a lambda_K-b lambda_(n-K)],
    K~Bin(n,g),
    delta=g²(1-exp(-a))+q²(1-exp(-b)).                       (3)

At zero arm survival, terms with zero pair count retain value one, as in the continuous polynomial source kernel. Assume `delta<=c0/16`.

**Both arms at most one.** For `0<=t<=1`, concavity gives `1-exp(-t)>=c0 t`. Jensen's inequality and `E lambda_K=lambda_n g²` give

    d_n >= exp[-lambda_n(g² a+q² b)]
        >= exp[-lambda_n delta/c0].                         (4)

**One arm larger than one.** Exchange the two arms if needed so a>1. From (3), `g²<=delta/c0<=1/16`; hence `g<=1/4` and `q>=3/4`. Both arms cannot exceed one, since that would give `delta>c0(g²+q²)>=c0/2`. Therefore b<=1 and

    b <= delta/(c0 q²) <=16 delta/(9c0).                     (5)

Restrict to routing outcomes with at most one root on arm a. No merger is possible on that arm, even if its duration is infinite. Arm b carries at most n roots, so

    d_n >= exp(-b lambda_n) P_n,
    P_n=Pr(K<=1)=q^(n-1)[1+(n-1)g].                        (6)

The elementary inequalities

    -log(1-g) <= g+g²/(2q),
    log(1+x) >= x-x²/2                 for x>=0

give

    -log P_n
       <= g²[(n-1)/q+(n-1)²]/2
       <= lambda_n g²/q
       <=4 lambda_n delta/(3c0).                           (7)

The first logarithm bound follows by integrating `t/(1-t)<=t/q` over `[0,g]`; the second follows by differentiating its difference. These inequalities do not require `(n-1)g` to be small. Thus (5)–(7) yield

    -log d_n <= [28/(9c0)] lambda_n delta
              <=(4/c0) lambda_n delta.

Together with (4), this proves (2) for every n at once. If delta=0 the same argument, or pair projectivity, gives the identity kernel. Endpoint coins are covered by continuity or by their ordinary surviving arm. No finite upper bound on the larger arm has entered the proof.

## 4. Global quadratic three-lineage control

For clarity the inherited bare lower bound is recalled in three steps. Let x=exp(-a), y=exp(-b), `A=g²x`, `C=q²y`. For n>=3, all-on-one-arm routing and `2lambda_n>=n` imply

    d_n >= A^lambda_n+C^lambda_n.

The exact triple formula gives `d_3<=3(A+C)`. Convexity therefore gives

    d_n >=2*6^(-lambda_n)d_3^lambda_n.                      (8)

Set `delta0=c0/16`, and first assume `0<d_3<1`.

If `1-d_3<=delta0`, projectivity gives `1-d_2<=1-d_3`; (2), `c0>1/2`, and `1-d_3<=-log d_3` imply

    -log d_n <=8lambda_n(-log d_3),

which is stronger than (1).

If `1-d_3>=delta0`, then `delta0>1/32`, so

    d_3^64 <=(1-delta0)^64 <=exp(-64delta0)
             <exp(-2)<1/6.

Raising this to lambda_n and combining with (8) proves (1). At d_3=0 the inequality is immediate; at d_3=1 projectivity and the pair union bound give d_n=1. Hence the bare-cell theorem holds throughout the closed parameter cube.

Ordinary factors also satisfy (1), since their diagonals are `exp(-t lambda_n)` and `d_3=exp(-3t)`. Multiplication of no-merger coordinates proves (1) for every finite word in its actual order. Continuity proves it in every declared finite-cap closure. Nothing in this argument changes the parameter tuple or replaces full-source composition by an external mixture.

A legal-observation consequence uses the inherited bridge event: if an actually supplied positive rooted-topology event of probability p forbids any merger among three specified descendants before their outside anchor joins, then `p<=d_3` for that same private slot. Consequently

    d_n >= p^[65 binom(n,2)]

at every higher declared arity of the compatible source. An arbitrary coarsening or unsupplied event does not furnish this premise. This is a quantitative survival floor, not a source-size bound.

## 5. Exact quadratic normalization of an arbitrary countable unequal carrier

Consider one compatible chronological carrier with ordinary complement A>=0 and a finite or countable collection of closed cells B_i, such that

    D_n=exp(-A lambda_n) product_i d_n(B_i),
    D_3>0.                                                 (9)

The inherited countable presentation gives (9) by finite chronological truncation. Its positivity criterion implies every retained `d_3(B_i)>0` and

    sum_i xi_i<infinity,      xi_i=-log d_3(B_i),
    -log D_3=3A+sum_i xi_i.                                (10)

Equation (1) now provides the summable bound, uniform in n>=3,

    0 <= [-log d_n(B_i)]/n² <=(65/2) xi_i.                  (11)

For each fixed closed nonsingular cell define

    gamma_i=lim_(n->infinity) [-log d_n(B_i)]/n².

This limit exists and is explicit:

- For an interior coin and two finite positive durations a,b, the inherited strict saddle calculation gives `gamma=ab/[2(a+b)]`.
- For an interior coin and at least one zero duration, gamma=0. The all-on-that-zero-arm route has probability equal to a fixed positive coin power, giving a linear-in-n logarithmic upper bound.
- For an interior coin, one infinite duration and the other finite positive duration b, gamma=b/2. Only zero or one root may enter the infinite arm without merger. The exact remaining sum is `q^n exp(-b lambda_n)+n g q^(n-1)exp(-b lambda_(n-1))`, whose quadratic rate is b/2. If b=0 the preceding zero-arm case gives zero.
- At an endpoint coin the factor is the ordinary evolution on its used arm, giving half that arm's finite duration; the unused arm is irrelevant. A used infinite arm would have d_3=0 and is excluded by (10). Both infinite arms at an interior coin are likewise excluded.

These cases exhaust the closed parameter cube with d_3>0. They describe auxiliary limit factors only. Dominated convergence using (11) proves

    sum_i gamma_i<infinity,
    lim_(n->infinity) [-log D_n]/n²
        =A/2+sum_i gamma_i.                                (12)

In particular, if this carrier has the complete endpoint law, or just every diagonal, of a fixed finite strict private target with total ordinary duration A_T and cells `(a_l,b_l,g_l)`, then

    A/2+sum_i gamma_i
        =A_T/2+sum_l a_l b_l/[2(a_l+b_l)].                  (13)

No bound on total physical arm exposure, summable logit squares, rational balance, nonresonance, or finite number of unequal factors is used. This proves the general quadratic resource match rather than assuming an interchange of an infinite sum with saddle asymptotics.

## 6. Precise remaining persistence obligation

Equation (13) alone allows countably many positive contributions of summable size and allows nonordinary zero-quadratic-rate boundary cells. It does not force finitely many persistent jumps, identify a target chronological body, or remove boundary arms. The next linear and logarithmic residual analysis is not automatically dominated by (11). In particular it does not supply the square-summable equal-family bias budget or common meromorphic interpolation needed by the accepted Laplace theorem.

The all-law INDEPENDENT-to-COMMON result for **finite strict original sources** cannot be applied to this countable closed carrier without an extension theorem. The carrier is an analysis object, not an admitted alternative source. Nor does its existence preserve a moving strict later-law discrepancy in an exact-prefix rival array.

The master obligation discharged here is therefore the previously unjustified **quadratic normalization step for arbitrary unequal countable persistence**, plus an improved source-positive all-arity survival bound. General finite persistence, the weak-reservoir chronology equality, a finite legal INDEPENDENT certificate, and a fixed-target full-prefix impossibility construction remain open.

Verification: direct hand inequalities and dominated convergence, with completed source suppliers reused and attributed. No new primary-paper claim, numerical search, source compiler, symbolic calculation, QE, Lean or Rust verification is asserted.
