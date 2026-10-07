# All-nine finite error assembly and a larger sufficient mean-separation scale

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. **HAND assembly candidate; independent review pending.** No arithmetic job, numerical scan, provider call, observation replay, new data, sampling, inverse run or compiler occurred. Metadata/hash checks concern preservation only.

The original full-target practical problem remains OPEN: useful inference over the unchanged nine-parameter D, with every exported normalized physical width at most 1/20 and valid confidence under the original locus law. The candidate below gives a deterministic uniform sufficient separation scale 2^-80, improving the accepted 2^-512 baseline if the assembly is accepted. Its precision remains unusable as a practical sampling prescription; no completed practical solver follows.

## Source, components and review boundary

Keep D and the original nine shifted Bernoulli means F=(AC1,AC2,CC1,BC1,BC2,AB1,AB2,AA1,BB1). h,u,v are in [1/32,1/8], each of five rates is in [1/2,6], and g is in [1/6,2/3]. Sites share ONE genealogy in a complete locus; locus independence and actual data admission are separate statistical obligations. Put A=h+u, T=h+u+v, R=rR, d=rAB and c=8/3. Delta means source0 minus source1 for ANY two coherent original endpoints.

This assembly uses the frozen original [pair source](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`, and the following separately captured finite components:

| Component | Frozen HAND source SHA256 | Review at capture |
| --- | --- | --- |
| [Root T/R](../2026-10-07-cloud-practical-root-propagation-2018z/ROOT-ERROR-PROPAGATION.md) | `1cdd69096481bac024fd3914480b65754e31045d07dd7285f81971ed60d58726` | canonical scoped HAND acceptance |
| [CC1 rate](../2026-10-07-cloud-practical-cc1-propagation-1948z/CC1-ERROR-PROPAGATION.md) | `3c904f258325be33a5d4dd83b6ed381a9c139125838c6abcd7e76bb725de1534` | canonical scoped HAND acceptance |
| [h](../2026-10-07-cloud-practical-h-propagation-2027z/H-ERROR-PROPAGATION.md) | `196e6977111076a3c18f27b03bb11f3d776f7549f191c1428f06bcfbda17fd4e` | canonical scoped HAND acceptance |
| [g](../2026-10-07-cloud-practical-g-propagation-1932z/G-ERROR-PROPAGATION.md) | `701b40842036b41189a4eb16996b8dc6acb1ee273bde38d00a2b7928287c2704` | canonical scoped HAND acceptance |
| [Finite auxiliary A/d](../2026-10-07-cloud-practical-a-finite-comparison-2047z/A-FINITE-COMPARISON.md) | `58503d9581e546c3cab12b9712d837cbe179f1128bce9be7277493a1b819d67c` | scoped HAND acceptance message received; canonical review pending |
| [AA1 rate](../2026-10-07-cloud-practical-aa1-propagation-1921z/AA1-ERROR-PROPAGATION.md) | `15890972eba89e909790a3778582a4e794b96cc0503298e3e7df8c9cff258757` | canonical scoped HAND acceptance |
| [Tied-B rate](../2026-10-07-cloud-practical-bb1-propagation-2103z/BB1-ERROR-PROPAGATION.md) | `ba588603352c80dd9e809eb88ce364e4362f91e5a523b1cde888b8570964a995` | scoped HAND acceptance message received; canonical review pending |

Earlier original identifiability, positive-integral/profile and classical interval/contraction attribution remains in those sources. This assembly claims no new general inverse or concentration method. HAND acceptance does not imply execution or practical width success. The all-nine assembly itself requires separate review.

## A dependency-retaining finite candidate certificate

The following is a mathematical candidate certificate for two source endpoints, not implemented inverse code. Complete interval enclosures for all indicated actual-source quantities could turn it into a checked cell-pair certificate; absent such enclosures, no source can be discarded.

For raw root moments a_i=AC1_i, b_i=AC2_i and rho_i=b_i/a_i², define the signed root residuals from the root component

    E_R=Delta b−rho1*(a0+a1)*Delta a,
    E_Rmu=Delta mu_AC2−rho1*(a0+a1)*Delta mu_AC1,
    E_R=2*E_Rmu,
    Delta R=−K*E_R, 0<K<851,
    J_T=(1+c/R0)*Delta a+a1*c*K*E_R/(R0*R1).

Use bounds

    B_R=851*|E_R|,
    B_T=(9/8)*|J_T|,
    B_C=(377/3)*[|Delta mu_CC1|+|Delta mu_AC1|+(48/29)*B_T].

For y_k=mu_BCk−mu_ACk, Q_i=y_2i/y_1i and y_10>1/1650, keep the shared h contrast

    E_h=Delta y_2−Q1*Delta y_1,
    B_h=(9/4)*[|E_h|/y_10+(16/3)*B_T+(1/8)*B_C+(12/19)*B_R].

The g component retains its BC/AC/CC residual

    E_g=Delta mu_BC1−(1−g1)*Delta mu_AC1
              −g1*exp(rC0*h0)*Delta mu_CC1,
    B_g=275*[|E_g|+8*B_h+(1/4)*B_C].

Keep both exact AB/AC/g routing residuals

    E_k=Delta mu_ABk−g0*Delta mu_ACk
          +(g0−g1)*(mu_ABk1−mu_ACk1)/(1−g1), k=1,2.

The finite-A component aligns at T*=max(T0,T1), R*=R0. Its signed original-endpoint lifting identity is

    e_k*=E_k/(1−g0)+C_0k^T−C_1k^T−C_1k^R,

where the C quantities are its exact nuisance integrals. All auxiliary durations are proved to lie in [1/32,5/16]; every profile rate stays between the endpoint rates. For a scalar fallback bound e_k* by

    B_ek=|E_k|/(1−g0)+t_k*B_T+r_k*B_R,
    (t_1,t_2)=(44/19,88/35), (r_1,r_2)=(48/361,96/1225).

With L_A=5*2^14*3^6,

    B_A=L_A*(|e_2*|+2*|e_1*|),
    B_d=4608*(|e_1*|+3*B_A),
    B_a=135*[|Delta mu_AA1|+3*|E_1|+(7/4)*B_A].

One may replace |e_k*| by B_ek, losing signed cancellation but preserving inclusion. B_d bounds rAB; B_a bounds rA. The tied-B residual uses b1=rB1 and beta0=1−g0:

    E_B=Delta mu_BB1
       −beta0*exp(−b1*A0)*Delta mu_AB1
       −g0*exp(−b1*h0)*Delta mu_BC1
       −g0*beta0*(exp(−b1*h0)−exp(−b1*A0))*Delta mu_AC1,
    B_b=240*[|E_B|+(20/11)*B_A+(128/57)*B_h+(11/8)*B_g].

The original finite identity is Delta rB=(E_B−N_B)/D_B with D_B>1/240 and N_B its signed nuisance integral; retain E_B−N_B when certified. No separate downstream rate errors or A/B feedback occur.

Original durations MUST be recovered as Delta u=Delta A−Delta h and Delta v=Delta T−Delta A. Their signed enclosures may be smaller than the safe fallbacks B_u=B_A+B_h and B_v=B_T+B_A. A is not an original accuracy coordinate. The nine normalized bounds are

    M=max((32/3)*B_h, (32/3)*B_u, (32/3)*B_v,
           (2/11)*B_a, (2/11)*B_b, (2/11)*B_C,
           (2/11)*B_d, (2/11)*B_R, 2*B_g).      (1)

If a COMPLETE source-pair enclosure certifies M<1/20, that pair/set satisfies the original normalized target. Point values, nominal estimates or one local cell do not certify the entire inverse union. All comparison ranges and every cell-pair must be covered.

## An explicit uniform sufficient scale

Let epsilon=max_j |Delta mu_j| for the original nine SHIFTED means. The following conservative coefficient table follows from the same finite gates; it does not assume convexity of the mean image.

| Quantity | Uniform upper bound |
| --- | --- |
| abs(Delta R) | 2^14 epsilon |
| abs(Delta T) | 2^15 epsilon |
| abs(Delta rC) | 2^23 epsilon |
| abs(Delta h) | 2^22 epsilon |
| abs(Delta g) | 2^34 epsilon |
| each abs(E_k) | 2^33 epsilon |
| each abs(e_k*) | 2^35 epsilon |
| abs(Delta A) | 2^63 epsilon |
| abs(Delta rAB) | 2^78 epsilon |
| abs(Delta rA) | 2^72 epsilon |
| abs(Delta rB) | 2^73 epsilon |
| abs(Delta u) and abs(Delta v) | 2^64 epsilon |

Here is the explicit hand arithmetic behind the table, including source-dependent cancellations used before the coarse powers:

1. rho≤361/105<4 and a0+a1≤2 give |E_Rmu|≤9epsilon. Hence |Delta R|≤15318epsilon<2^14epsilon. The exact root relation gives |J_T|≤[38/3+(32/19)*2^14]epsilon. Since 38/3<13 and 32/19<7/4, B_T<(258165/8)epsilon<2^15epsilon.
2. 377/3<126 and 48/29<5/3 give B_C≤[210*2^15+252]epsilon=6881532epsilon<2^23epsilon.
3. 0<Q1<2 and |Delta y_k|≤2epsilon give |E_h|≤6epsilon. With y_10>1/1650, the bracket for B_h is at most [9900+6*2^15+2^20+2^14]epsilon. Multiplying by 9/4 gives 2860803epsilon<2^22epsilon.
4. rC0*h0≤3/4, exp(rC0*h0)<3 and g1≤2/3 give |E_g|≤4epsilon. Thus B_g≤275*[4+2^25+2^21]epsilon<275*9*2^22epsilon<2^34epsilon.
5. For BOTH k, the original two-stage positive integral gives 0≤(mu_ABk1−mu_ACk1)/(1−g1)≤d1*v1/2≤3/8. Consequently |E_k|≤[(5/3)+(3/8)*2^34]epsilon<2^33epsilon. The lifting denominator is at least 1/3, both t_k<3 and both r_k<1, so |e_k*|≤[3*2^33+3*2^15+2^14]epsilon<2^35epsilon.
6. L_A=5*2^14*3^6<2^26. Therefore B_A<2^26*3*2^35epsilon<2^63epsilon. With 4608<2^13 and 2^35+3*2^63<2^65, B_d<2^78epsilon. The AA1 bracket is less than 2^64epsilon and 135<2^8, giving B_a<2^72epsilon.
7. The three nonnegative mean-error weights in E_B sum to beta0²*exp(−b1*A0)+g0*(2−g0)*exp(−b1*h0)≤1. Thus |E_B|≤2epsilon. Using 20/11<2,128/57<3,11/8<2, its full bracket is less than 3*2^63epsilon; 240*3<2^10 gives B_b<2^73epsilon.
8. Original signed u/v differences give |Delta u|≤B_A+B_h<2^64epsilon and |Delta v|≤B_T+B_A<2^64epsilon.

All five rate coefficients are at most 2^78; original time normalization gives coefficient at most 2^69/3 and g gives at most 2^35. Both are smaller than the rate-normalized coefficient 2^79/11. Therefore the candidate uniform finite implication is

    rho(theta0,theta1)≤(2^79/11)*epsilon,
    epsilon≤2^−80  ⇒  rho(theta0,theta1)≤1/22<1/20. (2)

The equality case at the sufficient mean threshold is included. This is a global finite-source implication assembled from the explicitly valid paths, not an inference from pointwise nonsingularity.

## Compare the old certificate without claiming practical closure

The [accepted baseline](../2026-10-07-dot-explicit-fixed-pulse-separation-0847z/EXPLICIT-CONSERVATIVE-DELTA.md) and its [independent review](../2026-10-07-dot-explicit-fixed-pulse-separation-0847z/INDEPENDENT-EXPLICIT-DELTA-REVIEW.md) already established the SAME source implication at Delta_old=2^-512. Therefore another mere existence statement would add no source precision. If accepted, (2) permits Delta_new=2^-80, a factor 2^432 larger. The old baseline stays valid and is not superseded as accepted evidence by this pending assembly.

Delta_new has an 81-bit denominator, so that scalar alone fits the recorded 256-bit rational-input limit; this does not establish the runtime/width of any receiver computation. The inherited conservative confidence-cloud budget factor 32/Delta² changes from 32*2^1024 to 32*2^160, a factor 2^864 reduction, before its same logarithm. Both remain far beyond practical locus budgets. This is comparison of sufficient bounds only, not a necessary sample lower bound, improved executed performance or authorization for sampling/cap changes. The original near-collision and accepted specific-method failure bounds remain intact.

## Exact missing admission, precision and exported-cover implication

The deterministic candidate difference set is B80=[−2^-80,2^-80]^9. To turn it into confidence with original normalized widths, a prospectively admitted original-source mean region C must contain the true F with its stated coverage and satisfy C−C⊂B80. This means coordinate DIAMETER at most 2^-80, not radius; a centered marginal box with radius 2^-81 meets the diameter condition only after its JOINT coverage is valid. The locus law and selected feature identities must be admitted, with within-locus dependence preserved. No such useful admitted inputs are supplied here.

For S={theta in D:F(theta) in C}, (2) then bounds every exact candidate pair by 1/22 on that admitted event. A complete numerical outer cover S_out must still contain every compatible source and export all nine original normalized union widths at most 1/20. A proof that S is small does not show the currently saved broad outer cover is small; source-box/mean enclosures, all cells, between-cell pairs and inflation require actual checking. The margin 1/20−1/22=1/220 is only available mathematical slack, not executed cover performance.

Neither archived 1024-locus retained-pair region is newly certified; their accepted particular-method width obstruction and historical admission debt remain. No data generation, prospective run, retrospective confidence, completed inverse/cover, useful sample guarantee or Lean verification occurs in this packet. Next obligation: scoped independent assembly review, then useful dependency-preserving precision/cover binding under the original admitted source, rather than treating (2) alone as practical endpoint closure.
