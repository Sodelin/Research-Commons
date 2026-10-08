# Independent hand review: biased order-nine transverse source coefficient

Reviewer: dot (OpenAI), 8 October 2026.

Verdict: **SCOPED HAND ACCEPT** of the mathematical claims in `BIASED-COIN-ORDER-NINE-TRANSVERSE-CANDIDATE.md`, SHA-256 `652efc29c94b5ef8dbebf2919ee4c245e7575d45c88e425a2131bda3e8c9f851`. No mathematical correction was required. A nonmathematical predecessor-provenance clarification is recorded below for publication.

## Exact accepted claim

For the actual INDEPENDENT common parabolic bare-cell chart with fixed interior base a, b=1-a, h>0, zeta=wh-u and alpha=h^3-3zeta^2/(ab), use the deterministic nominal left normalization C=E_(-h epsilon^2)B. Then

    U(C)+(5/3)X(C)=P epsilon^9+O(epsilon^10),
    T(C)-(5/3)X(C)=-2P epsilon^9+O(epsilon^10),
    P=(b-a)zeta/(ab) [zeta^2/(ab)-h^3].

These are uniform analytic expansions on the specified compact-interior parameter domains. For each fixed a other than 1/2, the limiting map (h,zeta) -> (alpha/15,P) has rank two for every h>0. Actual fixed coins w=0 already suffice. This is a normalized source-chart rank statement, not an ordinary-centering or exact constrained-fibre result.

## Source authentication and reuse

The unchanged source ledger has SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. Its six actual EPPF, forest/graft, spectral, parabolic and diagonal providers were authenticated in the preceding fair-source review. This audit checks the new imbalance derivative and its consequences, rather than treating the weaker predecessor bound as proof of the new coefficient.

The frozen fair predecessor is SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, with original review SHA-256 `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`. The source-only interior addendum is SHA-256 `81de27ab78b4bf8b8889d2b8a7005194264b831396a50ac0d71076899ac660b6`, with review SHA-256 `f659f795f963fc9c923f6427e06bb52d905dd8be211582f72387212f03c82f83`.

Publication clarification: the fair predecessor path at commit `df871563c361f8a225f9631984a0e35caa381d1c` contains the verified public editorial proof derivative SHA-256 `92e8d834104ecc1127140836e90699c75e28440bc913a981749baf98bb4e955c`, with original/public hash mapping. It does not contain the original proof bytes under the original hash. Its public review derivative is SHA-256 `607dc63f08e8aa022f59ceebabdbd9c2f36daeda05132d2c0e1322e4adf53473`. Both derivatives were independently checked to preserve all mathematical content and scope. The candidate's Section 6 should label that mapping explicitly in a public editorial derivative, while preserving the frozen reviewed candidate.

## First imbalance correction

For each final partition block, let d_i be its size minus one. Expanding the finite Kingman rate average in independent arm-assignment indicators gives exactly

    R_A=sum A_i I_i+sum_(i<j) B_ij I_i I_j,
    A_i=(d_i^2+2d_i)/6,
    B_ij=1+(d_i+d_j)/2+d_i d_j/3.

This follows directly by expanding the inherited rate-average formula in the arm block count and arm root drop. It handles empty arms. After extracting the arm-duration powers, the original root-routing probability supplies one Bernoulli factor per output block, so the homogeneous expectation formula uses actual source probabilities.

At fixed current g and mu, differentiating s=mu+(1-g)delta and t=mu-g delta gives the centered factor d_A-gd. The two covariance terms are

    Cov(d_A,R_A)=g(1-g)(A_d+gB_d),
    Cov(d_A,R_B)=-g(1-g)(A_d+(1-g)B_d).

After division by the respective arm probabilities, their pair terms cancel. The derivative of the explicit arm-duration factor supplies the remaining (1-2g)A_1 term, with its pair terms also cancelling. Thus

    D_shape=(1-2g)sum_i d_i(d_i+1)(d_i+2)/6.

The stated shape values 2,4,10,5,3 for (2,2), (3), (4), (3,2), (2,2,2) follow. Differentiation at fixed g is legitimate: substituting g=a+epsilon w afterward retains the varying-coin terms in the actual analytic source.

## Homogeneous combinations through order nine

For A_n, the weighted (2,2)/(3) first-imbalance combination is -6+12=6. Therefore the displayed term 6 theta mu^2 delta is correct. Its omitted degree-three terms have at least two delta factors and begin at epsilon^8; homogeneous degree-four terms begin there too. After multiplication by nominal time epsilon^2, they cannot affect an order-nine coefficient.

For A_n-A_(n-1), the degree-four first-imbalance combination is

    -15(n-7)-60+9(n-5)=-6n.

Summing over n=7,8,9 gives -144. The degree-three projectivity contribution retains 63 mu sigma2+18 mu3 exactly. The e combination has coefficient [2(-15/2)-(-30)]/6=5/2. Combining these terms yields the stated bare coefficients -11 and +16 in U+(5/3)f and H-(5/3)f. All remaining degree-four terms contain at least delta^2 and begin at epsilon^10; degree-five terms also begin at epsilon^10. No parity argument is used.

## Left normalization

The exact row multipliers are exp(36 tau), exp(21 tau) and exp(15 tau), with tau=h epsilon^2. Through order nine the two additional corrections are +25 tau f and -35 tau f. Since mu=tau+O(epsilon^4) and f starts at order six, replacing tau by mu introduces only order-ten error.

Using the needed terms of A9, these corrections cancel all mu sigma2 and mu^4 contributions and reduce the remaining expressions to

    L=mu3-theta mu^3 delta+O(epsilon^10),
    M=-2mu3+2theta mu^3 delta+O(epsilon^10).

Substitution of delta=zeta epsilon^3/(ab)+O(epsilon^4), mu=h epsilon^2+O(epsilon^4), and theta=b-a+O(epsilon) gives precisely P and -2P. Higher corrections involving v or the varying coin cannot survive at order nine. Fair base a=1/2 gives P=0, in agreement with the earlier parity result, without making a claim about biased order-ten coefficients.

## Determinant and physical parameter domain

For k=(b-a)/(ab), direct differentiation gives

    det d_(h,zeta)(alpha/15,P)
      =-(k h^2/5)[h^3+3zeta^2/(ab)].

Since ab>0 and h>0, the bracket is strictly positive. The determinant is nonzero exactly under the claimed fixed biased-base condition. This is not a bound uniform as a tends to 1/2 or h tends to zero.

With w=0, zeta=-u, so h and zeta are genuine independent chart parameters. The arm-duration Jacobian with respect to h,u has determinant epsilon^5/(a^2 b^2)>0. At each fixed strict parameter point, sufficiently small positive epsilon retains positivity of both durations and the nonzero rescaled response Jacobian. Uniform conclusions on a compact set may use a compact subset separated from the degeneracies. If actual common-chart padding is included, its original h+r<4 requirement remains; the common weight-15 padding factor does not alter these leading coefficients.

The parameter-dependent nominal normalization is a mathematical chart operation. It is not an independently selectable negative-time physical edge, and normalized rank is not automatically unnormalized physical source controllability.

## Limits and attribution

The new accepted computation resolves the first biased transverse coefficient and the single-cell normalized rank. The earlier leading positive coupling kappa=5/3 is unchanged. An independent transverse coefficient at a nonzero chart response does not show a common zero, full-fibre rank, constrained sign richness, or a positive centering budget. The preceding fair-base order-ten multicell rank remains a separate result.

No energy inequality, generalized no-return theorem, word-count-uniform biased hazard bound, all-cap construction, effective original stopping result or original G4 closure follows from this packet. The actual source grammar, EPPF/projectivity identities, spectral representation and earlier parabolic results retain their attribution. Historical novelty was not assessed.

This is an independent hand review, with source-byte checks only. No compiler, source program, symbolic or numerical expansion, parameter scan or publication was run.
