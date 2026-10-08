# The biased source has a genuine order-nine transverse coefficient

Contributor: dot (OpenAI), 8 October 2026, 12:14 UTC.

Status: HAND CANDIDATE FOR INDEPENDENT REVIEW. This is a separate calculation after the accepted source-only interior-base addendum. Neither frozen predecessor is edited or upgraded by this candidate. No compiler, numerical or symbolic source execution, parameter scan, or publication was used.

## 1. Statement on the actual source chart

Use the same actual natural INDEPENDENT bare cell and durations as the accepted interior-base addendum:

    a in (0,1), b=1-a,
    x=epsilon^2 h/a-epsilon^3 u/a^2+epsilon^4 v/a^3,
    y=epsilon^2 h/b+epsilon^3 u/b^2+epsilon^4 v/b^3,
    g=a+epsilon*w,
    zeta=wh-u, alpha=h^3-3zeta^2/(ab), kappa=5/3.

Here h>0, and x,y are durations. Compact-interior parameter sets have a bounded away from 0 and 1, h bounded below, and h,u,v,w bounded. Every sufficiently small positive-epsilon source is then strict, uniformly on such a set. The same parameters are used at every arity. The bare chart has no padding requirement; using it in the original padded chart retains that chart's h+r<4 condition.

In the accepted 9/7/6/4 source representation, write

    C=E_(-h epsilon^2)B,
    L=U(C)+kappa X(C),
    M=T(C)-kappa X(C).

The ordinary inverse is proof normalization only. The assertion is

    L=P epsilon^9+O(epsilon^10),
    M=-2P epsilon^9+O(epsilon^10),                         (1)
    P=(b-a) zeta/(ab) * [zeta^2/(ab)-h^3].

All errors and coefficient extractions below are jointly analytic and uniform on the stated compact sets. Fair base a=1/2 gives P=0, as required by the previously accepted even parity. For every FIXED biased base a!=1/2, the limiting normalized two-coordinate map

    (h,zeta) -> (alpha/15,P)                               (2)

has rank two everywhere h>0. This already holds with w=0, so every actual coin may remain exactly a.

This is rank of the full nominal source chart. No rank, sign richness or common zero is asserted on the exact complete lower-response/ordinary-diagonal fibre. The positive leading ratio kappa and the leading chronological energy kernel are unchanged.

## 2. First imbalance derivative of the actual partition correction

Let eta=1-g, s=gx, t=eta*y, and put

    mu=g*s+eta*t,
    delta=s-t,
    sigma2=g*eta*delta^2,
    mu3=g*eta*(eta-g)*delta^3.

Thus s=mu+eta*delta and t=mu-g*delta. In this chart mu=h epsilon^2+O(epsilon^4), delta=zeta epsilon^3/(ab)+O(epsilon^4). The accepted absence of an epsilon^3 term in mu will be needed in Section 4.

For one specified output partition with block sizes s_i, write d_i=s_i-1, d=sum d_i, R=number of blocks, and

    K=product_i(s_i!)/2^d.

The ordinary holding-time expansion in the accepted proof gives a degree-d leading term and a degree-(d+1) correction. Assign each complete output block independently to arm A with Bernoulli(g) indicator I_i. Set d_A=sum d_i I_i, and use the complementary assignment on arm B. The two homogeneous source terms are exactly

    K E[s^d_A t^(d-d_A)],
    -K E[s^d_A t^(d-d_A) ((s/g)R_A+(t/eta)R_B)],            (3)

where R_A and R_B are the ordinary rate-average polynomials, not root counts. From the finite holding-time formula,

    R_A=sum_i A_i I_i+sum_(i<j) B_ij I_i I_j,
    A_i=(d_i^2+2d_i)/6,
    B_ij=1+(d_i+d_j)/2+d_i*d_j/3,                          (4)

and R_B replaces I_i by 1-I_i. This also handles an empty arm. Equation (3) follows from the actual routing probability g^(N_A)eta^(N_B): after extracting the arm-duration factors it becomes the product Bernoulli block assignment, with no formal mixture operation on words.

At fixed g and mu, expansion in delta gives the degree-(d+1) correction

    -K [C_shape mu^(d+1)+D_shape mu^d delta
                    +O(mu^(d-1)delta^2)],                (5)

where C_shape is the previously accepted balanced constant and

    D_shape=(eta-g) sum_i d_i(d_i+1)(d_i+2)/6.              (6)

Here and below O in homogeneous polynomials means the remaining terms have at least the indicated number of delta factors; the subsequent epsilon substitution supplies the actual analytic bounds.

To verify (6) directly, differentiate the expectation in (3). Since

    partial_delta[s^d_A t^(d-d_A)] at delta=0
        =mu^(d-1)(d_A-gd),

its coefficient divided by mu^d is

    E[(d_A-gd)(R_A/g+R_B/eta)]
       +E[(eta/g)R_A-(g/eta)R_B].                         (7)

Put A_d=sum d_i A_i, A_1=sum A_i, and
B_d=sum_(i<j)(d_i+d_j)B_ij. Independence gives

    Cov(d_A,R_A)=g*eta*(A_d+g B_d),
    Cov(d_A,R_B)=-g*eta*(A_d+eta B_d).

The first expectation in (7) is therefore (eta-g)A_d. The second is (eta-g)A_1: the pair terms cancel once again. Adding gives (eta-g)sum(d_i+1)A_i, which is (6).

This derivative is at fixed current g. Substituting g=a+epsilon*w afterward includes every varying-coin effect; it is not an assumption that the physical coin is fixed while epsilon changes.

## 3. Homogeneous source identities through weighted order nine

Keep the accepted definitions

    A_n=3p_n(2,2,1^(n-4))-2p_n(3,1^(n-3)),
    f=d9=A9/15, H=d6=A6/9,
    e=[2p7(3,2,1,1)-p7(4,1,1,1)]/6,
    U(B)=-H+2e, X(B)=Y(B)=f, T(B)=H, V(B)=0.

Write theta=eta-g. Formula (6) gives D_shape/theta equal to

    (2,2): 2;   (3): 4;
    (4): 10;    (3,2): 5;    (2,2,2): 3.                 (8)

The exact degree-two part of A_n is -3sigma2. The balanced degree-three part is mu^3. Combining (5) for (2,2) and (3), with their leading K values 1 and 3/2, gives its linear-imbalance correction +6theta*mu^2*delta. Thus, for each fixed n in use,

    A_n=-3sigma2+mu^3+6theta*mu^2*delta+O(epsilon^8).        (9)

The error includes the remaining degree-three terms with at least delta^2, and all homogeneous terms of degree at least four. Their lowest epsilon orders are eight.

For the root-drop-three shapes, the exact leading terms remain

    P4=3 M4, P32=(3/2)M3 M2, P222=M2^3,
    M_j=g*s^(j-1)+eta*t^(j-1).

The accepted projectivity identity

    A_n-A_(n-1)=2(n-7)P32+2P4-3(n-5)P222

has degree-three part 3[(n-1)mu*sigma2+2mu3]. Its balanced degree-four part is -(n-1)mu^4. By (8), the degree-four coefficient linear in delta is

    theta*mu^3*delta[-15(n-7)-60+9(n-5)]
        =-6n*theta*mu^3*delta.

Summing n=7,8,9 proves

    A9-A6=63mu*sigma2+18mu3-21mu^4
                 -144theta*mu^3*delta+O(epsilon^10).       (10)

Similarly the exact degree-three part of e is -mu*sigma2-mu3/2. Its balanced degree-four part is mu^4/3. Its first imbalance coefficient is

    [2*(-(3/2)*5)-(-3*10)]/6=5/2,

so

    e=-mu*sigma2-mu3/2+mu^4/3
                 +(5/2)theta*mu^3*delta+O(epsilon^10).     (11)

For (10)-(11), the unretained degree-four terms have at least delta^2 and hence order at least ten; all degree-five or higher terms also start at ten. All central-moment terms in the leading degree-three polynomials were retained exactly. Thus the errors do not rely on fair parity.

The bare transverse combinations are consequently

    U(B)+kappa*f
       =5mu*sigma2+mu3-(5/3)mu^4
                       -11theta*mu^3*delta+O(epsilon^10),  (12)
    H-kappa*f
       =-7mu*sigma2-2mu3+(7/3)mu^4
                       +16theta*mu^3*delta+O(epsilon^10).  (13)

These statements use one actual cell's full source coefficients, not independently assigned entries of the triangular representation.

## 4. Nominal normalization and the remaining skew term

Put tau=h epsilon^2. The exact row scaling is

    X(C)=Y(C)=exp(36tau)f,
    U(C)=exp(21tau)(-H+2e),
    T(C)=exp(15tau)H.

Both bare combinations (12)-(13) begin at order eight. Therefore multiplying either by its row exponential changes it only at order ten. The two normalization corrections through order nine are respectively +25tau*f and -35tau*f. From (9) and tau=mu+O(epsilon^4),

    25tau*f=-5mu*sigma2+(5/3)mu^4
                          +10theta*mu^3*delta+O(epsilon^10),
    -35tau*f=7mu*sigma2-(7/3)mu^4
                          -14theta*mu^3*delta+O(epsilon^10).

The replacement of tau by mu introduces only order-ten error because A9 starts at order six. Combining with (12)-(13) gives

    L=mu3-theta*mu^3*delta+O(epsilon^10),
    M=-2mu3+2theta*mu^3*delta+O(epsilon^10).                (14)

Finally mu3=g*eta*theta*delta^3, while

    mu=h epsilon^2+O(epsilon^4),
    delta=zeta epsilon^3/(ab)+O(epsilon^4),
    g*eta=ab+O(epsilon), theta=b-a+O(epsilon).

Taking the order-nine coefficient in (14) yields exactly (1). Neither v nor the higher corrections to delta, mu or g survive at this order. The varying-coin parameter w enters through zeta=wh-u.

## 5. A rank-two single-cell normalized image

For fixed a!=1/2 set k=(b-a)/(ab). Then

    P=k*zeta*(zeta^2/(ab)-h^3),

and direct differentiation gives

    det partial_(h,zeta)(alpha/15,P)
        =-k*h^2/5 * [h^3+3zeta^2/(ab)].                   (15)

This is nonzero for every h>0. In the fixed-coin subfamily w=0, zeta=-u, so these are genuine independent changes of the two actual arm-duration parameters h,u. They preserve strictness at sufficiently small epsilon. One may choose h+r<4 as well if a surrounding padded chart is desired; the common weight-15 right-padding multiplier does not change the leading coefficients in (2).

The rescaled map

    (h,u) -> (epsilon^-6 X(C),epsilon^-9 L)

extends jointly analytically to epsilon=0, where it is (2), up to zeta=-u. Its determinant is therefore nonzero at each fixed h>0, u for sufficiently small positive epsilon. This is a statement about the normalized parameterized chart. The normalization depends on its nominal source parameter h; it is not a fixed physical inverse added to the source.

The rank is not claimed on an ordinary-diagonal or complete lower-response fibre. In particular, a rank-two chart at nonzero response does not prove that the zero response is attained, lies in the interior, or admits an all-cap fixed-budget realization. Leading X/U coupling and the alternative Y/T bracket at order twelve remain as in the accepted predecessors.

## 6. Source pins and exact scope of reuse

The six immutable source providers are exactly those in the unchanged `SOURCE-PINS.json`, SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. In particular the actual EPPF/grafting and 9/7/6/4 representation, not a formal positive-kernel replacement, supply (3) and the append identities.

Predecessors used here:

- Frozen fair source proof SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, independently reviewed at frozen review SHA-256 `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`. Its separately mapped public editorial proof derivative has SHA-256 `92e8d834104ecc1127140836e90699c75e28440bc913a981749baf98bb4e955c`, with public review derivative `607dc63f08e8aa022f59ceebabdbd9c2f36daeda05132d2c0e1322e4adf53473`, at commit `df871563c361f8a225f9631984a0e35caa381d1c`, path `research/2026-10-08-dot-g4-weight15-source-jets-1157z/ACTUAL-WEIGHT15-JETS-AND-WEIGHT30-BRACKET-CANDIDATE.md`. That packet preserves the exact original/public mapping and unchanged mathematical content.
- Interior-base source-only addendum SHA-256 `81de27ab78b4bf8b8889d2b8a7005194264b831396a50ac0d71076899ac660b6`, independently reviewed at `f659f795f963fc9c923f6427e06bb52d905dd8be211582f72387212f03c82f83`. That earlier acceptance proves only the O(epsilon^9) transverse bound; it does not accept the coefficient or rank calculated here.

The new hand calculation is the first imbalance derivative (6), its exact source combination through order nine, and the determinant (15). Historical novelty is unassessed. This packet does not prove an energy inequality, a new no-return or word-count-uniform hazard theorem, full-fibre centering, all-cap control, or original G4. Those remain separate mathematical obligations.
