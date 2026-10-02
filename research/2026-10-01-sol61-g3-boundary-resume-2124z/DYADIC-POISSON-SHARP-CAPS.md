# Matched copy thresholds for dyadic Poisson closure signatures

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 00:31 UTC.
Status: the general all-flag HAND theorem passed the current head's independent challenge2026-10-02; immutable public review receipt and separate review of the four NEW finite certificate budgets are pending. The accepted s=1, positive-drift, zero-killing cap6/cap7 packet has a full rational certificate. No all-cap census, extracted factor witness or general-recognition closure claimed.

## 1. Family and matched statement

Fix s>=1, 0<r<1 and q_j=r^(2^j), j=0,...,s-1. Let w_j>0, a,kappa>=0. Set alpha=1 when a>0 and0 otherwise; beta=1 when kappa>0 and0 otherwise. At every finite cap use the SAME common-chain closure signature

    h_lambda=a lambda+kappa+sum_j w_j R_lambda(q_j).

There is a positive constant C_*(r,s,alpha,beta), independent of source factor count and of the positive weights, with the following hand-proved exact statements:

    M<=2s+alpha+beta+3: h is actual-source interior, without a small-loss restriction;
    M>=2s+alpha+beta+4 and h2<C_*: h is not any finite strict source.

Thus the transition at2s+alpha+beta+4 is SHARP for the sufficiently-small-loss members of THIS family. More strongly, the attained-through cap guarantee is UNIFORM over arbitrary distinct s-node Poisson normal forms with these active flags; the dyadic family witnesses failure at the next cap. This is an optimal copy guarantee for that source-closure subclass, not a decision theorem for arbitrary signatures or a universal minimal counterexample cap.

Every such h belongs to actual closure and ordinary-moment interior. With rational r and positive weights/drift/killing chosen as rational multiples of -log b for rational b near1, its finite input coordinates are ALGEBRAIC. General explicit thresholds are not computed here. The executed r=1/2,s=1,alpha=1,beta=0 input b=1-2^(-175) is the first concrete instance.

## 2. Stronger attainment lemma for arbitrary distinct residual nodes

The upper-attainment part needs no dyadic restriction. Take ANY s distinct interior residual nodes q_j, positive weights, active a/kappa according to alpha/beta. Put

    d=2s+alpha+beta+2, M=d+1.

Choose the smallest node rho; rho^2 is strictly smaller than every original node. Let D(q)=(1-q^lambda_l)_l and Htilde(z,q)=log(1+z)-log(1+z q^lambda_l), with odds z>0. Add a first strict factor with odds t at rho and a second with

    z2=t^2(1/2+t u), node rho^2+t xi.

Subtract t(1-rho) from the positive residual weight at rho. Allow order-t^3 corrections to EACH active drift/killing coefficient and to all s residual weights and nodes. Inactive a=0 or kappa=0 are held fixed and are NOT counted as two-sided variables.

The exact same-target equation is analytically divisible by t^3, exactly as in CAP6-POISSON-INTERIOR.md. Its limiting linear equation consists of

    active alpha column: lambda;
    active beta column: 1;
    for every node q_j: R(q_j), w_j R'(q_j);
    two additional columns: D(rho^2), D'(rho^2)/2;
    fixed residual vector: D(rho^3)/3.

There are d unknowns. These d columns are independent. A left nullvector c gives F(x)=sum_l c_l(1-x^lambda_l), with a root at1, made double when alpha=1; double roots at all s original nodes and at rho^2. This is at least2s+alpha+3 positive roots counted with multiplicity. If beta=1 the constant monomial of F vanishes. Thus Descartes permits at most d-beta=2s+alpha+2 positive roots. F cannot be identically zero for nonzero c. Contradiction.

The analytic IFT therefore supplies finite analytic correction functions. For sufficiently small t>0, the second odds are positive because their leading coefficient is1/2, both factor nodes stay strict, every active coefficient stays positive, every residual node stays interior and distinct, and all inactive endpoints remain fixed in the normal form.

At positive t, varying the active coefficients, all residual weights/nodes and the second factor's odds/node is a genuine TWO-SIDED normal-form block. Divide its last derivative column by the nonzero second odds. Its limit is the same nonsingular algebraic matrix, up to positive column scales. Thus the EXACT target lies in int(actual closure). Accepted int(C)=int(S) gives exact actual finite-source interior, INCLUDING when a=0 in the supplied normal form: the theorem supplies a different actual realization with strict positive A. No zero baseline is admitted as an actual source.

Projection gives the lower caps. To handle arbitrary additional closure terms, split HALF of every eligible positive residual weight and HALF of each active positive drift/killing coefficient into this interior component. Keep inactive endpoints zero. All remaining terms, including retained strict factors, other residues and the other halves, remain in C by normal-form sufficiency. Additive int(S)+C absorption then attains the full point. No source factor-count bound or explicit finite realization is extracted.

Consequently EVERY nonattained finite-log closure point, in EVERY normal form with s>=1 positive interior residual nodes and active flags alpha,beta, must satisfy

    2s+alpha+beta<=M-4.

This strengthens the earlier first-order residual-support bound by two dimensions (one allowed node). The dyadic next-cap examples show this stronger subclass bound is sharp. It does not bound the finite retained Bernoulli count or cover the s=0 endpoint branch.

## 3. Two sparse normal polynomials for the rejection cap

Return to the dyadic nodes and let

    d_NO=2s+alpha+beta+3, M_NO=d_NO+1.

There are s+1 distinct nodes in the set consisting of all original q_j and their squares: the originals plus the new last square q_s=r^(2^s). Each cube q_j^3=r^(3*2^j) differs from every power-of-two node and from1.

Construct F0 from the first d0=2s+beta+2 exponents, embedded with zero coefficients in d_NO coordinates. Give it double roots at1 and all s ORIGINAL nodes; impose vanishing constant coefficient when beta=1. Construct F1 using all d_NO exponents, with multiplicity1+alpha at1 and double roots at ALL s+1 nodes q_0,...,q_s; likewise remove the constant when beta=1.

Each homogeneous linear system has one-dimensional nonzero solution space. Existence follows because the number of imposed constraints is one less than the coefficient count. Uniqueness follows from Descartes: two independent solutions could be combined to remove the lowest allowed monomial, lowering its positive-root capacity below the required root multiplicities. The lowest allowed coefficient cannot vanish for the same reason.

When beta=0 normalize Fk(0)=1. When beta=1 normalize Fk'(0)=1; the missing constant and first exponent lambda2=1 make zero a simple root. Saturated Descartes root counts show that there are no other positive roots and the specified multiplicities are exact. Hence both polynomials are STRICTLY POSITIVE on(0,1) outside their specified original/dyadic roots. The root at1 may be simple for F1 when alpha=0, but lies at the interval endpoint.

The corresponding covectors satisfy

    c0.lambda=0;
    c1.lambda=0 if alpha=1, and c1.lambda=-F1'(1)>0 if alpha=0;
    sum c0=sum c1=0 if beta=1;
    ck.R(q_j)=0 for every original node.

Thus both annihilate the TARGET h. The first annihilates any actual source baseline. The second annihilates a baseline when alpha=1, while its mandatory strictly positive source baseline contribution is POSITIVE when alpha=0. That one-sided source requirement HELPS the rejection; it is not silently removed.

## 4. Global uniform factor estimates, including both neutral corners

Define Lk(p,q)=ck.H(p,q), Bk=sum|ck,l|. In regions where p is small, exactly the paired-normal series identities hold:

    Lk=p Fk+p^2 Tk,2/2+p^3 Tk,3/3+O(p^4),
    Tk,2(q)=2Fk(q)-Fk(q^2),
    Tk,3(q)=3Fk(q)-3Fk(q^2)+Fk(q^3).

Choose small disjoint intervals U_j about the ORIGINAL dyadic nodes. At each such node F1 and T1,2 vanish doubly, while T1,3(q_j)=F1(q_j^3)>0. On their union U, for sufficiently small p, uniform constants gamma,B0>0 give

    L1>=gamma p^3, L0>=-B0p^2.

Choose a disjoint interval V about the NEW last-square node q_s. There F0 is strictly positive, so

    L0>=delta p, L1>=-B1p^2,

for some delta>0. On compact complements of the root-interval INTERIORS, both first coefficients are positive; small-p Taylor bounds make L0 strictly positive outside U and L1 nonnegative outside U union V.

Endpoint q->1 requires a uniform all-p argument. F0 has a double root1, so

    L0=p(1-p)(1-q)^2 A0(p,q), A0(p,1)=F0''(1)/2>0.

If alpha=1, the same form holds for L1. If alpha=0, its simple root1 gives instead

    L1=p(1-q) A1(p,q), A1(p,1)=c1.lambda>0.

Analytic division and compactness make both projections positive near q=1 for EVERY strict p, including p near one.

When beta=1 there is an additional q->0 issue because the constant monomial vanishes. Here sum ck=0 makes Lk(p,0)=0, and the normalization gives

    Lk=p q Bk_corner(p,q), Bk_corner(p,0)=1/(1-p)>0.

For p in[0,1/2], compact analyticity makes both projections positive near q=0. The small total-loss budget ensures p<=1/2 in this corner. When beta=0 the constant coefficient is positive and the ordinary small-p compact bound already includes q=0.

Select the remaining compact strip away from both endpoints and a fixed upper Q<1. A sufficiently small total first-coordinate loss C forces p<=C/(1-Q) on that strip. The resulting estimates cover EVERY strict factor, not just factors local to one chosen finite source.

All constants are fixed by r,s,alpha,beta. For rational r they can be extracted by finite exact polynomial/rational bounds as in the implemented cap-seven checker, with an extra first-derivative q->0 or q->1 numerator where needed. General extraction has not been run here.

## 5. All-factor-count contradiction

An actual source would have baseline a'>0, finite strict factors, and C=h2=a+kappa+sum w_j. The first normal gives sum L0=0, hence

    delta P_V<=B0 Q_U.

The second target normal equation gives sum L1=0 when alpha=1, and sum L1=-a' c1.lambda<0 when alpha=0. In both cases sum L1<=0. The factor bounds give

    sum L1>=gamma T_U-B1 P_V^2,
    Q_U^2<=P_U T_U<=K C T_U,

where K=1/(1-max U) is fixed. For sufficiently small C,

    sum L1>=(gamma-B1(B0/delta)^2 K C)T_U>=0,

with a strictly positive bracket. If alpha=0, this already contradicts the mandatory positive baseline contribution. If alpha=1, it forces T_U=0; first-normal positivity then forces ALL Bernoulli factors to disappear. A pure baseline cannot equal the target, because w_j>0 gives h3<3h2 (killing only strengthens that strict inequality). Contradiction.

This covers arbitrary finite integer factor counts with strict p,q,A. It uses no global linear-separator claim, no conic interpretation of integer multiplicity and no ordinary-law source substitution.

## 6. Closure, ordinary interior, algebraic inputs and sharpness

Normal-form sufficiency places the family in ACTUAL closure, using strict Poisson approximants and strict perturbations of killing/zero-baseline endpoints. Its ordinary mixing measure has positive mass on infinitely many distinct positive points: use the dyadic compound-Poisson clock, multiply by exp(-a), and add killing mass at zero when kappa>0. A nonzero finite polynomial cannot vanish on this support, so every finite ordinary-moment vector is interior. This measure is analysis, not an admitted finite source.

For rational r choose b rational near1, let a=alpha*(-log b), kappa=beta*(-log b), and w_j=-log b. Then

    m_lambda=b^(alpha*lambda+beta+sum_j R_lambda(r^(2^j)))

has positive algebraic coordinates and sufficiently small first loss. The same hierarchy is attained through cap2s+alpha+beta+3 and rejected beginning at cap2s+alpha+beta+4. Source positivity determines the flag-dependent threshold; these are matched upper/lower statements for the stated family only.

## Verification and remaining master scope

General proof: hand analytic IFT, sparse Descartes systems, exact p-series, uniform endpoint division, finite Cauchy/budget argument and inherited actual-closure/source transfer. The published s=1,alpha=1,beta=0 packet at c6b9804e supplies the accepted executed subcase. Four NEW exact coefficient/corner/cutoff/exponent certificates were executed, with no floating fit or factor scan:

- s1,alpha0,beta0: NO cap6, b=1-2^(-128)
- s1,alpha0,beta1: NO cap7, b=1-2^(-222)
- s1,alpha1,beta1: NO cap8, b=1-2^(-275)
- s2,alpha1,beta0: NO cap9, b=1-2^(-403)

The zero-drift/no-killing run completed in0.24seconds; the other three combined in6.43seconds under individual35second limits. The generic checker is dyadic_poisson_certificate.py. A symbolic expanded-vs-factored comparison in its beta1 corner assertion was fixed before those executions; no failed mathematical bound is concealed. These finite cases verify their exact premises rather than establish the general theorem by extrapolation. Compact JSON companions omit normalized coefficient arrays but preserve their counts/canonical hashes, original full-certificate hashes and exact regeneration recipe. General-case runtime/threshold extraction was not executed.

The head's general hand challenge accepted the zero-drift full two-sided normal-form rank, mandatory positive actual-source baseline in the lower proof, the q->0 uniform corner, saturated root dimensions and dyadic cube separation. The four new finite budgets/exponent records are being reviewed separately. This distinction is intentional: general HAND acceptance is not an all-instance numerical census or a complete Lean source theorem.

The finite Cauchy/scalar barrier is compiled and published by the existing Lean lane at2900ad0d0c114376dc0fd4761e4367d7563e0f3f, with source-specific transfer separate. The cap-six determinant also reported successful bounded compilation; immutable release is coordinated separately. See MATCHED-CAP-PRIOR-COMPARISON.md for the close full-law dyadic Poisson decomposition prior and why it does not decide this finite-observation endpoint. No historical novelty claim is made.

General finite algebraic-input source recognition, an input-effective factor bound and the separate cap-eight/nine killing-plus-two-factor candidate remain open. This family theorem does not decide them, establish priority or provide a finite-input undecidability reduction.
