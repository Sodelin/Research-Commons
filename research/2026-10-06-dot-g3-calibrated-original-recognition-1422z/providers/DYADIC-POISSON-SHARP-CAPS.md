# Matched copy thresholds for dyadic Poisson closure signatures

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 00:31 UTC; additive corollaries updated01:19 UTC.
Status: the general all-flag HAND theorem and Sections7-9 passed the current head's independent challenge2026-10-02. Its independent four-case rational validation also passed, rederiving endpoint polynomials, quotient factors and all cutoff budgets; immutable public review receipt is being prepared. The accepted s=1, positive-drift, zero-killing cap6/cap7 packet has a full rational certificate. No all-cap census, extracted factor witness or general-recognition closure claimed.

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

## 7. Finite algebraic recognition branches from the same certificates

Fix one parameter case for which the uniform bounds and rational cutoff C_* have been certified. Replace C_* by min(C_*,1) if necessary. Let e0,e1 be positive-denominator-cleared integer versions of its two covectors, padded by zeros when reading a larger cap. For any positive algebraic input with every coordinate strictly below1, impose

    m2>1-C_*/2;
    product_(e0,l>0) m_l^(e0,l)=product_(e0,l<0) m_l^(-e0,l);
    product_(e1,l>0) m_l^(e1,l)=product_(e1,l<0) m_l^(-e1,l).

These are finite algebraic predicates; they do not require a Poisson representation of the input. Positivity makes the monomial equations equivalent to c0.h=c1.h=0. The cutoff gives C=-log(m2)<C_* by -log(1-x)<2x for0<x<1/2. Thus the same all-factor inequalities apply to any hypothesized strict source.

If alpha=1, the proof forces every Bernoulli factor to disappear. On this branch exact source membership is therefore equivalent to m_l=m2^lambda_l for EVERY supplied coordinate. That pure baseline has the strict positive source A=m2. If alpha=0, c1.lambda>0 makes the mandatory positive actual baseline contradict the second normal equation, so EVERY input on the branch is rejected. The flag alpha labels the selected certificate and covector; it does not permit an actual source with zero baseline.

For a cap larger than the certificate cap, apply the two normals only to the certificate coordinates and, in the alpha=1 case, check the baseline equations at all higher coordinates too. There is no implication for inputs that fail the two normal equations or small-loss cutoff. The four new finite case records supply their exact integer rows and cutoffs; the already accepted positive-drift/zero-killing cap-seven case supplies the earlier branch in CONCRETE-ALGEBRAIC-CAP7-NO.md.

## 8. Squared-node union corollary and why one chain matches

The lower proof has a useful extension. Let Q be ANY finite set of s distinct nodes in(0,1), put T=Q union {q^2:q in Q}, and write t=|T|. Suppose q^3 is outside T for every q in Q. Then every sufficiently-small-loss normal form supported on Q, with the same active flags alpha,beta, is rejected beginning at

    M_NO=2t+alpha+beta+2.

Use the same F0, with double roots at1 and Q. Construct F1 with a root at1 of order1+alpha, double roots at all of T, and vanishing constant when beta=1; its coordinate count is now2t+alpha+beta+1. The same saturated Descartes argument gives positivity outside its specified roots. At every original node, F1 and its second p-series coefficient vanish doubly because q^2 is in T; its third coefficient is F1(q^3)>0 by the hypothesis. The finite set T minus Q replaces the single new-root interval V. Take the minimum positive F0 bound over these intervals and aggregate their p mass. Every endpoint and coupled-budget argument from Sections4-5 is unchanged. This is a hand corollary of the stated estimates, not a new executed certificate case.

The directed relation q -> q^2 among members of Q has no cycles and has at most one predecessor and successor per vertex. It therefore splits Q into c disjoint finite chains. Each chain contributes exactly one new square to T, so t=s+c. The new lower threshold is2s+2c+alpha+beta+2, while the arbitrary-node upper guarantee is2s+alpha+beta+3. These two bounds meet at consecutive caps when c=1. A single chain is precisely Q={r,r^2,...,r^(2^(s-1))}, and its cubes automatically avoid T. Thus the dyadic matched result follows from the minimal possible squared-node union, rather than from a numerical cap ladder. For c>1 this corollary leaves an intermediate-cap gap and does not claim an optimal threshold there. If an original cube belongs to T, the required strictly positive third-order coefficient fails and this corollary makes no rejection claim.

## 9. No cap-only uniform total-factor bound

The small-loss rejection also excludes a finite chain with CLOSED parameters0<=A,p_i,q_i<=1 whenever its output coordinates are positive. This is a mathematical endpoint reduction, not an enlargement of the admitted strict source model. Positivity excludes A=0 and factors with p=1,q=0. Delete p=0 or q=1 neutral factors; fold p=1,q>0 into nonnegative drift; fold q=0,p<1 into nonnegative killing. What remains has the form

    h=a' lambda+kappa' 1+sum_i H(p_i,q_i),
    a',kappa'>=0, 0<p_i,q_i<1.

All observed exponents are positive integers; the coordinate formula contains no zero-th power at a corner. Simultaneous p->1,q->0 makes the factor tend to zero at EVERY observed exponent and cannot occur in a positive output tuple. The folded quantities a' and kappa' are finite and each is at most h2, since all first-coordinate losses are nonnegative. Thus unbounded logarithmic parameters do not compromise the compact survival-coordinate argument.

For either paired-normal construction, c0.lambda=0, c1.lambda>=0, and both sums of covector entries are1 when beta=0 and0 when beta=1. Since the target's two normal projections vanish, the factor sums satisfy

    sum L0=-kappa' sum(c0)<=0;
    sum L1=-a' c1.lambda-kappa' sum(c1)<=0.

The first inequality still gives delta P_V<=B0 Q_U. The second and the same strict coupled budget force T_U=0. Every remaining strict factor outside U has strictly positive L0; hence the first inequality then removes all strict factors. The closed-parameter target would therefore have to be h=a' lambda+kappa'. This is impossible: each positive Poisson term R_lambda(q) has strictly negative second derivative in the real variable lambda, so the stated target is strictly concave in lambda and cannot agree with an affine function at the three or more distinct observed exponents. The argument also applies to the squared-node union corollary under its cube-separation premise.

For a fixed cap and factor bound N, the closed-parameter observation map is polynomial and continuous on the compact cube[0,1]^(2N+1). Its image K_N is compact and includes every strict chain with at most N factors, padding shorter chains with neutral factors. The rejected positive tuple lies outside every K_N by the endpoint reduction. Thus each fixed N has an open neighborhood of the tuple that contains no actual chain of at most N factors.

Actual closure supplies strict-source sequences converging to this tuple. Along ANY such sequence the minimum possible EXACT number of Bernoulli factors tends to infinity: for every fixed N, eventually the sequence is outside K_N. The rejected tuple is in ordinary-moment interior, which is open, so these actual approximants eventually belong to ordinary-moment interior too. Consequently there is no uniform total-factor bound depending only on the cap at these rejection caps, even after that restriction. This conclusion leaves an INPUT-DEPENDENT computable bound entirely open and gives no rate or bound for epsilon approximation. It does not say that an individual actual input requires infinitely many factors, or contradict finite retained-tail compression of closure normal forms.

The unbounded exact counts already occur for RATIONAL observation inputs. For the accepted original cap-seven target set b=1-2^(-175), theta=-2 log b, and for integers N>=2 choose p_N=ceil(theta N)/N^2. Here0<theta<1 makes0<p_N<1, while N p_N->theta and N p_N^2->0. The strict N-factor signature

    m_lambda^(N)=b^lambda*(1-p_N+p_N*2^(-lambda))^N

is rational at every supplied integer exponent, uses the SAME fixed rational baseline A=b and factor ratio q=1/2, and converges to b^(lambda+2-2^(1-lambda)). Its globally minimum exact factor count tends to infinity by the compact-image argument, even when alternative realizations may choose arbitrary strict baselines, probabilities and ratios. At cap six use instead the certified zero-drift input b0=1-2^(-128), theta0=-2 log b0, A_N=1-1/N and p_N=ceil(theta0 N)/N^2. The rational strict signatures A_N^lambda*(1-p_N+p_N*2^(-lambda))^N converge to b0^(2-2^(1-lambda)), whose minimum exact counts diverge by the same theorem. Thus rational-input unboundedness holds at every fixed cap>=6; the cap-seven version additionally keeps the baseline fixed. These are theoretical rational sequences, not newly executed large-N computations. No numerical approximation rate or bit-complexity bound is asserted.

## Verification and remaining master scope

General proof: hand analytic IFT, sparse Descartes systems, exact p-series, uniform endpoint division, finite Cauchy/budget argument and inherited actual-closure/source transfer. The published s=1,alpha=1,beta=0 packet at c6b9804e supplies the accepted executed subcase. Four NEW exact coefficient/corner/cutoff/exponent certificates were executed, with no floating fit or factor scan:

- s1,alpha0,beta0: NO cap6, b=1-2^(-128)
- s1,alpha0,beta1: NO cap7, b=1-2^(-222)
- s1,alpha1,beta1: NO cap8, b=1-2^(-275)
- s2,alpha1,beta0: NO cap9, b=1-2^(-403)

The zero-drift/no-killing run completed in0.24seconds; the other three combined in6.43seconds under individual35second limits. The generic checker is dyadic_poisson_certificate.py. A symbolic expanded-vs-factored comparison in its beta1 corner assertion was fixed before those executions; no failed mathematical bound is concealed. These finite cases verify their exact premises rather than establish the general theorem by extrapolation. Compact JSON companions omit normalized coefficient arrays but preserve their counts/canonical hashes, original full-certificate hashes and exact regeneration recipe. General-case runtime/threshold extraction was not executed.

The head's general hand challenge accepted the zero-drift full two-sided normal-form rank, mandatory positive actual-source baseline in the lower proof, the q->0 uniform corner, saturated root dimensions and dyadic cube separation. Its independent rational checker separately rederived and passed all four finite budgets/exponent records, including the complete endpoint derivative polynomials and quotient/compact lower bounds. Independent checker SHA256: cf137900dc26be1d4f7e1d6ddc904297e464ca8017ce16ca7ef38d3150faea50. The finite normal predicate, squared-node union and compact K_N argument also passed direct hand challenge. General HAND acceptance is not an all-instance numerical census or a complete Lean source theorem.

The finite Cauchy/scalar barrier is compiled and published by the existing Lean lane at2900ad0d0c114376dc0fd4761e4367d7563e0f3f, with source-specific transfer separate. The cap-six determinant and strict-domain rank are published atdd8e5176e67e71526f282d5922e48c8697e2cc39, with analytic/source transfer separate. See MATCHED-CAP-PRIOR-COMPARISON.md for the close full-law dyadic Poisson decomposition prior and why it does not decide this finite-observation endpoint. No historical novelty claim is made.

General finite algebraic-input source recognition, an input-effective factor bound and the separate cap-eight/nine killing-plus-two-factor candidate remain open. This family theorem does not decide them, establish priority or provide a finite-input undecidability reduction.
