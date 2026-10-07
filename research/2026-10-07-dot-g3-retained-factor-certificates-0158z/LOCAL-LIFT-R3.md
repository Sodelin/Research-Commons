# A semialgebraic all-state lift of the local retained-factor obstruction

Contributor: dot (OpenAI), 7 October 2026. Revision 3 hand candidate, with a narrow prior-flag attribution clarification. Independent review pending; the earlier working version is preserved. This note proves a local auxiliary-state exclusion assuming the inherited fixed critical anchor and uniform tail estimates; a separate global initialization/classification argument is still required before it is a source separator. No computation or execution is claimed.

## 1. Inherited data and intended scope

Use the six COMMON exponents Lambda=(1,3,6,10,15,21), r=1/2, s=r^2, D(q)_lambda=1-q^lambda, f_lambda(p,q)=1-p+p q^lambda and H=-log f. Let c be the old rational paired normal with F(q)=c.D(q)>=0 for q>0 and precisely the double positive roots 1,r,s. Fix a strict effectively algebraic pair theta*=(p*,q*) satisfying

    c.H_p(theta*)=c.H_q(theta*)=0,
    rank[Lambda,D(r),D'(r),H_p(theta*),H_q(theta*)]=5.

Let t be the unique coordinates of D(s) in these five columns, and assume its D'(r) coordinate t_r is nonzero. These are exactly the accepted one-retained NO hypotheses, with the previously independently certified example available. No new anchor or NO family is constructed.

The old accepted tail lemma supplies fixed disjoint compact node intervals about r and s, a small odds threshold, and positive constants such that, for every sufficiently small Jensen defect

    j(p,q)=f_21/f_1^21-1,

the following partition has uniform bounds. Class U has q in the r interval and z=p/(1-p) below the odds threshold; class V is the corresponding s interval; O is the remaining strict pairs. With L=c.H:

    U: L>=alpha z(q-r)^2+gamma z^3;
    V: L>=alpha z(q-s)^2-B z^2;
    O: L>=alpha_O j>0.

Also j is comparable with z on U,V, uniformly; on O the drift-normalized moment ratios are between 1 and 1+j. All constants are chosen before shrinking the final total tail budget. The old proof verifies the p-to-one, q-to-zero corner. Ordinary/equal-arm COMMON factors are separate identity updates in normalized coordinates.

The current proof lifts these already accepted estimates to arbitrary auxiliary states. It does not infer invariance merely from their validity on source histories.

## 2. Rational potentials and uniform one-factor bounds

Choose three integer rows v_1,v_2,v_3 in the rational annihilator of span{Lambda,D(r)} such that

    A=(v_j.D'(r), v_j.H_p(theta*), v_j.H_q(theta*))_(j=1,2,3)

is invertible. Such rows exist by the displayed rank-five hypothesis: the quotient of c-perp by span{Lambda,D(r)} has dimension three, and rational rows in the four-dimensional annihilator separate it. Equivalently, complete the rational nonzero row c to a rational basis of that annihilator and use the other three rows. Clear denominators. Set v_0 to a positive integer multiple of c.

Define rational positive monomial potentials on positive tuples,

    N_j(x)=product_lambda x_lambda^(v_j,lambda), j=0,1,2,3.

For a bare factor write d_j(p,q)=N_j(f(p,q))-1. Integer negative powers are rational functions with strictly positive denominators. All v_j annihilate ordinary drift and D(r).

There are fixed positive rational bounds C, beta, kappa and a rational small-defect threshold tau>0 for which the following inequalities hold on j(p,q)<tau. Scaling v_0 is included in the constants. On U put h=q-r, on V put h=q-s.

For j=1,2,3, let

    a_j=v_j.D'(r), b_j=v_j.D(s), e_j=v_j.D'(s).

Then

    U: |d_j+a_j z h-b_j z^2/2|<=C(z h^2+z^3),
       |d_j|<=C(z|h|+z^2);
    V: |d_j+b_j z+e_j z h|<=C(z h^2+z^2),
       |d_j|<=Cz;
    O: |d_j|<=Cj(p,q).

For the normal potential, set local positive charge ell equal to z h^2+z^3 on U, z h^2 on V, and j(p,q) on O; set local negative charge w=z^2 on V and zero elsewhere. Then

    N_0(f) (1-beta w) (1+kappa ell)<=1,
    1-beta w>0.

Choose C also so that z<=Cj and j<=Cz on U,V, and ell<=Cj on every class. In the later state, these bounds control every aggregate by the total Jensen budget.

Here is why these rational inequalities have effective finite certificates. The odds expansion gives

    log N_j(f)=-z v_j.D(q)+z^2 v_j.D(q^2)/2+O(z^3).

The term v_j.D(r) vanishes. Taylor expansion in q gives the U formula, and exponentiating changes the remainder only by a bounded multiple of z h^2+z^3. On V, its O(z^2) error is explicitly retained. On O, each normalized factor f_lambda/f_1^lambda lies between 1 and 1+j, so each fixed integer monomial differs from one by at most Cj when j is small. This bound includes both neutral corners and needs no new reciprocal-node source operation.

The inherited normal inequalities and e^(-x)<=1/(1+x), e^x<=1/(1-x) for x in their indicated positive ranges give the normal rational inequality after decreasing kappa and increasing beta if necessary. Each assertion is itself a finite rational inequality over the semialgebraic strict domain with j<tau. Positive denominators can be cleared; integer powers and absolute values are finite algebraic expressions. Rational enumeration with RCF checking finds suitable constants because the uniform analytic estimates just proved ensure their existence. No such enumeration has been executed.

## 3. Auxiliary tail states

Let y_lambda be the normalized tail coordinates; y_1=1 and Delta=y_21. Retain

    1<=y_lambda<=Delta,
    0<=B<eta<min(1/2,tau),
    1+B<=Delta, Delta(1-B)<=1.

The source updates are y_lambda'=y_lambda f_lambda/f_1^lambda and B'=B+j. Ordinary scaling acts trivially. When the updated Delta remains below 1+eta, the lower budget bound implies B'<eta. Both budget inequalities hold on all auxiliary states: the first uses (1+B)(1+j)>=1+B+j; the second uses

    (1+j)(1-B-j)=1-B-Bj-j^2<=1-B.

Include nonnegative aggregates P,Q,T,U2,V,V2,O,W,A_U,A_V, signed M,N, and define Z=U2+V2+T+O. Include a persistent finite flag sigma in {0,1}: sigma=0 requires P=Q=T=U2=M=A_U=0, while sigma=1 requires P,Q,T>0. Every strict U update sets sigma to 1; V, O and ordinary updates preserve it. These clauses are semialgebraic and hold at initialization. A strict U update has z>0, so the positive clause is preserved on every auxiliary state. The older 02:32/03:23 pure-family lifts already use a zero-statistic-implies-ordinary clause. The later all-rational proof 67e62d59 explicitly includes T=0 implies P=0. The binary sigma here is an encoding/refinement of that latter strictness clause, reusing the older mechanism; it is not a factor-count bound or a newly discovered strict-history principle. The aggregate updates are:

- U: add z,z^2,z^3,z h^2,z h,z|h| respectively to P,Q,T,U2,M,A_U.
- V: add z,z h^2,z h,z^2,z|h| respectively to V,V2,N,W,A_V.
- O: add j to O.
- All classes: add j to B.

Unlisted aggregates are unchanged. Impose the all-state inequalities

    A_U^2<=P U2, M^2<=P U2,
    A_V^2<=V V2, N^2<=V V2,
    Q^2<=P T, W<=V^2,
    P+V+Z<=C_1 B,
    B<=C_1(P+V+O).

Choose C_1 large enough for the factorwise bounds. The first five quadratic inequalities are positive-semidefinite two-by-two matrix constraints, preserved by adding the corresponding positive rank-one matrix; signs of h do not matter. W<=V^2 is preserved because W'=W+z^2<=V^2+z^2<=(V+z)^2. The last two inequalities are preserved additively by the one-factor comparisons. All hold at zero initialization. Thus no appeal to a latent finite factor history is needed to justify them.

For j=1,2,3 add real S_j and nonnegative R_j with

    |S_j|<=R_j<1/2,
    |N_j(y)-1-S_j|<=R_j^2/(1-R_j),
    |S_j+a_j M+b_j(V-Q/2)+e_j N|<=C_2(Z+W),
    R_j<=C_2(A_U+Q+V+O).

The updates are S_j'=S_j+d_j and R_j'=R_j+|d_j|. The first two are preserved by the elementary product-tracking lemma in PLAN-AND-PRODUCT-LEMMA.md, including positivity of the potential. The last two are preserved by adding the appropriate factorwise rational inequalities in Section 2. Choose C_2 sufficiently large once and for all. The U and V remainder charges add into Z+W; O is included in Z.

The bound R_j<1/2 is reestablished whenever the state stays in the small-Delta branch, by choosing eta sufficiently small after all fixed constants. Indeed the aggregate constraints give

    R_j^2<=C_3(eta Z+V^2),

using A_U^2<=P U2, Q^2<=P T, O^2<=C_1 eta O, and P,V<=C_1 eta. A_U+Q+V+O is uniformly O(eta), so every updated R_j is below 1/2. The proof does not use a source length.

Finally impose the normal constraint

    N_0(y)(1-beta W)(1+kappa Z)<=1,
    1-beta W>0.

This is invariant on all auxiliary states. The one-factor inequality in Section 2 multiplies the old bound. The new numerator factors satisfy

    1-beta(W+w)<=(1-beta W)(1-beta w),
    1+kappa(Z+ell)<=(1+kappa Z)(1+kappa ell).

Every displayed factor is positive when eta is small, because W<=V^2<=C_1^2 eta^2. The product of these two comparisons proves the updated normal inequality. Zero initialization has N_0=1 and satisfies it exactly.

The conditions above are a finite semialgebraic tail-state description, with exact rational or algebraic fixed coefficients and rational update maps. They are inductive while Delta<1+eta. Crossing that boundary is left to the global branch construction; no assertion of invariance through a discarded state is being made here.

## 4. Algebraic target equations with a nearby retained factor

Let theta be stored in a small compact strict neighborhood of theta*, put delta=theta-theta*, and suppose a current state has normalized coordinates

    x_lambda/x_1^lambda = [f_lambda(theta)/f_1(theta)^lambda] y_lambda.

All identities are rational with positive denominators. At a target satisfying

    N_j(x)=N_j(f(theta*)), j=0,1,2,3,

the tail potentials satisfy exactly

    N_j(y)=G_j(theta):=N_j(f(theta*))/N_j(f(theta)).

This includes every target A^Lambda f(theta*) exp[-u D(r)], because all rows annihilate Lambda and D(r). No exp or log is required to state the target equalities.

The rational functions G_j have algebraic coefficients and nonzero denominators near theta*. Their Taylor bounds give, with fixed constants,

    |G_j-1-v_j.H_p delta_p-v_j.H_q delta_q|<=C_4 ||delta||^2,
    |G_0-1|<=C_4 ||delta||^2.

The second bound uses criticality. The constants can be chosen and certified by rational/RCF inequalities on a sufficiently small algebraic box. Bounds on the rational Hessians and the mean-value theorem suffice; the use of H derivatives here denotes their rational values, not an exponential decision primitive.

The product-tracking inequalities yield

    |N_j(y)-1+a_j M+b_j A+e_j N|<=C_5(Z+V^2),
    A=V-Q/2.

Indeed W<=V^2 and R_j^2/(1-R_j)<=2C_3(eta Z+V^2). Combining with the target Taylor bounds and inverting the fixed matrix A from Section 2 gives

    (M,delta_p,delta_q)=-t_reduced A-k_reduced N+E,
    ||E||<=C_6(Z+V^2+||delta||^2).

The first coordinate of t_reduced is exactly the inherited nonzero t_r: quotienting by Lambda,D(r) removes only their coefficients from the five-column decomposition of D(s). In particular

    ||delta||<=C_7(|A|+|N|+Z+V^2+||delta||^2).

At the normal equation, G_0=1+O(||delta||^2). After shrinking the anchor neighborhood and eta so G_0>=1/2 and beta W<=1/2, the normal auxiliary inequality implies

    Z<=C_8(V^2+||delta||^2).

This follows by expanding G_0(1-beta W)(1+kappa Z)<=1 and absorbing the bounded positive factors; it is an ordinary rational inequality with fixed denominator margins.

## 5. All-state absorption and exclusion

Shrink the anchor neighborhood to absorb the quadratic delta term. Square the previous bound on delta, use A^2<=C(V^2+Q^2), N^2<=V V2<=C_1 eta Z, and Z<=C_1 eta. With constants fixed before choosing eta, this gives

    ||delta||^2<=C_9(V^2+Q^2+eta Z).

Combining with the normal inequality and taking eta smaller yields

    Z+||delta||^2<=C_10(V^2+Q^2).

The first coordinate of the projected tangent equation now reads

    M=-t_r(V-Q/2)-k_r N+e,
    |e|<=C_11(V^2+Q^2).

Cauchy and the preceding bound imply

    M^2+N^2<=C_12 eta(V^2+Q^2),
    e^2<=C_12 eta^2(V^2+Q^2).

Since t_r is fixed and nonzero, decreasing eta makes

    |V-Q/2|<=(V+Q)/4.

Consequently V<=Q. It follows that

    T<=Z<=C_13 Q^2<=C_13 P T.

Choose eta so C_13 P<=C_13 C_1 eta<1. Hence T=0, then Q=0 from Q^2<=P T; V=0, Z=0 and delta=0 follow. Since T=0 rules out sigma=1, the persistent flag in Section 3 forces sigma=0 and hence P=0. This step is essential: Cauchy alone would allow a spurious auxiliary limit with P>0 and Q=T=0. No finite source-count bound is used. Finally, the stored B<=C_1(P+V+O) gives B=0. Then Delta(1-B)<=1 and Delta>=1 force Delta=1, hence all normalized tail coordinates equal one. The anchor is theta*. A target with total normalized 21-coordinate strictly larger than that of theta* is therefore excluded. For the old positive-residue family this strict inequality is exp[u(21D_1(r)-D_21(r))]>1.

This last comparison can be checked directly in algebraic coordinates for an actual supplied family member; no logarithmic equality test is used. It does not claim an executed numeric family cutoff.

## 6. Status and remaining work

The strict-primary flag is now part of the state and the proof uses it explicitly. The candidate local result is a finite semialgebraic tail relation, invariant under every physical update that remains below its small-defect threshold, and incompatible with the displayed nearby-anchor target conditions having strictly greater normalized 21-coordinate than the fixed anchor. The global no-anchor/one-anchor/escape construction and restricted-envelope initialization remain a separate proof obligation. Neither this file nor that later integration is accepted until independently reviewed. No original whole-fibre completeness or master result follows.
