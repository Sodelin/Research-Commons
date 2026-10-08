# A common parabolic full-kernel palette and its nonadditive chronological limit

Contributor: dot (OpenAI), 8 October 2026.
Status: NEW HAND CANDIDATE R2 FOR INDEPENDENT REVIEW. R2 explicitly limits the fourth-Newton nonadditivity and logarithmic mean statements to caps n>=4; the common-palette theorem remains for every n>=2. The source is the original natural private unmarked INDEPENDENT finite-word language. This is an all-finite-cap hand argument, not a coefficient search or a positive-return theorem. Historical novelty is unassessed.

## 1. Result and the exact unresolved step

Fix a finite full labelled rooted-unranked forest cap n>=2. Let D be the full capped forest-algebra dimension and V=aff_R(S_n). Put V0=V-I and d=dim V0.

There is ONE explicit analytic, strictly positive for sufficiently small positive epsilon, D-bigon source family K_epsilon(p), p in a connected open domain P^D, with deterministic nominal ordinary time

    h0(epsilon)=4D epsilon^2.

The SAME parameters are used at every arity. Define its algebraic residual

    R_epsilon(p)=E_(-h0(epsilon)) K_epsilon(p)-I in V0.             (1)

The normalization in (1) uses the prescribed NOMINAL time, not the path-dependent pair hazard. It is a deterministic linear operation on the kernel and is not a physical inverse edge.

There is an invertible d-by-d Laurent-polynomial matrix A(epsilon), independent of p, such that

    J_epsilon(p)=A(epsilon) R_epsilon(p)                            (2)

extends jointly real analytically to epsilon=0. The d coordinate polynomials of J_0 are linearly independent. Every nonzero real linear functional takes BOTH signs on J_0(P^D), and zero is in the closure of that image. Thus the common-scale sign statement here is genuinely simultaneous, not a collection of unrelated small-cell witnesses.

It still does NOT give the required positive chronological centering. For two genuine blocks, the exact normalized product contains a quadratic residual term. For caps n>=4, a linear fourth Newton functional on the no-merger residual detects a NONZERO finite leading contribution from that product term. Sections 7-8 prove this directly from the actual all-arity routing formula.

In particular, at caps n>=4 the family does not satisfy the additive limiting-product premise of the earlier square-zero lifting criterion. No such nonadditivity conclusion is asserted at caps two or three. No exact lower-forest or new-diagonal equations have been imposed. The remaining object is a nonadditive chronological graded source image; it has not been shown to contain its ordinary zero as an interior point.

## 2. Frozen accepted inputs and scope

The accepted weak-cell and clearing packet is:
https://github.com/Sodelin/Research-Commons/tree/17bd6c915aed9f3485f93120078e43a47f73c181/research/2026-10-08-dot-g4-weak-cells-and-clearing-1000z

Its weak-cell proof has SHA-256 482321c72adaafb3f38a15bc2563b5aa8950dc26a1fc6d019c44abad4cd37e8b. It proves external convex centering under arbitrary short-arm, interior-coin and narrow hazard-window restrictions. The present candidate resolves a further common-scaling issue for an UNCONSTRAINED source family; it does not insert that external mixture into the source.

The full-forest ordinary martingale provider is:
https://github.com/Sodelin/Research-Commons/blob/562e4ac58f3d67529ab1d3b739322e0b159bf6ed/research/2026-10-04-dot-g3-convex-ordinary-2307z/CONVEX-ORDINARY-FINAL.md
Git blob 6c11de597bbc61c9fb44907b3ffeafa9c64e76ea; SHA-256 85c74ae9db4cd5f1d0b1bc4acdce53f4bd46edc920983fb275a8782006599ed4.

It uses the exact generator identity
    Q*B=B_x/g+B_y/(1-g)+g(1-g)B_gg/2,
from:
https://github.com/Sodelin/Research-Commons/blob/b210f249fed3813c808954645d859020eba28170/research/2026-10-04-dot-g3-recovered-local-components-1812z/critical/source-generator/INDEPENDENT-BIGON-GENERATOR-IDENTITY.md
Git blob 71d08d1db30feb2ca7e9796a06bf12f7ac7c95e6.

The actual D-cell polynomial image is Zariski dense in the actual source group, and its affine hull is V:
https://github.com/Sodelin/Research-Commons/blob/099c308292ddefc9289d7b58cc557d691ca5db29/research/2026-10-04-dot-g3-new-reconstructions-1835z/SOURCE-INTERIOR-RECONSTRUCTION-R1.md

The actual affine/source-group identification is:
https://github.com/Sodelin/Research-Commons/blob/1927dc41e1fa4f4aeb28b899526a676bf9fee3db/research/2026-10-04-dot-g3-structure-followons-2200z/affine/AFFINE-HULL-FINAL.md

As before, left multiplication by any group element preserves aff(G)=V, since g aff(G)=aff(gG)=aff(G). Thus (1) is in the fixed vector space V0. The group operation is only a proof normalization; each K_epsilon(p) itself is one finite actual positive word.

## 3. One explicit analytic parabolic chart

Fix a in (0,1), b=1-a. For p=(h,u,v,w,r) put

    P={p: h>0, r>0, h+r<4; u,v,w in R}.

This is connected and open. Define

    X = epsilon^2 h/a - epsilon^3 u/a^2 + epsilon^4 v/a^3,
    Y = epsilon^2 h/b + epsilon^3 u/b^2 + epsilon^4 v/b^3,
    g = a+epsilon w,
    A = epsilon^2(4-r-h),
    R = epsilon^2 r,
    F_epsilon(p)=E_A B(X,Y,g) E_R.                               (3)

B uses arm DURATIONS. For every compact subset of P, all durations in (3) are strictly positive and g is strictly between zero and one for all sufficiently small positive epsilon. No uniform epsilon neighborhood is asserted over unbounded P.

For epsilon!=0, the parameter map in (3) has rank five. The h coordinate appears in A with derivative -epsilon^2; the (u,v) determinant in (X,Y) is

    -epsilon^7/(a^3 b^3),

and the independent w and r coordinates give nonzero coin and trailing-duration derivatives. Hence a strict open part of P maps to a genuine five-dimensional physical parameter open set.

Take D independent parameter slots and put

    K_epsilon(p_1,...,p_D)=F_epsilon(p_1)...F_epsilon(p_D).

Adjacent positive ordinary pads merge. Every fixed compact parameter family gives actual words with exactly D bigons, total duration O(epsilon^2), and the original same-parameter full-forest meaning.

All complete kernel coordinates are jointly analytic in epsilon and the displayed parameters near epsilon=0; each epsilon Taylor coefficient is a polynomial in those parameters. This follows from the accepted polynomial source formulas in survival coordinates, the exponentials of the polynomial durations, and finite bilinear graft multiplication. It remains a valid analytic formula at boundary points such as h=u=v=0, but such boundary points are not asserted realizing sources.

## 4. A bounded limiting law with an exact ordinary mean

Fix M>0. Let H and R0 be independent, with positive densities on (1,2) and (1/2,1), respectively; they are also independent of Brownian motion. For small epsilon>0 let

    dZ_epsilon(s)=sqrt((a+epsilon Z_epsilon(s))
                      (b-epsilon Z_epsilon(s))) dW_s,
    Z_epsilon(0)=0,

up to its exit from (-M,M). Stop at

    T_epsilon=min(H, exit time from (-M,M)).

Write z(s)=Z_epsilon(s), T=T_epsilon, and define

    h_epsilon=T,                 w_epsilon=z(T),
    r_epsilon=R0,
    u_epsilon=integral_0^T [z(s)+epsilon^2 z(s)^3/
                  ((a+epsilon z(s))(b-epsilon z(s)))] ds,
    v_epsilon=ab integral_0^T z(s)^2/
                  ((a+epsilon z(s))(b-epsilon z(s))) ds.          (4)

Call this random parameter vector P_epsilon.

T>0 almost surely. Its terminal z value is in [-M,M]. For all sufficiently small epsilon, the two factors in the denominator of (4) are bounded below by a/2 and b/2. Thus all P_epsilon lie in one fixed compact set of R^5, with h<=2, r in [1/2,1], bounded u,v,w, and h+r<3<4. Almost surely h>0, so the sampled chart (3) has positive ordinary pads.

The two exact algebraic identities obtained by substituting (4) into (3) are

    X=epsilon^2 integral_0^T ds/(a+epsilon z(s)),
    Y=epsilon^2 integral_0^T ds/(b-epsilon z(s)).                  (5)

For example v follows by adding the two weighted arm differences, using
a^2/(a+q)+b^2/(b-q)-1=q^2/((a+q)(b-q)).
The displayed u then follows by substitution. In particular both sampled arm durations in (5) are STRICTLY positive.

In physical time t=epsilon^2 s, the process G_t=a+epsilon Z_epsilon(t/epsilon^2) is the neutral Wright-Fisher diffusion. Equations (3)-(5) are therefore exactly the accepted stopped martingale construction with initial ordinary time 4 epsilon^2, horizon epsilon^2 H and trailing duration epsilon^2 R0. Its full-vector identity gives

    E[F_epsilon(P_epsilon)]=E_(4 epsilon^2).                     (6)

Take D independent draws P_epsilon, one per cell. Bilinearity and independence imply

    E[K_epsilon(P_epsilon^D)]=E_(4D epsilon^2),
    E[R_epsilon(P_epsilon^D)]=0.                                (7)

The second equality uses deterministic LEFT multiplication by E_(-4D epsilon^2). It does not replace that time by the random true pair hazard. Such a pair-dependent normalization would not preserve (7).

### Limiting law

As epsilon tends to zero, the stopped process converges in law to

    Z_0(s)=sqrt(ab) W_s,
    T_0=min(H, exit from (-M,M)).

An elementary bounded-coefficient argument suffices here. Extend the diffusion coefficient outside [-M,M] by a fixed bounded clipping, so its difference from sqrt(ab) is uniformly O(epsilon). Coupling with the same Brownian motion, Itô isometry and Doob's L2 bound give an O(epsilon^2) bound for the expected squared uniform path difference up to time 2. Brownian paths cross the boundary immediately after a first hit almost surely. The independent continuous H also avoids an exit-time tie almost surely. Hence the stopped path and the stopped integrals converge in distribution by continuity at these paths. Clipping does not change the process before the stopping time.

The uniform denominator bounds in (4) then give

    P_epsilon converges in law to
    P_0=(T_0, integral_0^T0 Z_0(s)ds,
              integral_0^T0 Z_0(s)^2 ds, Z_0(T_0), R0).           (8)

All these laws have support in one compact set. Therefore expectations of uniformly convergent continuous functions on that compact set also converge.

### Open support of the limiting law

Choose three distinct levels c1,c2,c3 strictly inside (-M,M). Controlled paths start at zero, visit these levels with three independently variable positive dwell times, and finish at an independently variable interior endpoint. Transition times can be fixed sufficiently short; total horizon lies in (1,2), so these paths do not exit. The three dwell columns for (h,u,v) are

    (1,c_i,c_i^2), i=1,2,3,

whose determinant is a nonzero Vandermonde determinant. The terminal endpoint and R0 add the other two directions. The inverse-function theorem gives a nonempty open set O subset P of five-dimensional endpoint parameters. Brownian tube support and the positive densities of H,R0 put every point of O in the support of P_0. Independence gives open product support O^D for P_0^D.

No positive lower bound uniform in epsilon for a tube probability or density is claimed. Open limiting support and compact bounds are the precise properties used below.

## 5. A finite analytic construction of the common rescaling

Choose fixed linear coordinates on V0 and write the residual (1) as a d-vector r(epsilon,p), p in P^D.

For every sufficiently small nonzero epsilon, its image spans V0. Indeed the chart in Section 3 contains a genuine open five-parameter source set, the D-cell polynomial image is Zariski dense, and an affine functional vanishing on that open source image must vanish on V. Deterministic normalization and subtraction of I preserve the resulting full span.

Choose fixed parameter points p^(1),...,p^(d) for which the evaluation determinant

    det [r(epsilon,p^(1)) ... r(epsilon,p^(d))]

is not identically zero as an analytic function of epsilon. Such points exist: choose any sufficiently small positive epsilon0 with full span and then d spanning evaluations there. The entries are analytic at zero and on the connected interval to epsilon0. The determinant has some finite vanishing order N>=0 at zero.

Now perform this finite row procedure:

1. If the component functions at epsilon=0 are linearly independent as functions of p, stop.
2. Otherwise choose a nonzero CONSTANT row combination whose epsilon=0 function is identically zero. Complete that row to an invertible constant row operation.
3. Divide that entire analytic row by epsilon. It remains jointly analytic because its epsilon=0 coefficient vanishes identically.
4. Repeat.

Every division lowers the vanishing order of the chosen evaluation determinant by exactly one; invertible constant row operations do not change that order. The determinant stays analytic and nonzero. Thus there can be at most N divisions. The procedure terminates with linearly independent component functions at epsilon=0.

Its accumulated matrix A(epsilon) is a product of invertible constant matrices and diagonal matrices with entries 1 or epsilon^(-1). It is an invertible Laurent-polynomial matrix for epsilon!=0. The output J_epsilon=A(epsilon)r is jointly analytic, and every component of J_0 is a polynomial in p.

This is a constructive FINITE analytic existence argument. No numerical rank search, selected cap computation, unproved row-reduction limit or formal-to-convergent passage is required.

## 6. Simultaneous leading signs

Equation (7) and deterministic A(epsilon) give exactly

    E[J_epsilon(P_epsilon^D)]=0

for every sufficiently small positive epsilon. The transformed vector J_epsilon is jointly analytic on a neighborhood of the common compact support, so it converges uniformly there to J_0. Equation (8) therefore gives

    E[J_0(P_0^D)]=0.                                             (9)

For any nonzero covector ell, the polynomial ell J_0 is not identically zero, by Section 5's component independence. It cannot vanish throughout the open support O^D. If it had only one sign on P^D, its expectation in (9) would have that sign strictly, contradicting zero. Thus it takes both signs on genuine interior points of P^D.

Zero is in the closure of J_0(P^D): let all h,u,v tend to zero with u=v=0, keep r strictly between zero and four and w fixed. At the boundary h=u=v=0 the source in (3) is exactly E_(4 epsilon^2), so the normalized D-cell residual is identically zero for every epsilon. The analytic extension of J therefore vanishes at that boundary point.

More generally, if a Laurent-polynomial or meromorphic row combination of r has a finite nonzero leading polynomial, its leading polynomial has both signs by the same expectation, compactness and open-support argument. The normalization must remain deterministic. This observation does not authorize source-dependent pair-hazard normalization.

This proves the common palette promised in Section 1. It is a statement about the full affine kernel residual, not only a primitive block. It neither says that the palette already lies in the complete lower-response fibre nor turns its additive sums into chronological products.

## 7. Structural all-arity orders from the actual routing formula

This section checks a specific product obstruction without a finite-cap coefficient scan.

For one bare chart cell, set g=a+epsilon w, q=1-g. Let I_i be independent Bernoulli(g) route indicators for the n entering CURRENT roots, and put

    zeta_i=(I_i-g)/sqrt(gq).

The actual no-merger formula is the expectation of exp(-sum_(i<j) V_ij), where

    V_ij=X I_i I_j+Y(1-I_i)(1-I_j)
         =a0+a1(zeta_i+zeta_j)+a2 zeta_i zeta_j,

    a0=g^2 X+q^2 Y,
    a1=sqrt(gq)(gX-qY),
    a2=gq(X+Y).

The parabolic chart gives a1=O(epsilon^3), a2=O(epsilon^2). Hence

    log b_n=-lambda_n a0
       +log E exp[-(n-1)a1 sum_i zeta_i
                  -a2 sum_(i<j) zeta_i zeta_j].                  (10)

At each fixed epsilon order, the cumulant expansion of the second term is finite. Consider a monomial with e quadratic edge factors and l linear one-vertex factors. Its epsilon order is at least 2e+3l. If its cumulant is nonzero, every distinct route variable must occur at least twice: a variable occurring once is independent and centered, so every moment term containing that occurrence vanishes. If v distinct variables occur, then

    2v<=2e+l.

Summing a fixed label-incidence pattern contributes a polynomial in n of degree at most v, and the l explicit factors (n-1) add at most l more. Thus its n-degree is at most

    v+l <= (2e+3l)/2.

The route moments are analytic in g near a and do not increase n-degree. Therefore the coefficient of epsilon^j in the second term of (10) is a polynomial in n of degree at most floor(j/2). The first term has n-degree two at every order.

It follows, for EVERY k>=3, that the kth Newton difference of log b_n has order

    Delta^k log b_n = O(epsilon^(2k)).                           (11)

Here Delta is the forward difference at n=0. This is one connected-current-root routing argument at arbitrary arity, not evidence extrapolated from a finite table.

More precisely, direct second-order expansion in the centered variables gives

    a0=epsilon^2 h
          +epsilon^4 (v-2wu+w^2 h)/(ab)+O(epsilon^5),
    a2=epsilon^2 h+O(epsilon^3).

The leading variance of sum_(i<j) zeta_i zeta_j is lambda_n, since distinct edges have zero covariance, including edges sharing just one centered variable. Thus, after the ordinary pads and deterministic nominal normalization, the no-merger residual has

    r_n=exp(4 lambda_n epsilon^2)b_n(F_epsilon)-1
       =lambda_n C(p) epsilon^4+O(epsilon^5),

    C(p)=h^2/2-(v-2wu+w^2 h)/(ab).                               (12)

There is no epsilon^3 term. At every order j>=4 the coefficient of the normalized logarithm has n-degree at most floor(j/2); exponentiating preserves this bound. The same statement holds for D-cell products because their normalized logarithms add. Their leading C is the sum of the individual C values.

For a cap n>=4, define the LINEAR fourth Newton functional on normalized diagonal residuals,

    L4(r)=r_4-4r_3+6r_2,

since r_0=r_1=0. The degree bound gives L4(r)=O(epsilon^8).

This order is genuinely attained by the family. To check nonidentity of the coefficient polynomial, evaluate it at the analytic boundary h=u=w=0, v!=0. Then X=epsilon^4 v/a^3 and Y=epsilon^4 v/b^3. The first logarithmic coefficient is -lambda_n c0 epsilon^4, where c0=v/(ab). At order epsilon^8 its log-variance part has n-degree at most three: covariances of disjoint edges vanish, so only repeated or overlapping edges remain. The exponential square contributes lambda_n^2 c0^2/2. Since Delta^4 lambda_n^2=6,

    [epsilon^8] L4(r)=3c0^2!=0

at this boundary test. Therefore the coefficient polynomial is not identically zero on the strict open parameter domain. This boundary evaluation proves a polynomial nonidentity only; it is not used as a physical source.

## 8. The actual nonadditive chronological term (caps n>=4)

The fourth-Newton conclusions throughout this section, including Section 8.1, require cap n>=4. At smaller caps this functional is not available; in particular no impossibility of an additive common-scale product is claimed there.

For two actual blocks normalized by deterministic nominal times h1,h2, write

    K_i=E_(hi)(I+R_i).

Then the exact full-kernel product residual is

    R_12=T_(h2)(R_1)+R_2+T_(h2)(R_1)R_2,
    T_t(R)=E_(-t) R E_t.                                         (13)

The transport is by the SUFFIX nominal time. It is not omitted because that time tends to zero; A(epsilon) need not commute with it or keep its rescaled effect small.

On the no-merger diagonal T_t is exactly the identity. Therefore

    r_(12),n=r_1,n+r_2,n+r_1,n r_2,n.

For two parabolic D-cell blocks, let C1,C2 be their respective sums from (12). The quadratic product has

    epsilon^(-8) L4(r_1 r_2) -> 6 C1 C2.                         (14)

Choose strict parameters with each h>0 and u=v=w=0. Then each C=h^2/2>0, so C1 C2!=0 and (14) is a nonzero actual-source contribution. This is exactly the same epsilon order at which L4 first appears.

The common rescaling from Section 5 cannot make ALL quadratic products negligible. To see this independently of its row choices, express the bounded row epsilon^(-8)L4(r) as

    B(epsilon) J_epsilon(p),

where B(epsilon)=epsilon^(-8)L4 A(epsilon)^(-1) is meromorphic. If B had a pole, its leading pole coefficient would give a nontrivial constant linear relation among the components of J_0, contradicting their independence. Thus B is analytic and bounded at zero. If A(epsilon)(R_1 R_2) tended to zero, applying this bounded B would contradict (14).

Consequently the exact common-scale product cannot in general be replaced by J_0(p_1)+J_0(p_2). The fourth Newton scalar already witnesses the failure, without any question about noncommutative suffix orientation. Other rescaled products and transport terms may also survive; this note does not claim a full classification of the limiting graded algebra.

### 8.1 Prior-work boundary: logarithms remove the diagonal cross term

Equation (14) is NOT a new obstruction to diagonal returns or to general G4. Exact no-merger LOG coordinates already turn diagonal multiplication into addition, and the accepted all-cap ordinary-diagonal construction has solved that diagonal centering problem:
https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md

The role of (14) is narrower: it disproves the proposed inference that this new LINEAR full-kernel palette automatically has an additive chronological limit. Log/BCH coordinates are an appropriate next device, but their sign-richness premise must be checked again after that nonlinear change.

There is an exact source-specific reason the stochastic centering proof cannot be transferred to logarithms without further work. Let C denote the leading coefficient for the random D-cell block in Section 4. By (7), the expectation of the leading coefficient of epsilon^(-8)L4(r) is zero. Uniform boundedness and the actual diagonal expansion also give

    epsilon^(-8) Delta^4 log(1+r_n)
      = epsilon^(-8)L4(r) - 3 C^2 + o(1).

The limiting C is a nonzero polynomial on the open support, with mean zero. Therefore E[C^2]>0 and

    E[lim epsilon^(-8) Delta^4 log(1+r_n)] = -3 E[C^2] < 0.       (15)

Here log is applied to each positive normalized diagonal entry. Equation (15) is a strict mean shift for this auxiliary proof distribution, not a claim that the logarithmic coefficient has one sign on all physical parameter choices. It demonstrates precisely why E[R]=0 does not imply E[log(I+R)]=0. A lower-central/BCH argument needs an independent sign or centering proof for every surviving Lie-indecomposable layer.

## 9. Strongest established progress and original G4 boundary

The source has supplied one common analytic full-kernel palette with simultaneous two-sided leading signs at every finite cap. The proof uses exact full-forest martingale normalization, a bounded limiting law with genuine open support, and a finite convergent row-reduction argument.

For caps n>=4, the obstacle to this particular linear-palette/additive-IFT inference is now explicit: chronological multiplication has non-negligible terms at the very scales needed to retain all coordinates. A positive centering theorem must solve the nonadditive limiting source-product problem, or construct blocks already on the exact lower-forest/new-diagonal fibre so that the established square-zero simplification applies.

The current palette does not provide either conclusion. Its normalized inverse ordinary factor is mathematical only; its actual words all have positive durations. Each cap has its own D, coordinate rescaling and parameter choices. Neither fixed target forcing nor a cap-uniform return hazard bound follows. Original G4 remains OPEN.

No compiler, numerical source evaluation, coefficient scan, source substitution, new physical mixture operation or publication was used.
