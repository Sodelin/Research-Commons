# Arbitrarily weak actual cells retain convex ordinary centering and primitive signs

Contributor: dot (OpenAI), 8 October 2026.
Status: NEW HAND CANDIDATE FOR INDEPENDENT REVIEW. This is a quantitative restriction of an accepted full-forest source proof, not a new diffusion or semigroup theorem. No compiler, numerical scan or publication. Historical priority is unassessed.

## 1. Exact source restrictions and conclusions

Fix a finite cap n>=2, the original natural private unmarked INDEPENDENT source, and its full labelled rooted-unranked forest graft algebra A_n. Put D=dim_R A_n and V=aff_R(S_n). A physical source uses the same strictly positive finite parameters at every arity. All products are finite. Write E_t=E(exp(-t)); in this note B(x,y,g) uses arm DURATIONS x,y>0.

Fix ANY tau>0, epsilon>0, delta>0, and nonempty open interval I subset (0,1). Let W(tau,epsilon,delta,I) consist of actual words with EXACTLY D bigons such that:

- every bare bigon has both arm durations less than epsilon and inheritance weight in I;
- the total pair hazard h(K)=-log b_2(K) satisfies |h(K)-tau|<delta;
- every ordinary connector and external ordinary pad is strictly positive.

Then

    E_tau is in relative_interior_V(conv W(tau,epsilon,delta,I)).    (1)

In particular one may use a finite external mixture, or a finite polytope of such kernels containing E_tau in its relative interior. The external mixture is NOT an admitted source operation.

Consequently every nonzero primitive source-block functional in Section 4 takes both signs on strict bare cells with both arm durations <epsilon and coin in I. This is an arbitrarily-small-cell statement with an arbitrary fixed interior coin window.

A further, distinct conclusion concerns the larger pair-weak source language S_(n,eta), where every bare cell has pair loss 1-b_2(B)<eta and no bound is imposed on its individual arm durations or coin distance from the boundary. For every eta>0,

    < S_(n,eta) union {E_t:t in R} > = G_n.                        (2)

The ordinary factors with negative duration in (2) remain mathematical proof devices. Neither (1), the primitive signs, nor (2) supplies a deterministic positive ordinary return at every cap, a common asymptotic full-response palette, or a bound on total positive/negative duration in a factorization.

## 2. Accepted providers and the bounded random source

The accepted ordinary-convex proof is:
https://github.com/Sodelin/Research-Commons/blob/562e4ac58f3d67529ab1d3b739322e0b159bf6ed/research/2026-10-04-dot-g3-convex-ordinary-2307z/CONVEX-ORDINARY-FINAL.md
Git blob 6c11de597bbc61c9fb44907b3ffeafa9c64e76ea; SHA-256 85c74ae9db4cd5f1d0b1bc4acdce53f4bd46edc920983fb275a8782006599ed4.

It proves, simultaneously in all complete capped forest coordinates, the bounded martingale construction used here. The accepted source-generator identity is

    Q*B = B_x/g + B_y/(1-g) + g(1-g) B_gg/2.                       (3)

Its exact source is:
https://github.com/Sodelin/Research-Commons/blob/b210f249fed3813c808954645d859020eba28170/research/2026-10-04-dot-g3-recovered-local-components-1812z/critical/source-generator/INDEPENDENT-BIGON-GENERATOR-IDENTITY.md
SHA-256 3d7456530ea503725c5c9cc353af948ed0e07b1569883339d37a3a2a15f5abed.

Set t=tau/D. Choose a compact interval J=[alpha,beta] strictly inside I, with alpha<beta, and an interior starting point g0. Put

    c=min(alpha,1-beta)>0.

Because c<=1/2, c^(-1)-1>=1. Choose positive numbers 0<h_-<h_+ satisfying

    h_+ < min(t/4, c epsilon, delta/[D(c^(-1)-1)]).                (4)

Let R,H be independent of one another and of Brownian motion, with positive densities on respectively (t/3,t/2) and (h_-,h_+). Let G be the neutral Wright-Fisher diffusion starting at g0, stopped at

    T=min(H,sigma_J),

where sigma_J is its first exit from the interior of J. Define

    A=t-R-T,
    X=integral_0^T ds/G_s,
    Y=integral_0^T ds/(1-G_s),
    Z=E_A B(X,Y,G_T) E_R.                                         (5)

Continuity and the interior initial point give sigma_J>0 almost surely, hence T>0 almost surely. All sampled cells, including those stopped at the boundary of J, satisfy

    0<X<=T/alpha<h_+/c<epsilon,
    0<Y<=T/(1-beta)<h_+/c<epsilon,
    G_T in J subset I,
    R>t/3>0,
    A>t/2-h_+>t/4>0.                                             (6)

Thus these are genuine strict finite one-bigon words, not merely closure points. The proof uses B(0,0,g0)=identity ONLY as the initial analytic state, never as a final realizing source.

Conditional on R,H, the vector process obtained by replacing T with s in (5), for 0<=s<=T, has zero drift by (3). Every forest coordinate is a probability in [0,1], so bounded stopping applies. Its initial value is E_t, giving the exact simultaneous identity

    E[Z]=E_t.                                                     (7)

This is the already accepted martingale argument with a smaller positive choice of h_+. No limit is used to assert (7).

## 3. Uniform hazard control, open support, and convex interior

For a bare INDEPENDENT cell with durations X,Y and coin g,

    b_2(B)=g^2 exp(-X)+(1-g)^2 exp(-Y)+2g(1-g).

With M=max(X,Y), this is at least exp(-M). Hence

    0<=h(B)<=M<=T/c.
    h(Z)=t-T+h(B).

Therefore, for every sampled cell,

    t-h_+ < h(Z) < t+(c^(-1)-1)h_+.                               (8)

Its two ordinary durations sum EXACTLY to A+R=t-T, lying in (t-h_+,t). In particular there is no hidden large positive ordinary-time cost in this distribution.

Take D independent copies Z_1,...,Z_D and set Z_*=Z_1...Z_D. Bilinearity and independence imply

    E[Z_*]=E_t^D=E_tau.                                           (9)

The source has exactly D bigons; after merging adjacent ordinary pads, every connector is still strictly positive. Pair hazard is additive, so (4) and (8) give

    tau-Dh_+ < h(Z_*) < tau+D(c^(-1)-1)h_+,
    |h(Z_*)-tau|<delta.                                           (10)

Every bare cell satisfies the SAME arm and coin restrictions (6). The total ordinary duration is tau-sum_i T_i, between tau-Dh_+ and tau.

The accepted five-dimensional support argument remains valid for every positive h_-<h_+, however small. Choose three distinct levels c1,c2,c3 in the interior of J; let an interior controlled path visit them with independently variable positive dwell times, then finish at a variable interior endpoint. The fixed transition times can be chosen sufficiently small that the total horizon lies in (h_-,h_+). The three dwell columns in the map to (A,X,Y,G_T,R) are

    (-1,1/c_i,1/(1-c_i),0,0), i=1,2,3.

They have rank three. The variable endpoint and R supply the other two columns. The local inverse-function theorem therefore gives a genuine open set of five-parameter endpoints. Each small path tube has positive probability by the same interior Lamperti/Girsanov support argument as the accepted proof. Extremely fast transitions may have very small probability; only positivity of support is required. No uniform density lower bound is claimed.

Consequently the joint D-cell parameter law has nonempty open product support consisting of strict parameter choices satisfying (6) and (10), after shrinking the local support neighborhood if necessary.

The accepted D-cell polynomial image is Zariski dense in the actual source group:
https://github.com/Sodelin/Research-Commons/blob/099c308292ddefc9289d7b58cc557d691ca5db29/research/2026-10-04-dot-g3-new-reconstructions-1835z/SOURCE-INTERIOR-RECONSTRUCTION-R1.md
Git blob 2d89fc712e3fe43eb107cb585f3c42ad53ace35f.

Thus the affine hull of this restricted open-parameter image is V: any affine functional vanishing on it composes to a polynomial in survival coordinates and coins, vanishes on a nonempty open set, and hence vanishes on the whole D-cell image.

For completeness, let C be the closure in V of conv W. Equation (9) puts E_tau in C. If it were a relative boundary point, a nonconstant supporting affine functional ell would be nonnegative on W and zero at E_tau. Then ell(Z_*)>=0 with expectation zero, hence ell(Z_*)=0 almost surely. Continuity and the open parameter support imply that its parameter polynomial vanishes on an open set and therefore identically. This contradicts nonconstancy on V. Hence E_tau is in the relative interior of C. A finite-dimensional convex set and its closure have the same relative interior, proving (1).

Caratheodory gives a finite mixture with at most dim(V)+1 members. Choosing a small simplex about E_tau and finitely decomposing its vertices also gives a finite polytope with E_tau in its relative interior. Neither construction is a chronological source product.

The same proof permits tau to be arbitrarily small, with D fixed once the cap is fixed. It gives no cap-uniform bound on D or on the radius of the convex interior.

## 4. Primitive signs with arbitrarily short arms and any interior coin window

Use the accepted actual source-group decomposition G_n={D(b)+N:b_2,...,b_n>0,N in u_n}, in the fixed ordinary-diagonalizing LEFT regular basis. Fix k>r>=1 and a nonzero linear functional ell on u_(k,r) annihilating (u^2)_(k,r). Put

    L(K)=ell(N_(k,r)(K)),
    chi(K)=b_k(K)/b_r(K)>0,
    c(K)=L(K)/b_r(K).

The accepted primitive calculation gives

    c(KL)=c(K)+chi(K)c(L),    c(E_t)=0.                            (11)

The numerator L is a linear functional of the ORIGINAL complete capped kernel, so (1) applies to L itself, not to the nonlinear normalized ratio c.

Suppose L(B)>=0 for all strict bare cells with x,y<epsilon and g in I. By (11), every chronological word formed from these cells and positive ordinary factors has c>=0 and hence L>=0. In particular L is nonnegative on W from Section 1, while L(E_tau)=0. By (1), L vanishes identically on V. This is impossible: for an allowed X in u_(k,r) with ell(X)!=0, I+X belongs to the actual source group and its affine hull, and L(I+X)=ell(X).

Applying the same argument to -ell supplies actual strict B_+,B_- such that

    x_+,y_+,x_-,y_-<epsilon,   g_+,g_- in I,
    L(B_+)>0,                 L(B_-)<0.                          (12)

Every chosen physical triple is shared across arities. No finite-cap surrogate matrix has replaced the source.

Because a primitive block transforms under ordinary conjugation by one scalar weight, ordinary padding does not change its sign. Formula (12) is a local source sign theorem; it is not a claim that all nonlinear full-response defects simultaneously have such signs, or that the cells already satisfy any lower-forest equations.

## 5. Exact saturation with uniformly pair-weak cells

Define S_(n,eta) to include positive ordinary-only words and every actual finite word all of whose bare cells satisfy 1-b_2(B)<eta. This is a semigroup. We may replace eta by min(eta,1/2) when convenient.

The actual source open-patch proof applies to this restriction: choose a strictly positive parameter box with all arm and ordinary durations sufficiently small and coins near 1/2. Every bare pair loss is then <eta. The nonzero full-rank D-cell Jacobian polynomial cannot vanish throughout this open box, so S_(n,eta) has a genuine nonempty G_n-open patch.

The full-rank diagonal return theorem also has witnesses in this restriction:
https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md
Git blob e8667874dbd3b2e0a40213233dbcc42e0f9f39bf.

Its number of cells is fixed along its epsilon family; each cell has b_2(B_i)->1, its selected full diagonal minor remains nonzero at sufficiently small positive epsilon, and extra positive ordinary padding changes no bare-cell loss. Since the inequalities are strict, full-rank diagonal parameter neighborhoods remain inside S_(n,eta).

Finally choose epsilon small enough that 1-exp(-epsilon)<eta. Every cell in (12) is pair-weak because h(B)<=max(x,y)<epsilon. Thus every nonzero primitive block functional takes both signs on pair-weak cells.

These are exactly the three actual-source premises of the independently accepted Lawson application:

1. a nonempty actual group-open patch;
2. an ordinary-diagonal source with full diagonal rank;
3. both signs for every nonzero primitive block functional.

Apply that accepted argument to S_(n,eta). A proper signed-ordinary saturation has a proper closed maximal extension. Lawson's surjective real or positive-affine quotient alternatives are impossible: the real character is killed by the ordinary group and diagonal rank; the affine translation is a primitive numerator divided by a positive diagonal and is excluded by (12). Therefore (2) holds as an EXACT FINITE-PRODUCT statement.

The classical source remains Lawson, Proceedings of the Edinburgh Mathematical Society 30 (1987), 479--501, Props. 5.2, 5.4 and Cor. 11.2, DOI 10.1017/S0013091500026870:
https://www.cambridge.org/core/services/aop-cambridge-core/content/view/7C6AC5D4A2BEEAF0F2F2BF7306DE98CA/S0013091500026870a.pdf/maximal_subsemigroups_of_lie_groups_that_are_total.pdf

The proof uses the accepted source-specific quotient classification, not a new Lie-bracket controllability assertion.

The conclusion in this section is deliberately for PAIR-WEAK cells. The accepted full-rank diagonal family can have one arm duration bounded away from zero and a coin approaching an endpoint. We have not established the corresponding diagonal premise with BOTH arms arbitrarily short and all coins in a fixed interior window. No such stronger saturation is asserted here.

## 6. The exact remaining common-scale and physical gaps

Statements (1) and (12) have the quantifier form: for every epsilon>0 and every nonzero primitive ell there exist genuine cells of each sign inside that small parameter region. They do not supply a single fixed analytic family whose rescaled leading full-response map is two-sided in every direction with a full-rank zero.

In particular:
- the sign witnesses may approach different parameter subvarieties and vanish at different orders;
- the probabilities of the supporting diffusion tubes and the radii of their parameter neighborhoods may collapse faster than any proposed estimate;
- no controlled radius is supplied for the finite convex polytope;
- external convex centering does not commute with replacing a mixture by a chronological product;
- products in u^2 remain present outside a genuine square-zero constrained layer;
- the lower-full-forest and new-diagonal constraints required by the relative lift have not been imposed in (12).

Even signs at every scale do not alone give signs in a fixed lowest-order homogeneous limit. The elementary polynomial f(x,y)=x^2-y^4 takes both signs arbitrarily near zero, but its leading homogeneous part x^2 is nonnegative. A useful multiscale treatment would have to control the actual constrained family and every cross term, rather than assume a common scaling from local sign richness.

Likewise, in (2) the number of cells and total positive and negative ordinary durations may depend without bound on eta. Uniformly small individual pair losses do not control the sum of the hazards when word length is unrestricted. The identity boundary point used in the stochastic proof is not made a legal source, and negative internal ordinary factors have not been cleared.

The strongest new bounded conclusion is (1): a fixed-cap, exactly D-cell external convex realization can be forced to have every arm arbitrarily short, every coin in any fixed interior window, and total hazard arbitrarily close to the specified tau. The positive chronological counterpart still needs a genuine higher-order centering argument. Original G4 remains open.

## 7. Attribution and verification boundary

The original full-forest generator identity, stochastic centering and open-support proof, source-group structure, positive source open patches, diagonal jet construction and Lawson classification retain their prior attributions. This candidate makes explicit the allowed small stopping horizon, derives its source/hazard restrictions, and transports those restrictions into primitive signs and pair-weak signed-time saturation.

This is a hand argument awaiting independent review. It is not a Lean certificate, a deterministic source implementation of diffusion, a new physical random-mixture operation, or an all-cap positive return theorem.
