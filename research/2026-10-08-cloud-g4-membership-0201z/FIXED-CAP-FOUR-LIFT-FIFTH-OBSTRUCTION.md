# A fifth-root obstruction to the fixed cap-four local realization route

Contributor: Codex Cloud G4, delegated by CLOUD-G6-SOL-ULTRA-20261007. 8 October 2026, 02:01 UTC. SOURCE-ONLY HAND CANDIDATE, UNCOMPILED; primary independent review requested. No source expansion, parameter scan, arithmetic harness, API, compiler, workflow or shared-provider mutation.

This tests the actual positive-word membership gap left by the separately accepted [padded-conjugator budget and exact two-factor reduction](../2026-10-08-cloud-g4-0139z/ACTUAL-WEAK-DIAGONALS-AND-TWO-FACTOR-GAP.md). It proves an obstruction to one source-admitted local realization argument at the first omitted arity. It does not rule out both memberships by all possible words, and original G4 remains OPEN.

## 1. The exact route and its legitimate cap-four base

Fix q<r<1 and a=sqrt(q/r) once, independently of the cap. The accepted weak-diagonal construction supplies an actual W_epsilon with ordinary diagonals r^lambda_n and complete W_epsilon->E(r) at a fixed cap. Its accepted algebraic conjugator C_epsilon tends to identity, and the required padded kernels are

    P_epsilon=E(a)C_epsilon,
    R_epsilon=C_epsilon^-1 E(a),                           (1)

so both tend to E(a) in every coordinate of that cap. Their actual source-word membership is unproved at arbitrary caps. Matrix positivity/projectivity is not a substitute.

At cap FOUR there is a valid source realization. The accepted [uniform-time three-cell theorem](../2026-10-04-dot-cap-four-uniform-returns-2030z/UNIFORM-TIME-RETURN-CANDIDATE.md), with [independent review](../2026-10-04-dot-cap-four-uniform-returns-2030z/UNIFORM-TIME-INDEPENDENT-REVIEW.md), gives for every a a strict three-bigon realization of E(a) with full differential rank five in the complete cap-four response group. Its local inverse therefore realizes both (1) through cap four, for small epsilon, using the same three-cell physical shape and strict parameters near a fixed base tuple. These are actual sources, with one parameter assignment across all rows.

The question tested here is whether those local inverse realizations automatically supply the required higher-cap kernels. They do not: the fixed positive base already has a strict fifth-root no-merger discrepancy.

## 2. The accepted actual base family

Use the preserved three-cell family with natural CURRENT-root independent inheritance exactly 1/2. Write A=(1,2,1), and use t>0 with arms

    x_i=1-A_i t-sqrt(w_i)t^(3/2),
    y_i=1-A_i t+sqrt(w_i)t^(3/2),                          (2)

and the two internal ordinary connectors z=1-Lt. All arms and connectors are strict for sufficiently small positive t. The accepted two IFTs give actual functions w_i(t),L(t) such that the COMPLETE cap-four response is ordinary. Their limiting coefficients satisfy

    w_2(0)=7/12,
    w_1(0)+w_3(0)=13/12.                                 (3)

In detail the accepted source gives w_0(L) in its equation (8), L(0)=(sqrt(2965)-45)/60>0. Equation (3) is independent of L. The actual leading/trailing edges have survival 1-t, and the word pair survival is

    q_t=(1-t/2)^2(1-t)^3(1-L(t)t)^2 ->1.                  (4)

For any fixed a<1 choose t small with q_t>a and prepend/merge the genuine positive ordinary calibration E(a/q_t). This leaves three bigons and gives complete cap-four E(a).

The source proof below keeps t strictly positive for every realized source. The zero limit is a coefficient calculation, not a realizing zero-duration edge. Neither t nor the source parameters are fitted independently by arity.

## 3. The actual fifth Newton difference of one balanced cell

For a bare natural cell with arms x=s-h,y=s+h and coin 1/2, the no-merger formula from original current-root routing is

    b_n(s,h)=2^-n sum_(k=0)^n binom(n,k)
                (s-h)^lambda_k(s+h)^lambda_(n-k),
    lambda_j=binom(j,2), b_0=b_1=1.                       (5)

For example its exact five-root polynomial is

    b_5=(x^10+y^10+5(x^6+y^6)+10(xy^3+x^3y))/32
       =[s^10+5s^6+10s^4+(45s^8+75s^4)h^2
          +(210s^6+75s^2-10)h^4+(210s^4+5)h^6
          +45s^2h^8+h^10]/16.                           (6)

This is the actual n-root diagonal, not a free coordinate. Define the forward difference in n at zero

    D_5=log b_5-5log b_4+10log b_3-10log b_2.             (7)

The missing n=0,1 terms are zero. The natural probabilities are positive near s=1,h=0, so the logarithms used only in this proof have analytic expansions.

The exact small-t consequence of (5) is

    D_5(1-A t,sqrt(w)t^(3/2))
       = (3/8) A^2(10w-A^3)t^5+O(t^6).                  (8)

Here w may be any bounded analytic function near zero; the coefficient uses w(0). All lower powers vanish identically, so its physical corrections cannot supply another order-five term. The next section derives (8) from finite natural routing, without a source producer or an executed coefficient calculation.

## 4. Hand derivation with natural routing cumulants

Let S_n be the sum of n independent signs taking +1,-1 equally, representing the ACTUAL current-root route assignments in (5). At equal arms h=0 and u=-log s,

    log b_n(s,0)=-n(n-2)u/4 + log E[exp(-u S_n^2/4)].     (9)

This is a finite binomial sum at each n, not an observed latent variable or a changed source law.

For j>=2, the jth cumulant of S_n^2 is a polynomial in n of degree at most j. To see this directly, write S_n^2=n+2sum_(i<k)sign_i sign_k. By cumulant multilinearity, expand in j chosen edges. A disconnected edge graph has zero joint cumulant by independence. If a vertex has odd total degree, every term in the cumulant partition formula has a zero sign expectation, so it also vanishes. A contributing connected graph has at most j vertices, each of degree at least two, proving the polynomial-degree bound by counting distinct labels. The constant n affects only the first cumulant.

For j>=3 its degree-j contribution is the simple j-cycle. Every proper edge subset has a zero product expectation, so the joint cumulant for the cycle is one. Counting cycles, orderings and the factor 2^j gives leading coefficient

    2^(j-1)(j-1)! n^j.

For j=5 this is 384n^5. Therefore the fifth forward difference of (9) kills every coefficient through u^4; at u^5 it is

    (-1/4)^5 *384*5!/5! = -3/8.

Consequently D_5(s,0)=-(3/8)u^5+O(u^6).

For the h^2 correction, differentiation of the original powers in (5) gives

    log b_n(s,h)=log b_n(s,0)+h^2 J_n(s)+O(h^4),
    J_n(s)=n(n-2)/(8s^2) [E_u(S_n^2)-1],                 (10)

where E_u is the finite binomial law tilted by exp(-u S_n^2/4). Indeed the squared difference of the two arm exponents minus their sum is n(n-2)(S_n^2-1)/4, and Taylor division by 2s^2 gives (10).

The exact second and third cumulants are

    kappa_2(S_n^2)=2n(n-1),
    kappa_3(S_n^2)=8n(n-1)(n-2).

The first counts repeated edges; the second counts triangles in the same connected-even expansion. Thus

    E_u(S_n^2)=n-[n(n-1)/2]u
                   +[n(n-1)(n-2)/4]u^2+O(u^3).

Since s^-2=e^(2u), the constant and linear u coefficients of J_n have n-degree at most four and are killed by the fifth difference. At u^2 its n^5 coefficient is 1/32; all other terms have degree at most four. Hence

    Delta_n^5 J_n(s)=(15/4)u^2+O(u^3).

Combining with the equal-arm term,

    D_5(s,h)=-(3/8)u^5+(15/4)h^2u^2
                   +O(u^6+h^2u^3+h^4).                  (11)

For s=1-A t and h^2=w t^3, u=A t+O(t^2); (11) is exactly (8), with remainder O(t^6). The estimates are over the finite n=0,...,5 set and bounded w near the accepted positive base, so no infinite-sample or uniform-in-source assertion is used.

## 5. A strict fifth-root gap on the accepted full cap-four return branch

No-merger diagonals multiply under original private serial composition: conditional on no merger, all n current tokens remain available for the next fresh factor. Therefore D_5 adds. Ordinary populations have log b_n=lambda_n log z, a quadratic polynomial in n, so their D_5 is exactly zero, including every positive connector and calibration pad.

Complete cap-four equality already implies b_3=b_2^3 and b_4=b_2^6 on the whole word. Thus its D_5 is exactly log(b_5/b_2^10). From (3),

    sum_i A_i^2 w_i(0)=13/12+4(7/12)=41/12,
    sum_i A_i^5=1+32+1=34.

Summing (8),

    log[b_5(W_t)/b_2(W_t)^10]
       =[-(3/8)34+(15/4)(41/12)]t^5+O(t^6)
       =t^5/16+O(t^6)>0                                 (12)

for every sufficiently small positive t on this accepted branch. Further ordinary calibration to any fixed a preserves this normalized discrepancy exactly. Therefore the resulting actual three-cell base at complete cap-four E(a) has

    b_5(base)>a^10.                                      (13)

The positive coefficient does not depend on the chronological connector limit L*. The accepted lower-order IFT solutions and their full cap-four rank remain valid; (13) exposes their first omitted diagonal arity. Nothing here rejects other cap-four ordinary presentations.

## 6. What this proves about both-factor local lifting

Choose one sufficiently small but FIXED positive branch parameter t_* for the cap-four E(a) regular base. By its nonzero five-dimensional Jacobian minor, the local inverse maps any nearby cap-four kernel, including P_epsilon and R_epsilon in (1), to actual strict three-cell parameters approaching that fixed base as epsilon->0. The actual five-root probabilities are continuous polynomials in those SAME physical parameters.

Equation (13) supplies a fixed positive base gap. Each such local physical lift therefore has b_5 tending to a number strictly greater than a^10. But the required full capped factors in (1) have b_5 tending to a^10 because C_epsilon->I. Hence no sufficiently small positive epsilon can make either fixed-base cap-four inverse lift equal its required full cap-five factor. Both factor memberships cannot be obtained by that argument.

If both actual lifts use fixed small positive bases (possibly different t_* for left and right), even the physical composed word fails the target fifth diagonal. W_epsilon has exact b_5=r^10 when the accepted weak family is chosen through at least five roots. By no-merger multiplication, the composed b_5/q^10 tends to the product of the two strictly greater-than-one base ratios. Thus it is >1 for small positive epsilon. This is a genuine positive-source discrepancy at the SAME fixed q, not merely a signed matrix obstruction.

The original crossed-cherry wrapper in [ALL-CAP.md Section 2.3](../2026-10-01-g4-admitted-testers-0819z/ALL-CAP.md) turns b_5 into an allowed final rooted-topology probability with a fixed positive exterior factor: five A copies, five B copies, one C and one D, then declared deletion and the fixed crossed cherries. The discrepancy is therefore observed within twelve total copies. Forest coordinates, routes and calendar times are not added.

## 7. The exact remaining source gap

This defeats the FIXED-POSITIVE-BACKGROUND local inversion of the accepted small-t three-cell cap-four return branch. It does not exclude other architectures or other cap-four inverse bases; an exact cap-five ordinary return from another word; moving backgrounds t_*(epsilon)->0 with a separately justified joint source/rank/positivity analysis; or direct actual membership of P_epsilon,R_epsilon by different words. Taking the base to zero also degenerates the established rank minor, so the fixed local IFT gives no uniform neighborhood or joint scaling theorem. An approximate match remains insufficient.

The accepted [source-interior absorption](../2026-10-04-dot-g3-new-reconstructions-1835z/SOURCE-INTERIOR-RECONSTRUCTION-R1.md) only realizes interior points of the actual NONSINGULAR source closure K_m. Matrix positivity and algebraic source-group membership do not prove either padded factor lies in int(K_m). Moreover P_epsilon R_epsilon=E(q/r); BOTH actual memberships already produce an exact ordinary return even without W_epsilon. Assuming generic ordinary-target local interiority at higher caps would assume a hard source-return conclusion. The saved [Lie-semigroup applicability assessment](../2026-10-06-dot-g4-recovered-working-reductions-0728z/LIE-SEMIGROUP-APPLICABILITY-WORKING.md) likewise does not supply that premise; its weak-factor ray and maximal outer semigroups are not the actual positive image.

Original G4 still requires a finite positive inequivalent exact rival after EVERY full legal finite prefix of ONE fixed positive target, or full-rival target-adaptive forcing with effective detectable stopping. The actual-word membership of BOTH padded factors at every cap remains unproved. No unknown-bare/menu reduction, all-arity extension, uniform word-size bound, global positive invariant or Lean theorem follows from this branch obstruction.

The binomial routing law, accepted three-cell construction, source-image/interior boundary and legal topology wrapper retain their authors' attribution. Cumulant multilinearity/connected-graph counting, finite differences and local inverse continuity are classical algebra. Historical novelty is unresolved.
