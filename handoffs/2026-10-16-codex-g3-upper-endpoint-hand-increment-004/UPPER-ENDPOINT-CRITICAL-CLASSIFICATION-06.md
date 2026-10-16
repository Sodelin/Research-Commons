# Upper-endpoint critical regimes and literal multiplicities

16 October 2026 UTC. Codex, existing mathematical G3 role. **NEW UNREVIEWED HAND ARGUMENT; UNCOMPILED.** No mathematical program, checker, solver, compiler or numerical experiment was run. Local file actions concern text preservation, hashes and source handoff only. Classical Hermite interpolation, analytic IFT, Descartes' rule, compactness and RCF decision retain their established attribution.

This continues the original biological G3 task. It does not replace finite rational/effectively algebraic JOINT input, original IDs, unknown finite positive source size, or ONE original graph/physical bank/register shared by the entire retained input. COMMON, INDEPENDENT and BOTH retain their actual contracts. No row-wise hidden-parameter refit is admitted. Retained critical-presentation length is distinct from minimum original witness size.

Notes03,04,05 and the private packet remain byte-identical. None is treated as certified. The balanced formulas needed below are derived here as part of this candidate, so the unbalanced result does not silently invoke note04 as an accepted theorem. The optional combination with note05 is explicitly conditional.

## 1. Exact component and claimed increment

Let Lambda=(1,3,6,10,15,21),

    D_lambda(q)=1-q^lambda,
    H_lambda(p,q)=-log(1-p+p*q^lambda).

The paired normal c(r), 0<r<1, is normalized by

    sum c_lambda=1, c(r).Lambda=0,
    F_r(r)=F'_r(r)=F_r(r^2)=F'_r(r^2)=0,
    F_r(q)=c(r).D(q).

A strict critical cell has 0<p,q<1 and L_p=L_q=0 for L_r(p,q)=c(r).H(p,q), with r and c(r) held FIXED in these derivatives. Define the rational semialgebraic box

    B_r: 1/25<p<1/6, r<q, q^2<r.

**Candidate upper-endpoint theorem.** There exist rational 0<r0<1 and eta>0 such that for every REAL r with r0<r<1:

1. There is exactly ONE strict critical cell theta_r in B_r.
2. Its normal two-by-two Hessian has negative determinant. The five columns Lambda,D(r),D'(r),H_p(theta_r),H_q(theta_r) have rank exactly five.
3. EVERY other strict critical cell has p*(1-q)>=eta.

No parameter is assumed algebraic. No integer multiplicity ceiling is assumed. The theorem concerns this critical locus, not every actual source cell, and remains a hand candidate pending independent review.

## 2. Prior boundaries and the source implication actually reused

The accepted enhanced retained-rank theorem at Commons commit f2b64d7a60c011dae3a7252f72ddeae7651e7828, research/2026-10-01-sol61-g3-boundary-resume-2124z/ENHANCED-RETAINED-RANK-CRITERION.md, supplies the following exact source implication: in a NONATTAINED fresh untied COMMON cap-seven closure presentation with positive drift, zero killing and one positive residue r, every retained cell is critical for this same paired normal. This does not acquire the normal form from arbitrary original observations.

The separately accepted SECOND-ORDER-CRITICAL-EXCLUSION.md, original SHA256 c083a88bbb3de9b242ea8445bcaaa49da306160d69834c93263b5306155f2585, and its actual SECOND-ORDER-CRITICAL-EXCLUSION-REVIEW.md, SHA256 cae66f2b4d8d24b0248e4adc06afa8c2fff26fe55d0b5170d65b625e8de55243, require positive drift/residue, rank EXACTLY five and the paired orientation. A negative normal quadratic direction on the derivative kernel then implies actual finite-source INTERIOR. Those bodies were reread for this transfer. The theorem does not apply automatically to rank below five, missing active coefficients, tied cells or arbitrary original joint fibres.

The older compact-uniform critical floor and input-derived ALL-REAL-CRITICAL-PRESENTATION-FINITENESS.md already provide the stated fixed-input critical budgets/finiteness. The remaining effective transcendental-zero problem is not solved here. This increment is an endpoint-uniform critical classification plus a conditional source consequence, not a first fixed-input count theorem or a new historical claim about the classical tools.

## 3. Uniform analytic scaling, including the probability boundaries

Put

    epsilon=-log r, s=-log q, t=s/epsilon,
    c_epsilon=c(exp(-epsilon)), mu_k(epsilon)=sum c_epsilon,lambda*lambda^k.

The equations for c_epsilon say that sum c_epsilon,lambda*exp(-lambda*u) Hermite-interpolates the constant1 at u=0,epsilon,2epsilon, with values1 and derivatives0. Replace those six conditions by confluent divided differences at the repeated nodes0,0,epsilon,epsilon,2epsilon,2epsilon. At epsilon=0 their matrix is the six-row Vandermonde jet matrix, hence invertible. Thus c_epsilon extends analytically to epsilon=0. In particular

    mu_0=1, mu_1=0,
    mu_k(0)=0 for 2<=k<=5,
    mu_6(0)=-product(lambda), K=product(lambda)/720=315/4.

The last identity follows by averaging the degree-six polynomial with roots Lambda: its terms of degrees1 through5 vanish under c_0, and its constant term is product(lambda).

For epsilon>0, F_r(exp(-epsilon*t)) has exact double zeros at t=0,1,2. Its coefficient of epsilon^j is a polynomial in t of degree at most j. For j<6 that polynomial has six zeros counted with multiplicity, hence is zero. At order6 its leading coefficient is K. Therefore

    f_epsilon(t)=F_r(exp(-epsilon*t))/(K*epsilon^6)
        -> G(t)=t^2*(t-1)^2*(t-2)^2,

with an analytic extension at epsilon=0 on every compact real t interval. Every derivative needed below converges uniformly there. Comparing coefficients of t^k also gives

    mu_k(epsilon)=O(epsilon^(6-k)), 2<=k<=5.            (2)

Write kappa_j(p) for Bernoulli cumulants. The Taylor coefficient of s^j in H_lambda(p,exp(-s)) is (-1)^(j+1)*kappa_j(p)*lambda^j/j!. Consequently

    Psi_epsilon(p,t)=L_r(p,exp(-epsilon*t))/(K*epsilon^6)

has an analytic extension through epsilon=0 jointly in p,t, on a neighborhood of p in[0,1] and any compact t interval. For these sets the logarithm arguments are uniformly near1 when epsilon is small. Equation(2) removes every apparent negative power of epsilon. At epsilon=0,

    R(p,t)=4*kappa_2*t^2-12*kappa_3*t^3
             +13*kappa_4*t^4-6*kappa_5*t^5+kappa_6*t^6. (3)

The analytic extension, rather than an unscaled O(p^k) remainder, is essential when p approaches an endpoint much faster than epsilon.

The exact identities L_r(0,q)=L_r(1,q)=0 and, for the unscaled function in (p,t) coordinates, L_epsilon(p,0)=partial_t L_epsilon(p,0)=0 imply

    Psi_epsilon(p,t)=p*(1-p)*t^2*A(epsilon,p,t),         (4)

with A analytic near epsilon=t=0 and p in[0,1]. Formula(3) gives A(0,p,0)=4 for every p, including0 and1. No division at a vanishing p is performed without this analytic factorization.

## 4. Every vanishing-loss critical sequence has q->1

Take any strict critical sequence r->1 with ell=p*(1-q)->0. If q has a limiting value q0<1, then p->0. Analyticity of c_epsilon and the exact p derivative give

    L_p -> F_1(q0),

where F_1(q)=1-sum c_0,lambda*q^lambda. This polynomial has a root of multiplicity six at1. It has seven possible nonzero terms with distinct exponents0,1,3,6,10,15,21, so Descartes' bound allows at most six positive roots counted with multiplicity. Since F_1(0)=1, it is strictly positive on[0,1). The limiting derivative cannot be zero. Thus q->1, hence s->0. This includes q0=0 and uses the actual six-coordinate normal, not a presumed strict endpoint critical exclusion.

The ratio t=s/epsilon is positive. Sections5-7 handle all its possible subsequential regimes and both p endpoints.

## 5. The regimes t->0 and t->infinity are impossible

### 5.1 t->0: keep the exact p*(1-p) factor

Differentiating (4), with epsilon and p fixed,

    partial_t Psi=p*(1-p)*t*(2A+t*A_t).

The last bracket tends uniformly to8 as epsilon,t->0, for ALL p in[0,1]. It is positive in one common neighborhood. For strict p,t>0 this excludes criticality, regardless of the relative rates of p,1-p,epsilon and t.

### 5.2 t->infinity: a coprime cumulant pair

Now s->0 and epsilon/s->0. Expand H in the physical variable s, holding epsilon and c_epsilon fixed. The sixth-order Taylor remainder and its p and s derivatives are uniform on p in[0,1], because all log arguments remain uniformly positive there. Using(2),

    L_p/s^6 -> K*kappa_6'(p),
    L_s/s^5 -> 6K*kappa_6(p),                           (5)

uniformly in p. More explicitly the two errors are bounded by a constant times

    s+epsilon+sum_{j=1}^4 (epsilon/s)^j,

once epsilon/s<=1. Thus there is no hidden division by p or1-p in (5).

With b=1-2p,

    kappa_6(p)=p*(1-p)*(15b^4-15b^2+2)/2.

Its interior zeros have b^2=(15+sqrt105)/30 or (15-sqrt105)/30. Both numbers lie strictly between0 and1 and are distinct. These four interior roots and the two endpoint roots p=0,1 are all simple. Therefore kappa_6 and its derivative have NO common root on[0,1]. Compactness gives a positive lower bound for the norm of this polynomial pair. The uniform limits(5) contradict simultaneous criticality.

Thus a vanishing-loss critical sequence has t bounded away from both0 and infinity, after passing to subsequences.

## 6. Bounded positive t with p->0: exact double zeros control the remainders

Take t in a fixed compact interval [a,b], a>0, and put odds z=p/(1-p). Near z=0 the already-proved joint analytic extension gives

    Psi_epsilon(z,t)
       = z*f_epsilon(t)-(z^2/2)*f_epsilon(2t)
                         +(z^3/3)*f_epsilon(3t)+O(z^4).

This notation composes Psi with p=z/(1+z). It follows either by expanding the two logarithms in the exact identity

    L_r=log(1+z)-sum c_epsilon,lambda*log(1+z*exp(-lambda*epsilon*t))

or by differentiating at z=0. The remainder and its needed z,t derivatives are UNIFORM for small epsilon and t in[a,b], because the epsilon^-6 singularity has already been removed analytically. No uncontrolled infinite-k expansion is used. The critical equations become

    0=partial_z Psi
       = f_epsilon(t)-z*f_epsilon(2t)+z^2*f_epsilon(3t)+O(z^3),
    0=(partial_t Psi)/z
       = f'_epsilon(t)-z*f'_epsilon(2t)+z^2*f'_epsilon(3t)+O(z^3). (6)

Limits of(6) force G(t0)=G'(t0)=0. Since t0>0, only t0=1 or2 is possible.

### 6.1 t->1

Write delta=t-1. For EVERY epsilon, f_epsilon and its derivative have exact double-root factorizations at1 and2. In particular

    f_epsilon(t)=O(delta^2),
    f'_epsilon(t)=delta*(2+o(1)),
    f_epsilon(2t)=O(delta^2), f'_epsilon(2t)=O(delta).

All constants are uniform as epsilon->0. The second equation of(6) gives delta=O(z^2), after absorbing O(z*|delta|). The first then yields

    (partial_z Psi)/z^2 -> G(3)=36>0,

a contradiction. The exact identities f_epsilon(1)=f'_epsilon(1)=f_epsilon(2)=f'_epsilon(2)=0 prevent any epsilon-error term independent of delta from swamping z^2.

### 6.2 t->2

Now delta=t-2 gives f_epsilon(t)=O(delta^2) and f'_epsilon(t)=delta*(8+o(1)). The second equation gives delta=O(z). The first gives

    (partial_z Psi)/z -> -G(4)=-576<0,

again a contradiction. Thus p->0 is impossible in the bounded-positive-t regime.

## 7. Bounded positive t with p->1

The exact complement identity is

    L_r(1-p,q)=L_r(p,1/q),

because c(r).Lambda=0. Equivalently, the scaled function satisfies Psi(1-p,t)=Psi(p,-t). Hence

    partial_p Psi(1,t)=-partial_p Psi(0,-t)=-f_epsilon(-t).

For a limiting t0>0, f_epsilon(-t)->G(-t0)>0. Uniform analytic convergence of the p derivative therefore excludes criticality as p->1. This uses the extension at negative t for the proof; it does NOT admit q>1 as a physical cell or change the source domain.

Sections4-7 prove: every vanishing-loss critical sequence as r->1 has p and t in compact subsets of their strict physical intervals. No p endpoint or t endpoint remains hidden in a balanced-only argument.

## 8. The remaining balanced point, rederived within this candidate

The cumulants appearing in(3) can be written, with b=1-2p,

    kappa_2=p*(1-p), kappa_3=p*(1-p)*b,
    kappa_4=p*(1-p)*(3b^2-1)/2,
    kappa_5=p*(1-p)*b*(3b^2-2),
    kappa_6=p*(1-p)*(15b^4-15b^2+2)/2.

Set x=b*t-1 and v=4p*(1-p)*t^2. The map from 0<p<1,t>0 to x in R,v>0 is a diffeomorphism, with

    t=sqrt((x+1)^2+v), p=(1-(x+1)/t)/2.

Substitution into(3) gives the exact polynomial

    R=(v/8)*(2x^2*(x-1)^2-x*(11x-2)*v+2v^2).

At a stationary point R_x=0 gives

    v=2x*(x-1)*(2x-1)/(11x-1).

The values x=0,1,1/11 cannot solve the original equation with v>0. Substitution into R_v gives

    R_v=-(9/4)*x^2*(x-1)*C(x)/(11x-1)^2,
    C(x)=35x^3-15x^2-x+1.

C has discriminant -9760 and exactly one real root x_*. Since C(-1/4)=-15/64 and C(-1/5)=8/25, x_* lies in(-1/4,-1/5). The associated v_*>0, so there is exactly ONE limiting critical point in the physical domain. Direct interval bounds give

    1/6<v_*<1/3, 1/20<p_*<1/8, 3/4<t_*<1.

At this root R_xv=-v*(22x-2)/8>0. The derivative of R_v(x,v(x)) is positive, since its factor multiplying C is positive and C'(x_*)>0. Differentiating R_x(x,v(x))=0 then gives

    det Hess(R)=-R_xv*d/dx[R_v(x,v(x))]<0.

Thus the limiting critical point is a nondegenerate saddle. IFT supplies a unique nearby actual critical branch for sufficiently small epsilon>0. The Hessian sign is preserved in the physical (p,q) variables by congruence at a critical point and by the positive scale K*epsilon^6. Differentiation continues to hold epsilon/c fixed.

The branch lies inside B_r for small epsilon: r<q and q^2<r are exactly 1/2<t<1, and p_* lies strictly between1/25 and1/6. Any additional critical sequence in B_r would lie in its compact (p,t) closure and have the same limiting point, contradicting local IFT uniqueness. This proves existence/uniqueness in B_r near1.

If assertion3 of section1 failed, critical cells outside B_r could be chosen with r->1 and ell->0. Sections4-7 put them in the balanced regime, and section8 forces their limit to (p_*,t_*), strictly inside B_r. They would eventually lie in B_r, a contradiction. Hence there is a uniform positive complementary loss floor. Rational r0,eta can be chosen by shrinking the neighborhood and the floor.

## 9. Exact rank-five premise, not inferred from the saddle alone

Let v_k=(lambda^k) over the six entries of Lambda, k=1,...,6. They form a basis. Consider the five columns

    Lambda, D(r), epsilon*Lambda*exp(-epsilon*Lambda), H_p, H_t.

For epsilon>0 these have the same rank as Lambda,D(r),D'(r),H_p,H_q, because the third column is -epsilon*r*D'(r) and H_t=-epsilon*q*H_q. In v_k coordinates, the first column is exactly v_1. Remove its row/column from the five-by-five minor using coordinates v_1,...,v_5. For rows k=2,3,4,5, factor out (-1)^(k+1)*epsilon^k/k!. The limiting four-by-four matrix is

    [1, k, kappa'_k(p)*t^k, k*kappa_k(p)*t^(k-1)].

Terms of degree6 lie entirely in v_6. Higher Taylor terms contribute vanishing errors in the first five coordinates after the displayed row rescaling, uniformly in the balanced compact neighborhood. Thus a nonzero limiting determinant proves actual rank at least five.

Second differences eliminate the first two columns and leave the Jacobian in (p,t) of

    S4=kappa_4*t^4-2*kappa_3*t^3+kappa_2*t^2,
    S5=kappa_5*t^5-2*kappa_4*t^4+kappa_3*t^3.

In (x,v) coordinates,

    8S4=2v*x^2-v^2,
    4S5=v*(x+1)*x^2-(2x+1)*v^2.

The determinant of the Jacobian of these two displayed polynomials is

    -2v*(x^4+(3x^2+2x)*v+2v^2).

At x_*,v_*, one has 3x_*^2+2x_*>-5/16 and2v_*>1/3. The bracket is strictly positive, since 2v_*+3x_*^2+2x_*>1/48. The coordinate transformation is nonsingular, so the minor is nonzero. This rederives the rank calculation; it is not a citation to an accepted note04.

The common paired annihilator c(r) annihilates all five physical columns at a critical point. The rank is therefore at most five and, by the minor, exactly five along the weak branch for r sufficiently close to1.

## 10. Finite RCF formulation, with no executed certificate

Every critical equation, Hessian entry and five-column minor is rational in r,p,q; c(r) is rational in r. The box B_r is polynomial. Accordingly the three claims of section1, including the rank premise of section9, are expressible by a finite RCF sentence with rational coefficients and quantified real r,p,q. Positive source denominators may be cleared; denominators of c are retained as nonzero conditions or cleared by squares.

Enumerate positive integer pairs (j,k) by increasing j+k. Set r0=1-2^(-j), eta=2^(-k), and decide the universal sentence for r0<r<1. Its existence/uniqueness assertion quantifies the critical cell in B_r, not a sampled algebraic residue. The hand theorem guarantees success for some pair. Every test is finite; dovetailing does not remain at one j forever. No arbitrary real constant is smuggled in as effective RCF data.

No RCF, root isolation or algebraic checker was executed. This is an effectivity argument for this rational derivative predicate, not a decision procedure for the original exponential/logarithmic presentation equations.

## 11. Varying heads and independent literal multiplicities

Supply a coherent fresh untied COMMON cap-seven normal form

    h=a*Lambda+u*D(r)+sum_j n_j*H(p_j,q_j),
    a,u>0, zero killing, n_j positive integers,

with the actual SAME r and every retained cell critical for c(r). This is a conditional source premise, not an extracted solution of original joint input. An initially countable summable list is allowed. For fixed r>r0 the weak cell has strictly positive ell_r and every other critical cell has loss at least eta. The nonnegative first-coordinate budget therefore already makes the entire retained list finite; this uses min(ell_r,eta), not an assumed uniform integer cap.

All nonweak occurrences, including all repetitions of every other critical type, satisfy

    number_nonweak*eta <= sum_nonweak H_1 <= h_1.

No equal-multiplicity assumption or fixed head is made. There is exactly one possible weak TYPE, but its literal multiplicity is a separate quantity.

If that weak type occurs twice, vary the two copies in opposite directions along a negative vector of its normal Hessian. Their first derivatives cancel. The normal second variation is twice a strictly negative number. The full presentation derivative has rank exactly five: section9 supplies five independent columns, while the common c(r) annihilates EVERY column from every retained head and the drift/residue columns. The paired orientation is the required one: the sparse polynomial F has its six positive zeros counted with multiplicity at1,r,r^2, no others by Descartes, and F(0)=1. Thus F>=0 on(0,1).

The accepted second-order source theorem now applies with its actual hypotheses and implies actual finite-source INTERIOR. This theorem acts on the displayed fresh untied COMMON component. If original joint constraints tie the cell variations to additional hidden components or register parameters, their legality and the same-tuple source correspondence must be proved there; this calculation licenses no componentwise or row-wise refit. A failure of joint source realization alone does not imply nonattainment of this component. Consequently a NONATTAINED form in the exact component source class stated above has weak literal multiplicity at most ONE. Its total retained count is bounded by

    floor(B/eta)+1 whenever B>h_1.                       (7)

This is a conditional hand consequence of the NEW classification/rank proof and the accepted curvature theorem. It is not independently accepted just because the older theorem is accepted. If h_1=-log m_1 with effectively algebraic m_1>0, an integer B with m_1>2^(-B) is computable and satisfies h_1<B. The R(r) residue convention is equivalent after u=w/(1-r)>0; this is an invertible change of parameters for a fixed strict residue, not a new physical law.

Optionally, IF candidate05's lower-endpoint theorem AND the present upper-endpoint theorem pass review, the older accepted compact-uniform floor covers the remaining residue interval. Taking the minimum of those finitely many floors would give a uniform critical-presentation count of the form floor(B/eta_global)+1 for these NONATTAINED cap-seven one-residue positive-drift forms across all0<r<1. This integration is explicitly conditional on both unreviewed increments. It does not assert that every actual source has bounded presentation length or that arbitrary original input has a bounded minimum witness.

## 12. Exact remaining master gaps

| Obligation | Present evidence | Remaining requirement |
| --- | --- | --- |
| Unbalanced r->1 critical regimes | New uniform hand argument, sections3-7 | Independent mathematical review |
| Unique weak type, saddle and rank5 | Re-derived hand argument, sections8-9 | Independent mathematical review; no machine certificate |
| Literal multiplicity consequence | Conditional source transfer, section11 | New hypotheses must be established, with exact flags and fresh untied source semantics |
| Uniform normal-form budget across all residues | Conditional integration only | Review05 and06 and bind the compact provider; no arbitrary-source cap follows |
| Exact arithmetic/negative certificate | OPEN | Decide possible isolated transcendental critical presentations and rule out alternative actual words where required |
| Original JOINT shared-source recognizer | OPEN | Acquire source-complete information from the actual retained input, preserve original IDs/one tuple, handle every admitted cap/flag and INDEPENDENT/BOTH |

The source input equations are joint constraints, not independent scalar fits. Neither (7) nor a census of closure presentations supplies exact attained membership. No endpoint argument here invents a source-size cap, positivity margin, closure=attainment rule or exponential-zero oracle for the full task.

The next sharper branch is the exact-arithmetic/actual-source alternative gap: characterize which finite Nash critical branches admit effective exact tests at algebraic joint input, without presuming algebraic hidden tuples or discarding original shared parameters. That is a mathematical task, not an authorized solver/compiler job. Full biological G3/G4 remain OPEN; no accepted CM/G2 or other ownership scope changes.
