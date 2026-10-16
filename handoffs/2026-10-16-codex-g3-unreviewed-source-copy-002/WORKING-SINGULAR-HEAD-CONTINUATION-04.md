# Working continuation: varying singular heads and multiplicities

16 October 2026. PRIVATE working hand derivation by Codex. No independent review, mathematical computation, solver, compiler, or new source adoption. This checkpoints restarted original biological G3 research at the source-handoff boundary; it is not a completed recognizer. Candidate 03 and its private envelope remain unchanged.

## Governing target

Original finite rational/effectively algebraic JOINT input, arbitrary finite positive original source, original IDs, and ONE graph/physical bank/register across every retained row. COMMON, INDEPENDENT and BOTH retain their actual semantics. The following analysis is on a difficult COMMON slot component; it does not replace that target or independently fit hidden moments. Presentation length and minimum witness size are separate.

## 1. Prior already supplying the generic reductions

The following actual source bodies were read again in this continuation, avoiding a false claim to rediscover their conclusions:

- ENHANCED-RETAINED-RANK-CRITERION.md and SUPPLIED-RESIDUE-CRITICAL-COUNT-BOUND.md in research/2026-10-01-sol61-g3-boundary-resume-2124z; independent acceptance G3-ENHANCED-RETAINED-STRATUM-REVIEW.md in research/2026-10-01-sol61-head-audit-1956z. Accepted source pin f2b64d7a60c011dae3a7252f72ddeae7651e7828. Nonattained cap-seven positive-drift, zero-killing, one-residue forms have every retained cell critical for the paired normal c(r).
- ALL-REAL-CRITICAL-PRESENTATION-FINITENESS.md in research/2026-10-10-dot-g3-real-critical-finiteness-1446z, SHA256 52b4b1cba30ebd792b3c8b47c81e071d232c18491c67be634decd79018fa4688. Its accepted earlier providers already give input-derived residue confinement and a retained-count bound for ALL real paired-critical presentations of one fixed algebraic singleton. Finiteness is not an effective census of its possible transcendental isolated solutions or a NO certificate against alternative finite words.
- EFFECTIVE-ENDPOINT-EXCLUSION.md and UNIFORM-CRITICAL-PURITY.md in research/2026-10-06-dot-g3-critical-stratum-compactification-0826z. Do not repackage supplied compact residue bounds as new input acquisition.
- SECOND-ORDER-CRITICAL-EXCLUSION.md in research/2026-10-06-dot-g3-interior-critical-saddle-0942z: accepted original SHA256 c083a88bbb3de9b242ea8445bcaaa49da306160d69834c93263b5306155f2585; independent review cae66f2b4d8d24b0248e4adc06afa8c2fff26fe55d0b5170d65b625e8de55243. At derivative rank five, a negative oriented quadratic direction on the derivative kernel gives actual finite-source INTERIOR. Positive semidefiniteness is not a NO criterion.

The older PAIRED-CRITICAL-CURVATURE-ATTAINMENT.md still has a pending-review header. The intended reuse here instead points to the separately accepted second-order theorem with its EXACT rank-five hypothesis; that hypothesis must be proved, not omitted.

## 2. Balanced drift-endpoint scaling of the actual paired family

Let Lambda=(1,3,6,10,15,21), D_lambda(q)=1-q^lambda and H_lambda(p,q)=-log(1-p+p*q^lambda). Let c(r) be the paired row with sum c=1, c.Lambda=0 and F_r(r)=F'_r(r)=F_r(r^2)=F'_r(r^2)=0, F_r(q)=c(r).D(q).

Set r=exp(-epsilon), q=exp(-epsilon*t), epsilon>0. Partial derivatives in p,t below hold epsilon, hence c(r), FIXED. Differentiating a moving normal path in a head Hessian would be invalid.

The paired linear system is Hermite interpolation of the constant function at 0,epsilon,2epsilon by the six functions exp(-lambda*s). Divided-difference row operations extend the system analytically through epsilon=0. Its limiting matrix is the ordinary Vandermonde jet matrix. Therefore c(epsilon) is analytic at zero and

    sum c(0)=1, c(0).Lambda^j=0 for j=1,...,5.

The old endpoint source already supplies c(0)=(297,-275,154,-54,11,-1)/132; this limit is NOT new here. Lagrange interpolation at the six positive lambda values also gives

    c(0).Lambda^6=-product(lambda),
    K=product(lambda)/720=315/4>0.

For every epsilon, F_r(exp(-epsilon*t)) has double zeros at t=0,1,2. Its coefficient of epsilon^j is a polynomial in t of degree at most j. For j<6 the six prescribed zeros make that polynomial zero. Thus

    F_r(exp(-epsilon*t))/(K*epsilon^6)
        -> G(t)=t^2(t-1)^2(t-2)^2
        =4t^2-12t^3+13t^4-6t^5+t^6.

The quotient has an analytic extension and convergence holds with derivatives on compact t sets.

Write kappa_j(p) for the Bernoulli cumulants, so H(p,exp(-s)) has lambda^j*s^j coefficient (-1)^(j+1)*kappa_j(p)/j!. It follows that

    Psi_epsilon(p,t)=c(r).H(p,exp(-epsilon*t))/(K*epsilon^6)

extends analytically and converges, with derivatives on compact sets, to

    R(p,t)=4 kappa_2 t^2-12 kappa_3 t^3
              +13 kappa_4 t^4-6 kappa_5 t^5+kappa_6 t^6.

This is an actual coupled source derivative limit; no independent row or fitted energy is involved.

## 3. Exact limiting stationary point and saddle

Use the diffeomorphism from 0<p<1,t>0 to x in R,v>0:

    z=(1-2p)t, x=z-1, v=4p(1-p)t^2=t^2-z^2.

The inverse is t=sqrt((x+1)^2+v), p=(1-(x+1)/t)/2. The Bernoulli cumulant polynomials give exactly

    R=v/8 [2x^2(x-1)^2-x(11x-2)v+2v^2].             (E)

At a stationary point R_x=0 implies

    v(x)=2x(x-1)(2x-1)/(11x-1).

The exceptional denominator x=1/11 cannot solve R_x=0; neither x=0 nor x=1 can with v>0. Substitution gives

    R_v(x,v(x))
      =-(9/4) x^2(x-1) C(x)/(11x-1)^2,
    C(x)=35x^3-15x^2-x+1.

C has discriminant -9760<0 and hence one real root. C(-1/4)=-15/64, C(-1/5)=8/25, so its root x_* is exactly specified by that interval and lies below zero. It gives v_*>0. There are no other limiting stationary points in the physical domain.

At this root C'>0. Also R_xv=-v(22x-2)/8>0, and the derivative of R_v(x,v(x)) is positive. Since v'(x)=-R_xx/R_xv, these identities give

    det Hess_(x,v) R =-R_xv * d/dx[R_v(x,v(x))]<0.

The stationary point is a nondegenerate SADDLE. Elementary bounds give v_* in (1/6,1/3), p_* in (1/20,1/8), t_* in (3/4,1). No decimal root or numerical Hessian was computed.

IFT therefore gives a unique nearby actual critical branch p(epsilon),t(epsilon) for sufficiently small epsilon>0. Its physical Hessian in (p,q) is also indefinite: at a critical point, a smooth invertible change of coordinates transforms the Hessian by congruence. The positive K*epsilon^6 scale does not change this.

For any compact balanced regime p in [eta,1-eta], t in [a,b], eta,a>0, all limiting critical points must be the one above. Outside a neighborhood of it, the limiting gradient has positive norm on the compact set; analytic convergence excludes extra critical points. This proves the balanced-regime classification in hand argument, not a classification of all possible endpoint scalings.

## 4. Rank-five condition required by the accepted curvature theorem

It is not enough to find an indefinite 2-by-2 head Hessian. The original derivative block must have rank five. For this branch consider

    [Lambda,D(r),D'(r),H_p(theta),H_q(theta)].

Its common paired annihilator gives rank at most five. Rescale the head q column using t, and use the Vandermonde basis Lambda^1,...,Lambda^6. The leading five-row minor reduces, after removing nonzero factors, to the four-by-four matrix with rows k=2,3,4,5,

    [1, k, kappa'_k(p)t^k, k*kappa_k(p)t^(k-1)].

Quotienting its first two columns by second differences reduces its determinant to the Jacobian of

    S4=kappa_4 t^4-2kappa_3 t^3+kappa_2 t^2,
    S5=kappa_5 t^5-2kappa_4 t^4+kappa_3 t^3.

In x,v coordinates,

    8S4=2v x^2-v^2,
    4S5=v(x+1)x^2-(2x+1)v^2.

The Jacobian determinant of these last two displayed polynomials is

    -2v [x^4+(3x^2+2x)v+2v^2].

It is nonzero at x_*,v_*: x_* in (-1/4,-1/5) gives 3x_*^2+2x_*>-5/16, and v_*>1/6 gives 2v_*+3x_*^2+2x_*>1/48. The bracket is strictly positive. Thus the actual block has rank exactly five for all sufficiently small positive epsilon.

In a positive-drift, zero-killing, one-residue paired-critical normal form, TWO identical retained copies from this branch admit opposite head perturbations. Their first derivatives cancel, while their normal second variations add and can be strictly negative. The remaining critical heads do not increase rank above five; the displayed block already supplies rank five. The accepted second-order theorem then implies actual finite strict-source interior. Consequently a NONATTAINED form has multiplicity at most ONE at this weak saddle type. This conclusion treats literal multiplicities, not just distinct parameter types.

It neither bounds every presentation nor proves that a nearby observed input is NO. In particular the one-cell actual sources from the moving branch have short witnesses; their vanishing head loss is not an unbounded-minimum-count result.

## 5. Stronger endpoint reduction under development; do not import as accepted

A possible upgrade is to prove that every vanishing-loss paired-critical sequence as r->1 eventually enters this balanced branch, leaving a uniform positive loss floor for all other critical cells. The following arguments have been outlined but the complete uniform/source proof is not frozen as a theorem here:

- Vanishing pair loss and r->1 force q->1. If p->0 with q bounded away from1, the p derivative limits to F_1(q)>0.
- If t=(-log q)/(-log r)->0, the analytic quotient Psi/[p(1-p)t^2] tends to4 near t=0, uniformly in p in[0,1]. Its t derivative has a strict sign, excluding criticality.
- If t->infinity while q->1, expansion in s=-log q with epsilon/s->0 gives L_p/s^6 -> K*kappa'_6(p), L_s/s^5 ->6K*kappa_6(p), uniformly in p in[0,1]. The sixth Bernoulli cumulant and its derivative have no common root; its interior zeros come from the distinct roots b^2=(15+/-sqrt(105))/30 with b=1-2p.
- For t in a compact positive interval and p->0, the divided critical equations force t->1 or2. The exact double zeros of the scaled F at1,2 give uniform versions of the old fixed-r rare-root contradictions: at1 the p derivative has positive leading p^2 F(3), at2 negative leading -p F(4).
- Complement symmetry L(1-p,q)=L(p,1/q), from c.Lambda=0, excludes p->1 in a balanced positive t interval.

If fully justified, these would prove existence of rational r0<1 and eta>0 such that all critical cells at r0<r<1 either are the one weak saddle or have loss >=eta. The weak branch can be enclosed by rational SEMIALGEBRAIC inequalities p in(1/25,1/6), r<q and q^2<r. Uniform existence/uniqueness, negative Hessian determinant, rank five and the complementary loss floor would then be finite RCF checks. A fair dyadic search would terminate from the hand theorem, not from a sampled test.

Combined with the multiplicity-one rule, this would give an endpoint-uniform bound floor(B/eta)+1 on retained count in NONATTAINED forms with -log m_1<B. This stronger statement is still WORKING, not discharged in this checkpoint. The r->0 scaling is not handled here. The old endpoint exclusion and fixed-input critical budget remain the accepted tools.

## 6. Exact arithmetic bottleneck is not forgotten

The prior input-only census already handles algebraic residues and the all-real theorem gives a finite set of possible transcendental presentations. Neither computes the isolated transcendental zeros or proves nonattainment against alternative actual words. The new saddle calculation must not be advertised as filling that arithmetic gap.

A further direct-transcendence test is being preserved as an unfinished approach: drift normalization in the pure-residue base gives polynomials T_lambda of degrees 1,4,8,13,19. Their pairwise unordered degree sums are all distinct, making Sym^2(span_Q T_lambda) inject into Q[r]. Thus a direct nontrivial two-by-two multiplicative grid inside that rational log-span is unavailable at a transcendental residue. This appears to block a direct six-exponentials grid shortcut; the argument, precise source reduction and its limits still need a separate written verification. No general transcendence impossibility or hardness theorem is claimed.

## 7. Master and evidence boundary

These are hand calculations on varying singular heads and their independent literal multiplicities, with source-faithful curvature reuse and a checked rank premise. They do not supply source-complete extraction of the original hidden joint tuple, a minimum witness bound, arbitrary-cap/all-flag exceptional coverage, an exponential zero oracle, or INDEPENDENT/BOTH transfer. Full biological G3/G4 remain OPEN.

No mathematical program was run. Local actions were source reads, text preservation and byte/hash metadata only. The inspected older executions remain attributed older evidence; none was replayed. This file is private working source, not independent acceptance or a canonical result.
