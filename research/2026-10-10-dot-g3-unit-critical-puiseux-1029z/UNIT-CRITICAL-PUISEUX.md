# Candidate: no nonvertical repeated unit factor for the Bernoulli source pencil

Contributor: dot (OpenAI), G3 constructive source-realization lane, 10 October 2026.
Status: revised hand argument submitted for final independent adversarial review. No historical novelty, full G3 recognition, source computation, or Lean verification is claimed. The complementary lane independently owns a bounded counterexample search; it is corroboration only, not this universal proof.

## 1. Exact source gate and claimed scope

At a fixed original natural COMMON cap, let Lambda be any finite set of distinct positive integer exponents (in the original source, 1,3,6,...). Put

    f_lambda(p,q)=1-p+p q^lambda,  H_lambda=-log f_lambda,
    0<p<1, 0<q<1.

For a nonzero rational ordinary-neutral normal e, clear denominators so e is integral and e dot Lambda=0. The prior unresolved unit-critical gate asks whether

    N_e=product f_lambda^(e_lambda positive)
           -product f_lambda^(-e_lambda negative)

can have a repeated irreducible factor meeting the strict square. On its positive unit locus, zero logarithmic gradient is exactly zero gradient of N_e. The source and gate are inherited from [the Oct8 continuation](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/ATTEMPT-3-CONTINUE-HERE.md) and [the unit-critical audit](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-witness-bound/attempt3/UNIT-CRITICAL-POLYNOMIAL-ROUTE.md).

The candidate proves this repeated-factor exclusion, and then gives a separately explicit extension to every fixed nonzero REAL normal's zero-level critical set. Ordinary neutrality is allowed but is not used by the exclusion proof. This is a property of the actual two-parameter source family, not a global additive support inequality.

## 2. Polynomial theorem

Let L be a finite set of distinct nonnegative integers, w_lambda nonzero integers for lambda in L, and write

    U(x,q)=product_(w_lambda>0)(x+q^lambda)^w_lambda,
    V(x,q)=product_(w_lambda<0)(x+q^lambda)^(-w_lambda),
    R=U/V, D=U-V.

Empty products are 1. Suppose at least one w_lambda is nonzero.

**Candidate Theorem A.** D is squarefree as a polynomial in x over C(q), up to a nonzero factor in C(q). In particular, every repeated irreducible factor of D in C[x,q] is a polynomial in q alone. No such pure-q factor has a zero r with 0<r<1.

The last assertion follows directly: if D(x,r) were identically zero, the distinct monic affine polynomials x+r^lambda would have equal multiplicities on both sides. Since r is strictly between zero and one, their roots are distinct, forcing every w_lambda=0.

For the source substitution x=(1-p)/p, one has f_lambda=(x+q^lambda)/(x+1). Add w_0=-sum_(lambda>0)e_lambda and omit any zero coefficient. Then R=product f_lambda^e_lambda. The rational change of variables is nonsingular on the strict square and x+1 is nonzero there. Denominator clearing cannot introduce a repeated strict component. Thus Theorem A gives the original rational-normal gate. The padding identity sum w_lambda=0 and ordinary neutrality sum lambda*w_lambda=0 are exact; Theorem A itself needs neither identity.

### Proof of Theorem A

The polynomials x+q^lambda are irreducible and pairwise nonassociate, so U and V are coprime and D is not zero. If an irreducible positive-x-degree factor G occurs at least twice in D, then on its function field

    R=1,  partial_x R=0.

Neither U nor V vanishes identically on G. The projection q is nonconstant on a positive-x-degree irreducible plane curve, except for a vertical component which would have x-degree zero. On the connected projective normalization, q extends to a nonconstant meromorphic function, hence a surjective morphism to the projective line: its image is closed by properness and is not a point. In particular it has a place above q=0. Newton–Puiseux at that place gives a branch in C((q^(1/m))) for some positive integer m.

First dispose of x identically zero. Such a component can lie in D only if sum lambda*w_lambda=0. At x=0 its logarithmic x derivative is

    sum_lambda w_lambda q^(-lambda),

a nonzero Laurent polynomial because the exponents are distinct. Thus x=0 cannot be repeated. Likewise x identically -q^lambda is excluded by coprimality of U,V: R would have a zero or pole rather than value 1.

On every remaining branch, for some a in C minus {0} and rational kappa,

    x=a q^kappa(1+o(1)).

The valuation notation is formal Puiseux notation. Negative kappa (x tending to infinity), kappa above every exponent, and fractional kappa are all permitted. Put

    T=x partial_x log R
      =sum_lambda w_lambda x/(x+q^lambda)=0.

#### Case I: kappa is not a supported exponent

Separate L_-={lambda<kappa} and L_+={lambda>kappa}. Set

    E=sum_(L_+) w_lambda,  K=sum_(L_-) lambda*w_lambda.

The constant Puiseux term of T is E, so E=0. The exact factorization is

    R=q^K x^E
       product_(L_-)(1+x/q^lambda)^w_lambda
       product_(L_+)(1+q^lambda/x)^w_lambda.

Each parenthesized factor is a formal unit tending to 1. Since R=1 and E=0, its valuation forces K=0. The monomial factor q^K x^E therefore cancels IDENTICALLY; higher Puiseux corrections to x cannot leave a lower-order contribution from it.

Let delta be the least positive distance |lambda-kappa| over L. There is at most one nearest exponent below kappa and at most one above it. Define A=w_lambda*a if the nearest lower exponent has distance delta, and A=0 otherwise. Define B=w_lambda/a if the nearest upper exponent has distance delta, and B=0 otherwise. At least one of A,B is nonzero. Formal logarithms of the displayed units are well defined. Their first possible coefficient at q^delta is A+B. Since R=1, it vanishes.

The coefficient of q^delta in T is instead A-B: a lower exponent contributes x/q^lambda, while an upper exponent contributes 1-q^lambda/x. All other exponents and all higher Puiseux corrections have strictly larger valuation. Thus A-B=0 as well. These two equations force A=B=0, a contradiction. This includes slopes outside the whole support, when just one of the two nearest sides exists.

#### Case II: kappa equals a supported exponent lambda_0

Write B=w_lambda_0 and E=sum_(lambda>lambda_0)w_lambda. If a=-1, the term B*x/(x+q^lambda_0) in T has negative valuation, while every other term is bounded (tending to 0 or to its coefficient). It cannot cancel. If x+q^lambda_0 is identically zero, R was already excluded. Therefore a is neither 0 nor -1.

The leading coefficient of R and constant term of T give, respectively,

    a^E(1+a)^B=1,
    E+B*a/(1+a)=0.

The first equation also requires that R's q valuation vanish; no value for that valuation is assumed in advance. If E=0 or E+B=0, the second equation is immediately impossible because B and a are nonzero. Otherwise it forces

    a=-E/(E+B),  1+a=B/(E+B).

In particular a is real, even though the Puiseux leading coefficient was allowed to be complex. Taking the logarithm of the absolute value in the first equation gives

    E log|E|+B log|B|-(E+B)log|E+B|=0.                 (*)

This is impossible whenever E,B,E+B are nonzero real numbers. To see it, for positive u,v use

    (u+v)log(u+v)-u log u-v log v
      =u log(1+v/u)+v log(1+u/v)>0.

If E,B have the same sign, (*) is the positive or negative of this expression. If they have opposite signs, move the smaller absolute summand to the other side; it is again the positive or negative of the same expression for two strictly positive numbers. Hence its value cannot be zero. Negative a or any possible complex root-of-unity phase cannot repair the contradiction in modulus.

Both cases contradict a repeated positive-x-degree factor. This proves Theorem A. QED, subject to independent review.

## 3. Real-normal extension using logarithmic modulus

**Candidate Theorem B.** For every fixed nonzero real vector c indexed by Lambda, the set

    S_c^0={0<p,q<1: c dot H=0,
                       c dot H_p=0, c dot H_q=0}

is finite. In particular no strict neutral-reaching critical curve exists for any real normal.

This assertion does not split real coefficients into rational differential normals. It is a separate analytic use of the same Puiseux argument.

After x=(1-p)/p, set real w_lambda=c_lambda and w_0=-sum c_lambda, deleting zero entries. The actual logarithmic function, up to the harmless overall sign, is

    F(x,q)=sum_lambda w_lambda log(x+q^lambda)

on the positive real domain. Its two derivatives are rational functions with real coefficients. Their common zero set is semialgebraic and has dimension at most one: the p derivative in the original coordinates cannot be identically zero, since at p=0 its numerator is sum c_lambda(1-q^lambda), a nonzero polynomial for nonzero c.

If S_c^0 contained a positive-dimensional critical component, it would contain a smooth semialgebraic strict real arc on which F=0. Take an irreducible complex algebraic curve C containing a subarc. This is possible because the nonzero gradient numerator bounds the complex common-zero locus by dimension one, and an arc cannot lie in its finitely many isolated points. A polynomial vanishing on the arc vanishes identically on C: a nonzero regular function on an irreducible algebraic curve has only finitely many zeros. Thus both cleared gradient numerators vanish on C. This argument is over C and allows arbitrary fixed real coefficients; it makes no algebraicity assumption on c. A vertical strict curve q=r is impossible: sum w_lambda/(x+r^lambda) would vanish identically in x, contradicting the distinct simple poles and nonzero coefficient vector. No divisor x+q^lambda=0 contains the original positive arc.

On the connected projective normalization of C, delete the finitely many zeros and poles of the meromorphic functions x+q^lambda. The differential

    eta=sum_lambda w_lambda d(x+q^lambda)/(x+q^lambda)

vanishes identically: both ambient rational derivatives vanish on C, and their pullbacks express eta as F_x dx+F_q dq. This is an equality of complex meromorphic differentials even for transcendental real w. Because the coefficients w are REAL, the globally single-valued function

    F_abs=sum_lambda w_lambda log|x+q^lambda|

has differential Re(eta)=0. The punctured normalization is connected, and F_abs equals zero on the original strict real arc. Thus F_abs is identically zero.

Choose a place above q=0 and the same nonzero Puiseux branch x=a q^kappa(1+o(1)). The boundary x identically zero is impossible for a curve containing x>0. A divisor x identically -q^lambda is likewise impossible.

Off support, the rational derivative equation T=0 still forces E=0, with E now real. The expansion of F_abs then forces K=0 from the coefficient of log|q|. After these monomial terms cancel exactly, choose local holomorphic logarithms of the units tending to 1. Their weighted sum has complex differential eta=0, so it is locally constant on a complex punctured neighborhood in the normalization. Its limit at the puncture is zero, so it is identically zero. Thus its complex Puiseux coefficient A+B vanishes, not merely its real part. Together with A-B=0 from T, this is the contradiction in Case I, including complex a and fractional slopes. No arbitrary logarithm-branch phase enters the argument because these unit logarithms are normalized to tend to zero.

On support, a=-1 is excluded by the same unique unbounded term of T. Otherwise the derivative gives a=-E/(E+B), where E,B,E+B must be nonzero real numbers. The expansion of F_abs first forces the coefficient of log|q| to vanish, and then its constant term gives E log|a|+B log|1+a|=0, contradicting the same strict entropy identity. This proves that S_c^0 has no curve.

For finiteness, the common derivative locus has finitely many real semialgebraic connected components. The original smooth function c dot H is constant on each, by piecewise differentiable semialgebraic paths. Its zero-level subset is therefore a union of such components; this also justifies the positive-dimensional-component starting point above without claiming in advance that a logarithmic zero set is semialgebraic. None is positive-dimensional, so only finitely many points remain. This argument retains isolated real points even if they belong to a positive-dimensional complex component. QED, subject to independent review.

## 4. Pointwise critical-loss floor and exact original limit

**Candidate corollary.** For each fixed nonzero real c there exists epsilon(c)>0 such that every strict critical cell satisfies p(1-q)>=epsilon(c), unless the critical locus is empty. If c is supplied effectively real-algebraic, such a positive rational epsilon is computable.

Indeed, a contrary sequence of critical cells with p(1-q) tending to zero has a subsequence in one of the finitely many connected critical components. On that component c dot H is constant, while 0<=H_lambda<=-log(1-lambda*p*(1-q)) tends to zero for sufficiently small loss. Its constant is zero. Theorem B says that the zero-level critical locus is finite, and a finite set of strict cells has positive loss minimum, a contradiction.

For supplied algebraic c, clear the positive denominators of the actual derivative equations. RCF decides whether a strict critical point has loss below 2^(-k). The proved positive floor makes this search terminate; any returned dyadic lower bound is exact. Given a positive algebraic target pair moment m_1, choose N with (1-epsilon)^(N+1)<m_1. A retained critical-factor list for that supplied normal has at most N members, since actual factors have pair survival at most 1-epsilon and ordinary positive passage only decreases the product. Empty critical loci require no retained factors.

This would strengthen the inherited supplied-normal count interface, including its algebraic unit-level branch. It does NOT supply the normal from an arbitrary finite input, bound the normal's degree/height, classify alternative presentations or singular residues, or turn a critical presentation into NO. The floor depends on c; the accepted weak-cell controls as c varies still rule out a cap-only uniform floor. The full original fibre may hide its kernel coordinates. Original shared parameters/banks/registers, arbitrary finite levels and hidden sizes, ordered parallel parent occurrences, all rival cores and INDEPENDENT chronological prefix/suffix normals remain untouched. General G3 stays open.

## 5. Prior and verification boundary

The Oct1 [neutral-accumulation theorem](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-01-sol61-g3-boundary-resume-2124z/NEUTRAL-ACCUMULATION.md) already excludes q tending to one and the killing corner for a fixed normal. The Oct8 accepted finite carrier catalogue and full-value-space interface are also prior. None is being re-proved as a new source theorem here. The proposed new step is the above Puiseux-at-q-zero exclusion of a zero-level critical algebraic curve, using the paired leading coefficients and the nonunit entropy value.

Newton–Puiseux, normalization of an algebraic curve, connectedness after deleting finitely many points, partial fractions, and the elementary logarithmic inequality are classical. Historical priority for this particular binomial pencil theorem has not been assessed. At writing, tool work in this lane was source retrieval, text construction, and confirming existing Python/SymPy availability; no symbolic search, source compiler, source realization, RCF, Lean or installation was executed. Independent proof review is required before publication or use as an accepted provider.
