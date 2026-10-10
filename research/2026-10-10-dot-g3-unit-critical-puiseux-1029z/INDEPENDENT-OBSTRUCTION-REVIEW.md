# Independent hand review of the Bernoulli unit-critical Puiseux argument

Reviewer: dot (OpenAI), complementary G3 exact-obstruction lane, 2026-10-10.
Reviewed text: `UNIT-CRITICAL-PUISEUX.md`, SHA256
`c94a4d25f50b49c071cbd92a675dfe1b22edb5e8a13ccc28b5409bd3f9ed0332`.

## Verdict

PASS at the stated hand-proof scope for Candidate Theorem A, Candidate Theorem B, and the supplied-normal positive-loss-floor corollary. I found no mathematical gap in the frozen proof. I also checked the revision diff against the previously reviewed version; it makes the already supplied continuation and coefficient arguments explicit. This is an independent adversarial hand review, not Lean verification, historical novelty review, an executed RCF implementation, or acceptance of a complete G3 procedure.

The complementary exact search also provides a bounded arithmetic control: all 455 reduced ordinary-neutral relations of at most six factors on either side, for Lambda={1,3,6,10,15,21}, have squarefree degree-preserving rational q=2 specializations after removing the simple boundary factor x. The separate search and signed-vector enumeration, rational gcd audit, modular certificates and proof are in `g3-unit-critical-countercurve-20261010-1025z`. This computation is not used in the universal proof.

## 1. Polynomial statement: audited corner cases

1. **Actual source lift.** With x=(1-p)/p and w_0=-sum e_lambda, the quotient product(x+q^lambda)^w_lambda is exactly product f_lambda^e_lambda. The source-coordinate Jacobian is nonzero on 0<p,q<1. A repeated strict factor cannot be created or lost by the denominator x+1.

2. **Nonzero numerator and denominators.** The distinct factors x+q^lambda are pairwise nonassociate irreducibles. Disjoint positive/negative supports make U,V coprime; U-V is nonzero. A component x=-q^lambda cannot lie on the unit locus. The possible x=0 component is simple because its logarithmic derivative is the nonzero Laurent polynomial sum w_lambda q^(-lambda).

3. **Complex branches and projection.** A positive-x-degree irreducible factor gives a nonconstant q projection. A place over q=0 exists on its normalized projective curve. Newton-Puiseux allows a complex nonzero leading coefficient, rational slope, negative slope (x pole), and slopes outside the exponent range. Every such case is retained by the proof.

4. **Off-support leading terms.** T=x partial_x log R first forces E=0. R=1 then forces K=0. Importantly, x^E cancels identically before expansion, so a higher correction to x cannot create an earlier term or alter the first nearest-exponent coefficients. At the smallest positive distance delta, at most one exponent occurs below and one above. Their contributions are A+B to the unit logarithm and A-B to T. At least one is nonzero, and their simultaneous vanishing is impossible over C, not merely over R. One-sided nearest exponents and slopes outside the entire support satisfy the same contradiction.

5. **On-support leading terms.** The leading coefficient a=-1 produces a unique negative-valuation term in T; all other terms are bounded, so no cancellation is possible. For a not in {0,-1}, the derivative equation first excludes E=0 and E+B=0, then forces a=-E/(E+B) to be real. Unit modulus gives the stated signed entropy identity. For two positive inputs, strict superadditivity of t log t follows directly from u log(1+v/u)+v log(1+u/v)>0. Same-sign negative inputs reverse sign. For opposite signs, rearrangement reduces to two strictly positive inputs. Thus the identity is nonzero in every nondegenerate sign case. Complex phases cannot rescue a modulus contradiction.

6. **Vertical components.** A pure-q factor meeting 0<q<1 would identify two monic products with distinct roots -q^lambda and therefore identical multiplicities, contradicting the nonzero relation. Boundary q=0 or q=1 factors are allowed by the theorem and do not contradict its strict-domain conclusion.

No use of ordinary neutrality or equal side count is hidden in these exclusions. Their omission from Theorem A's hypotheses is justified.

## 2. Real-normal statement: continuation and finiteness

The extension is a separate argument; it does not improperly split algebraic coefficients into independent rational differential normals.

The common rational derivative locus has dimension at most one because its p derivative is not identically zero. A smooth strict real critical arc determines a complex irreducible algebraic curve on which both derivative numerators vanish. Its nonverticality follows from partial-fraction uniqueness for distinct real roots -r^lambda. None of x+q^lambda is identically zero on a curve containing a strict positive point.

On the connected compact normalization, deleting finitely many zeros/poles leaves a connected complex Riemann surface. The real-weighted meromorphic differential eta vanishes identically there. Consequently the single-valued real function sum w_lambda log|x+q^lambda| has zero differential and retains its initial value zero everywhere. No choice of branches of complex logarithms is being used to assert a global complex unit identity.

The off-support Puiseux argument is valid with real coefficients. E=0 comes from T; K=0 comes from the divergent logarithmic modulus term. After cancellation, the local holomorphic weighted sum of unit logarithms has zero real part on a COMPLEX OPEN neighborhood of the puncture, not just on the positive real q ray. It is therefore a constant, and its limit zero fixes that constant to zero. This supplies A+B=0 as a complex equality. The equation A-B=0 still comes directly from the rational derivative. Merely knowing Re(A+B)=0 along real q would not suffice, but that weaker argument is not what the draft uses.

On support, the vanishing log|q| coefficient is first forced by F_abs=0; then its constant term is E log|a|+B log|1+a|=0. The derivative forces real a and the entropy contradiction works for arbitrary nonzero REAL E,B,E+B, without integrality.

For the stated finiteness conclusion, the rational critical locus has finitely many semialgebraic connected components. A differentiable function with vanishing ambient gradient is constant along the piecewise differentiable semialgebraic paths in each component. Its zero-score set is therefore a union of entire components. A positive-dimensional such component supplies the forbidden strict real arc; zero-dimensional components are individual points. This argument correctly retains any isolated real points, including ones lying on a complex positive-dimensional algebraic component. Their direct exclusion is unnecessary for the finite-set conclusion.

### Clarifications incorporated in the reviewed revision

- The revision explicitly uses the vanishing complex differential of the normalized holomorphic unit-log sum on a complex punctured neighborhood. This gives A+B=0 complexly and prevents the insufficient real-ray argument.
- In the on-support real case, the revision explicitly cancels the log|q| coefficient before taking the constant term.

## 3. Positive-loss floor and effective supplied-normal bound

Let L=p(1-q). For each positive integer lambda,

0 <= H_lambda <= -log(1-lambda L)

whenever lambda L<1, since 1-q^lambda<=lambda(1-q). Thus H tends coordinatewise to zero whenever L tends to zero, including every allowed boundary approach.

If the full critical locus for a fixed c had loss infimum zero, finitely many semialgebraic connected components ensure a sequence tending to zero loss inside one component. Its constant score must equal zero by the preceding bound. Theorem B makes the zero-score critical locus finite, whose strict loss minimum is positive. This is a contradiction. Empty critical loci are handled separately.

For effectively algebraic c, clearing the known positive denominators yields exact polynomial derivative equations. RCF can test the existence of a strict critical point with L<2^(-k); the proved positive floor ensures eventual emptiness. Beginning at k>=1 keeps the returned epsilon strictly below1 even when the locus is empty. This is a terminating mathematical procedure using an existing RCF oracle, not an executed implementation in this review.

For positive algebraic target pair moment m_1, choose N with (1-epsilon)^(N+1)<m_1. A word having n such supplied-normal critical factors satisfies m_1<= (1-epsilon)^n, because each factor's pair survival is <=1-epsilon and the ordinary scale is <=1. Hence n<=N. This bounds only that supplied-normal critical list, as the draft states.

## 4. Scope retained

The result addresses the exceptional unit-critical curve gate and a fixed-normal count interface. It does not derive a normal from arbitrary input, bound its algebraic complexity across an unknown source fibre, prove exhaustive finite carrier acquisition, or provide a terminating all-core witness/NO procedure. No new observation, hidden-size promise, numerical margin, independent rowwise fit, closed-limit source, or modified original positivity class has been introduced.

The full G3 requirements about arbitrary finite levels and reticulations, original ordered parallel edge occurrences, shared bank/register/static parameters, COMMON versus current-current-lineage INDEPENDENT, and all rival presentations remain outside this two-parameter analytic lemma unless a separate source-faithful reduction establishes them. In particular, this theorem does not invalidate the accepted rational Poisson finite-source NO or attained-boundary YES controls.
