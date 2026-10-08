# The COMMON additive-log alphabet gate is already closed by the accepted slope cone

Contributor: Codex, original G3 attempt 3, 8 October 2026. **Hand source application of accepted prior; independent root review pending.** This advances the failed complete hardness attempt, not a full G3 decision or impossibility theorem. Earlier frozen attempt files remain unchanged.

## Governing prior and the exact remaining hardness design

The accepted [effective physical log-ray theorem](../../../2026-10-06-dot-g3-actual-ray-realization-0915z/EFFECTIVE-FIXED-SIZE-RAY-REALIZATION.md), Section 6, and its [independent review](../../../2026-10-06-dot-g3-actual-ray-realization-0915z/EFFECTIVE-FIXED-SIZE-RAY-REALIZATION-REVIEW.md) already identify the closed conic hull of actual fresh COMMON duration-log profiles with the increasing discrete-concavity slope cone. Their physical hinge limits and classical tropical/convex geometry are governing prior. This note derives the exact dual equality-case consequence needed by the attempted alphabet enforcement. It does not claim a new cone theorem or historical novelty.

Earlier [rare-factor calculation](../coupled-arithmetic/LOGARITHMIC-ALPHABET-DETECTOR-FAILURE.md) excluded a detector whose first rare coefficient has a strict interior zero. It explicitly left full finite-cell zeros unresolved. The direct hardness design now examined is broader:

* use a finite linear character of the logarithms of actual COMMON spectral moments;
* require it to be nonnegative on **every** freely parameterized strict cell;
* make its endpoint equality zero force every unmarked cell into a useful nonordinary finite alphabet;
* transfer that rule to every original source compatible with the input.

The first three clauses cannot coexist. The all-core observation-transfer clause remains separate and is not assumed below.

## Exact finite-dimensional character criterion

Let 0<lambda1<...<lambdad be the actual finite COMMON exponents (in the original forest compiler, lambdaj=binom(j+1,2)). Let c=(c1,...,cd) be real and **ordinary-neutral**:

    sum_j c_j lambda_j=0.

For a natural unequal-arm cell orient q in (0,1) toward the smaller survival and let p in (0,1) be its natural probability. Set

    phi_(p,q)(lambda)=log(1-p+p q^lambda),
    H_c(p,q)=sum_j c_j phi_(p,q)(lambda_j),
    h_c(a)=sum_j c_j (lambda_j-a)_+.

Claim: the following are equivalent:

    H_c(p,q)>=0 for every strict p,q;
    h_c(a)>=0 for every a>=0;
    h_c(lambda_i)>=0 at every exponent knot i.

Moreover, if these hold and c is nonzero, then

    H_c(p,q)>0 for EVERY strict p,q.                       (1)

The last equivalence uses piecewise linearity, h_c(0)=0, and h_c(a)=0 for a>=lambdad. It gives an explicit polyhedral coefficient cone; no unknown transcendental feasibility test is involved in this character screen.

### Necessity: literal physical hinge limits

Fix a>0 and take q_t=exp(-t), p_t=exp(ta)/(1+exp(ta)), t>0. Every finite t is strict. Then

    phi_(p_t,q_t)(lambda)/t
       = [log(1+exp(t(a-lambda)))-log(1+exp(ta))]/t
       -> (a-lambda)_+-a = -min(lambda,a).

Therefore H_c(p_t,q_t)/t tends to -sum_j c_j min(lambda_j,a), which equals h_c(a) by ordinary neutrality. Global nonnegativity of H implies nonnegativity of h. This is the physical hinge construction of the accepted provider, with sign reversed from duration logs to log moments.

To make each test a literal padded source, choose any positive baseline A<1, choose c0 with sqrt(A)<c0<1, and use E(A/c0^2) B_COMMON(q_t c0,c0,p_t) E(c0). All ordinary edges and both arm survivals are strict; its moment is A^lambda(1-p_t+p_t q_t^lambda). Ordinary neutrality cancels the positive baseline. No boundary factor or fractional number of cells is used.

### Sufficiency and strict equality case

The function phi has phi(0)=0 and

    phi''(a) = p(1-p) (log q)^2 q^a /(1-p+p q^a)^2 >0.

Taylor's formula with integral remainder gives

    phi(lambda)=lambda phi'(0)+integral_0^lambda (lambda-a)phi''(a) da.

After summing against c, ordinary neutrality removes the first term and yields

    H_c(p,q)=integral_0^lambdad h_c(a) phi''(a) da.          (2)

Hence h>=0 implies H>=0. If c is nonzero, h cannot be identically zero: on each interval between distinct exponent knots its derivative is minus the sum of the coefficients at the remaining knots, so an identically zero h successively forces every c_j to vanish. A nonnegative nonzero continuous h is strictly positive on an interval. Since phi'' is strictly positive throughout, (2) proves (1).

This proof also exposes the equality case directly instead of relying only on an abstract cone statement. The convex/hinge duality and source cone are inherited mathematical context, not a new recognition mechanism.

## Actual word and alphabet consequence

For one actual fresh untied/unexposed COMMON word,

    m_lambda=A^lambda product_i (1-p_i+p_i q_i^lambda),

after orienting each unequal factor and absorbing equal-arm factors into A. Its character is additive:

    sum_j c_j log m_(lambda_j) = sum_i H_c(p_i,q_i).

If c is nonzero and the character is globally nonnegative on strict cells, its exact zero forces **no unequal factor at all**. The word's complete capped COMMON kernel is then an ordinary kernel; the same ordinary semigroup identity holds at every arity. Arbitrarily many equal-arm subdivisions do not form a useful discrete alphabet of unequal generators.

For integer c, a zero character is the monomial equality between the positive and negative moment powers. Thus even when an original menu genuinely identifies enough moments to check that equality, this particular globally nonnegative ordinary-neutral detector cannot enforce a nonordinary alphabet. A finite list of such detectors cannot rescue the design. If every coefficient vector is zero, the equality places no restriction; otherwise one nonzero detector already excludes every unequal factor.

This strengthens the earlier rare-zero screen at its declared scope. It does not change the original master or insert a new observation. Static protected coefficients may be held fixed while applying the argument to a genuinely free slot. It does not license deleting a protected or cross-used coin or replacing a correlated register by free marginals.

## Direct whole-attempt outcome and remaining next gate

The protected-bank arithmetic reduction still lacks an all-core backward implication. This consequence removes its last proposed **globally one-sided ordinary-neutral linear log-character** enforcement mechanism, in COMMON as well as the separately established INDEPENDENT barrier. The mechanisms and proofs remain distinct: COMMON admits nontrivial Jensen-type positive characters, whereas the INDEPENDENT signed-time/chart result has a stronger trivial-character conclusion. Only the desired nonordinary zero alphabet is excluded in COMMON.

A genuinely nonlinear/nonlocal detector, a score valid only on a separately proved coupled target fibre, or a discrete encoding not requiring an enforced alphabet remains outside this result. It cannot be called impossible merely because this attempt failed. Conversely, the accepted fresh [fixed-target quotient result](../../../2026-10-08-dot-g3-fixed-target-quotient-check-1346z/B3-FIXED-TARGET-QUOTIENT-CHECK-CANDIDATE.md) rules out a universal finite exact append bisimulation even for one algebraic YES target; it leaves an input-effective bound on ONE initialization witness untouched. The exact NO-certificate and alternative-presentation completeness gates also remain open.

No actual-source undecidability reduction, total original recognizer, algebraic closure replacement, fresh finite-cap diagnostic, execution, solver or compiler is claimed. The next full-proof attempt must tackle one of those remaining global gates rather than resurrect a log-character alphabet or finite exact quotient.
