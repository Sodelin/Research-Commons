# Independent agent review of the exponential-expression draft

Review date: 15 October 2026. Reviewer: `/root/independent_proof_review`, a separate Codex reasoning agent. This is independent agent review, not external human peer review or formal proof verification.

Reviewed file: `EXPONENTIAL-EXPRESSION-THEOREM.md`.

- Source SHA-256: `ae73c480a112e2e9bda56d5dedc6a54cb7bcfb019f021e402f4cedb5e0638db2`.
- Source Git blob: `6c8256b96063663ae2e220c82801dbc585cfb609`.
- Repository HEAD when inspected: `58a84f0acf2809304363cb4926cee97190f6f422`.
- Line references below refer to that exact source, not a later revision.

## Verdict

Theorem 1 passes this scoped hand review. The normal-form identity criterion, generic-ray argument, algebraic-point zero/sign procedure and rational counterexample search are correct under the stated grammar. No counterexample to those claims was found.

Theorem 2 is a correct conditional corollary once the semantics of partial expressions and the effective encoding of the domain are explicit. The draft should specify how undefined terms behave inside negation and other Boolean connectives, and where graph variables are quantified. These are specification improvements; the conditional decidability result supports either of the concrete first-order semantics described below.

The main-paper fit, compiler coverage, ownership decisions and existing holds were outside this review. They do not follow from these two mathematical statements.

## Theorem 1: checks and details

### Normal form and constant shifts, lines 27–57

Finite expansion is legitimate because all products of exponentials can be replaced by an exponential whose exponent is the sum of the original polynomial exponents. Ordinary polynomial terms are represented with exponent zero. All resulting polynomial coefficients and exponent coefficients remain real algebraic and have effective exact arithmetic.

For a fixed normalized exponent `R`, the coefficients of `A_R` are finite algebraic linear combinations of the distinct numbers `exp(c)`. The required linear independence is exactly the standard Lindemann–Weierstrass statement, including the case `c = 0`. The [Popescu v2 abstract](https://arxiv.org/abs/2306.14352v2) states this form. Thus cancellation between different algebraic constant shifts cannot be silently performed, and the displayed criterion is correct.

The real-algebraic coefficient restriction matters. For example, if an unstructured transcendental coefficient `e` were admitted as a polynomial coefficient, then

\[
e\,e^0-e^1=0
\]

would have nonzero coefficient groups in the proposed criterion. This is outside the stated input language and is not a counterexample to Theorem 1. It is a useful regression boundary against casually extending the coefficient field.

### Generic ray and dominance, lines 59–80

Let `f` be any nonzero real polynomial. Write it as a finite sum of homogeneous parts. At least one part `h` is nonzero, and `f(tv)` cannot vanish identically in `t` when `h(v) != 0`. For a nonzero normalized difference `R-S`, some positive-degree homogeneous part is nonzero. Requiring that part to be nonzero at `v` prevents `(R-S)(tv)` from becoming constant.

This gives finitely many nonzero real polynomials in `v`. Their product is nonzero, so its complement is nonempty and open. Rational vectors are dense in that complement. This also works when the coefficients of `A_R` are transcendental real numbers: the exceptional sets need only be real algebraic sets, not sets defined over the algebraic numbers.

After restricting to such a ray, every pairwise exponent difference is a nonconstant real univariate polynomial. Its eventual sign is fixed by its leading nonzero coefficient. Consequently the finite family has an eventual strict order. After division by the largest surviving exponential, every other term tends to zero, since its exponent tends to minus infinity polynomially and dominates any polynomial factor. A nonzero real polynomial cannot tend to zero as `t` tends to plus infinity. The contradiction is valid.

The ray is a proof device, not an extra numerical subroutine required by the decision procedure. Its existence need not be algorithmically certified before the finite coefficient criterion is applied.

Real analyticity on connected `R^d` justifies moving from identity on a nonempty open box to identity everywhere. This step would not apply to agreement only on a lower-dimensional surface; the draft correctly preserves that boundary.

### Point sign and witness termination, lines 82–91

At any encoded real-algebraic tuple, every evaluated `P_i` and `Q_i` is algebraic. Exact grouping of the evaluated exponents followed by the same linear independence test decides zero, including zeros caused by specialization of polynomial coefficients or collisions of formerly different exponents.

For the nonzero case, algebraic numbers and the real exponential have arbitrarily precise certified rational enclosures. Finite arithmetic preserves effective enclosure refinement. Hence an enclosure whose endpoints have the same strict sign is eventually obtained. The argument is about certified enclosures, not floating-point comparisons.

A nonidentity cannot vanish throughout the supplied open box. Continuity provides an open neighborhood on which its value is nonzero, and that neighborhood contains a rational point. Fair dovetailing therefore eventually finds an enclosure excluding zero.

A simpler equivalent algorithm is available because the algebraic-point zero test is already total: enumerate rational points, apply the exact zero test to each, and refine enclosures only at the first nonzero point. No numerical refinement is then spent indefinitely on an actual zero. Both versions are valid. Neither yields a complexity bound or a practical bound on the search.

## Theorem 2: specification amendments

### State the conjecture and the input encoding

For precision, define real Schanuel as follows: for every finite tuple of real numbers linearly independent over `Q`, the tuple together with its exponentials has transcendence degree at least the length of the tuple over `Q`.

The [Berarducci–Gallinaro v3 introduction](https://arxiv.org/html/2603.08365v3) explicitly states the conditional decidability of the real exponential field under this real form, attributes it to Macintyre–Wilkie, and gives Theorem 14.4 as the completeness result for its recursive axiomatization. The conditional dependency and theorem numbering in the draft are supported. The unconditional restricted model-completeness statement does not supply unconditional unrestricted decidability.

Specify that a supplied domain is a finite formula in the admitted language with effectively encoded algebraic constants. A merely mathematical definable set with arbitrary unnamed real parameters is not an effective input. Algebraic constants are eliminated using their uniquely isolating root descriptions.

### Fix one semantics for undefined expressions

One precise convention is a guarded atomic semantics:

\[
\operatorname{Eq}(E,F)(x):=\exists u,v\,
 (\operatorname{Graph}_E(x,u)\land\operatorname{Graph}_F(x,v)\land u=v).
\]

Use the analogous formula for inequalities, then apply ordinary first-order Boolean connectives to the resulting predicates. Under this convention, an equality with an undefined term is false, and its negation is true. In particular, `not (1/0 = 0)` is true. The assertion `1/0 != 0` must be explicitly defined either as that negation or as the distinct guarded inequality predicate; those two choices differ at undefined inputs.

Another valid convention requires all expressions occurring in a requested Boolean condition to be defined, and then evaluates the Boolean condition. Under that convention, `not (1/0 = 0)` fails the definedness requirement. Both conventions translate effectively, but they do not describe the same predicate. The draft's phrase about usual definedness conditions does not settle this distinction for arbitrary Boolean combinations.

Recommendation: explicitly select guarded atomic semantics for the general first-order language, and offer `all expressions defined AND Phi` when the user wants the latter predicate. For closed-expression sign, return one of undefined, zero, positive or negative, rather than silently assigning a sign to an undefined expression.

### Keep graph variables under their dependencies

Build each graph recursively, with the child graphs present at every operation, including multiplication and exponential. Introduce graph-value existential quantifiers inside the atom and beneath any quantifiers for the atom's free variables. Do not hoist them across universal quantifiers or force all branches of a disjunction to be defined unless the chosen semantics requires it.

For example, the true sentence `for every x, exp(x) > 0` translates as

\[
\forall x\;\exists z\;(z=e^x\land z>0),
\]

not as `exists z, for every x, z = exp(x) and z > 0`. These scoping requirements are routine, but writing them avoids a common error in an executable translation.

The draft's displayed equality-on-domain formula already enforces both expressions' definedness at every point of the domain. It correctly gives vacuous truth for an empty domain. If a nonempty domain is required for an application, add a separate existential nonemptiness condition.

## Safe mathematical extensions

The following follow from the same proof and do not require Schanuel. They are optional corollaries, not claims that an implementation already provides them.

1. **Derivatives.** Every partial derivative remains in the class, since
   \(\partial_j(Pe^Q)=(\partial_jP+P\partial_jQ)e^Q\).
   Consequently equality of any supplied finite collection of derivatives is decidable by the same identity test.
2. **Algebraic polynomial substitution.** Substitution of an algebraic-coefficient polynomial tuple into an admitted expression preserves the class. Thus identity after a supplied polynomial parametrization can be tested on an open box in its parameter space. A chart's geometric coverage must still be established separately.
3. **Polynomial denominators.** Rational-function coefficients with algebraic-coefficient polynomial denominators can be handled for identity on a specified common domain by clearing denominators. If the supplied box avoids the denominator zeros, the original theorem applies directly after clearing them. If domain coverage or total definedness is part of the predicate, it must also be checked. This does not justify exponentiating arbitrary rational functions or allowing arbitrary expression denominators under the same proof.

The theorem remains an identity and algebraic-point sign theorem. It does not, by this argument, decide whether an unrestricted exponential-polynomial expression is positive everywhere or has a real root.

## Actual verification and remaining limits

Performed: exact source hash/blob inspection, line-by-line hand review, two primary-source web inspections, and hand analysis of the coefficient-field and partial-function boundary examples above.

Not performed: SMT jobs, compiler builds, numerical experiments, Lean or other proof-assistant checks, an executable decision procedure, main-paper integration, novelty search, or an external human review. No other project's source, runtime, configuration or ownership was modified. This review changes no compiler, solver, cloud or device hold.
