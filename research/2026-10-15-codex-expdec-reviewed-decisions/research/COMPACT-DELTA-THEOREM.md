# Unconditional bounded decisions for nested exponential expressions

Contributor: Codex, EXPDEC theorem task. 15 October 2026.
Status: hand-derived specialization of established delta-decision methods;
independent review and finite arithmetic controls are recorded separately.

This result permits arbitrary finite exponential nesting without Schanuel's
conjecture. Its output distinguishes exact falsity from truth after a stated
numerical relaxation. Exact truth at a zero margin is a different question.

## Input and meaning of a decision

Let each variable range over a supplied nonempty closed rational box.
Constants are effectively real algebraic. Terms are finite expressions built
from variables, constants, addition, subtraction, multiplication and exp.
There is no fixed bound on finite nesting depth or expression size.

Formulas use atoms f >= 0, conjunction, disjunction and finitely many
existential or universal quantifiers over these boxes. Each f is an admitted
term. Write f = 0 as (f >= 0 and -f >= 0). Write f <= 0 as -f >= 0.
All atomic comparisons in this theorem are weak. Negation must not be silently
replaced by a weak comparison at the boundary.

Define the real robustness value r of a closed formula recursively:

| Formula | Robustness |
| --- | --- |
| f >= 0 | f |
| phi and psi | min(r(phi), r(psi)) |
| phi or psi | max(r(phi), r(psi)) |
| exists x in K, phi | max over K of r(phi) |
| forall x in K, phi | min over K of r(phi) |

Compactness and continuity make every displayed extremum attained. Induction
therefore proves phi is true exactly when r(phi) >= 0. This statement would
need modification for strict atoms or a noncompact quantified domain.

For rational delta > 0, let phi^delta replace each atomic f >= 0 by
f >= -delta. Keep the same Boolean operators and quantified boxes. Since
every min, max and extremum commutes with adding one common constant,

    r(phi^delta) = r(phi) + delta.

## Theorem 3

There is a terminating unconditional algorithm returning one of:

- **FALSE:** the original closed formula phi is false;
- **TRUE_DELTA:** the relaxed formula phi^delta is true.

Both outputs can be permissible on the overlap where the original is false
and its relaxation is true. TRUE_DELTA alone does not certify original exact
truth. Given the additional promise |r(phi)| >= delta, an exact TRUE/FALSE
decision is also computable by the same finite construction.

No polynomial running time or practical grid size is asserted.

## Explicit finite construction and proof

Use the maximum norm on the product of all quantified boxes. For each term t
compute rational B_t >= 0 and L_t >= 0 such that |t| <= B_t and t is
L_t-Lipschitz throughout that product. One elementary recursive construction
is:

| Term | Magnitude bound | Lipschitz bound |
| --- | --- | --- |
| algebraic constant c | any rational B_c >= |c| | 0 |
| coordinate x_j | max absolute endpoint | 1 |
| u + v or u - v | B_u + B_v | L_u + L_v |
| u v | B_u B_v | B_u L_v + B_v L_u |
| exp(u) | U(B_u) | U(B_u) L_u |

Here U(b) is any effectively obtained rational upper bound for exp(b).
For example U(b) = 3^(ceil(b)+1) works for b >= 0, using e < 3.
These are finite computable bounds even for deep nesting, although they can
be enormous. The derivative bound for exp and the mean value theorem justify
the final row.

Let L be the maximum atomic L_t and q the maximum number of quantified
blocks along a branch of the formula syntax. Min and max of functions with
common Lipschitz bound L retain that bound. Taking an extremum over a fixed
compact box also retains L in the remaining free variables: compare the same
quantified point before taking the extremum in both directions.

For each quantified box construct a finite rational h-net contained in that
box. Replacing one true extremum by the corresponding finite min/max changes
its value by at most L h. This holds for existential maxima and universal
minima alike. Replacing all quantifiers gives total error at most q L h:
induct on syntax, adding L h at each quantifier and taking the maximum
inherited error at each Boolean node.

Choose a positive rational h satisfying

    q L h <= delta/8.

If q L = 0, any finite nonempty contained nets suffice. At the finitely many
leaf evaluations, compute rational approximations of each term with absolute
error at most delta/8. Algebraic numbers and exp are effectively approximable
to any requested error; evaluating a fixed finite expression preserves this
property. Min/max are nonexpansive in the maximum norm, so numerical errors
through the entire finite evaluation tree remain at most delta/8.

Consequently the computed rational rhat satisfies

    |rhat - r(phi)| <= delta/4.

If rhat >= -delta/2, return TRUE_DELTA. Then
r(phi) >= rhat-delta/4 >= -3delta/4 > -delta, so phi^delta is true.
Otherwise return FALSE: r(phi) <= rhat+delta/4 < -delta/4 < 0.
Every computation is finite, proving termination and soundness.

Under the margin promise |r(phi)| >= delta, the sign of rhat is the exact
sign of r(phi), proving the exact promised decision result. QED at hand level.

The construction is an explicit grid specialization of the bounded
delta-decidability theory of Gao, Avigad and Clarke. Their work handles a
broader computable-function language and is the prior method, rather than a
novel general decidability discovery. See the
[primary paper](https://arxiv.org/abs/1204.6671) and
[author-hosted proceedings text](https://www.cs.cmu.edu/~sicung/papers/lics2012.pdf).

## Guarded division and logarithms

The same argument extends when every relevant denominator u has a supplied
certified rational bound |u| >= m > 0 throughout the full product domain, and each
logarithm argument has u >= m > 0 there. These are hypotheses to verify,
not assumptions inferred from a few grid values.

For reciprocals take B_(1/u)=1/m and L_(1/u)=L_u/m^2; handle a quotient by
multiplication. For log(u), B_log(u)=max(B_u,1/m) is a rational magnitude
bound on the positive range [m,B_u]; use L_log(u)=L_u/m. Each term is then defined,
computable and uniformly Lipschitz on the complete domain. Positive-base
powers exp(v log(u)) follow under the same lower-base guard.

Without these guards, poles and undefined logarithms can invalidate both
the modulus and the formula's intended interpretation. The theorem does not
treat undefined expressions as numerical residuals.

## Fixed source chart corollary

Suppose a supplied finite chart maps every parameter tuple beta in a
nonempty compact rational box K to one admitted original physical source.
Assume all protected parameter relations, physical constraints and shared
register/ID requirements hold exactly by construction of that chart.
Suppose the complete supplied finite response vector F(beta) is expressible
in the admitted term language, with any log/division guards certified.

For algebraic observations y_1,...,y_m define

    phi := exists beta in K,
           AND_j [F_j(beta)-y_j >= 0 and y_j-F_j(beta) >= 0].

Then Theorem 3 returns either:

- FALSE: no source in this supplied chart realizes all observations exactly;
- TRUE_DELTA: one source in this same chart has
  max_j |F_j(beta)-y_j| <= delta.

The quantifier over beta is outside the entire conjunction. Independent
parameter fits for individual rows would give a different assertion.
Only response residuals are relaxed. Physical admission and protected
equalities stay exact because they are built into every chart point, rather
than inserted as relaxable residual atoms.

In this existential-only fitting case, retain the rational grid tuple beta
attaining the computed maximum. Its exact minimum atomic residual is at
least rhat-delta/8, since only the leaf evaluation error applies at that
specific tuple. On TRUE_DELTA this is at least -5delta/8. The same certified
leaf enclosures therefore provide a concrete tuple and residual bounds
inside [-delta,delta], rather than merely a nonconstructive existence claim.

This is a fixed-chart result. It supplies neither complete chart generation
nor a bound on rival source size. A bounded exclusion cannot be relabelled
as original all-size G3 NO or finite-INDEPENDENT G4 forcing. Even inside a
chart, TRUE_DELTA does not establish exact source attainment. For equality-only
fitting, r(phi) = -min_beta max_j |F_j(beta)-y_j| <= 0. Every exact fit has
margin zero, so the positive-margin exact-decision promise excludes those
exact YES instances; it is not a route to general exact source recognition.

The relaxation depends on the written residuals and their units. Replacing
f >= 0 by 100f >= 0 leaves exact truth unchanged but changes the permitted
error in the original units under a common delta. Fix residual scaling as
part of the input contract before comparing conclusions.

## Verification boundary

The hand proof establishes the finite construction. Separate SMT checks can
test the rational inequalities used for its output threshold and expose
shared-tuple or guard mistakes. They do not establish the exp approximation
bound, Lipschitz construction, whole-grid coverage or the all-input theorem.
No delta-decision engine or biological chart provider is claimed implemented
by this document.
