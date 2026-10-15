# Decision theorems for finite exponential expressions

**Draft for Nolan, 15 October 2026.** Contributor: Codex, phone theorem task.
These results give an unconditional identity decision theorem, a conditional
exact decision theorem for arbitrary finite nesting, and an unconditional
bounded decision theorem with an explicit numerical relaxation. The exact
main-paper receiver is awaiting Dot's binding through the user-selected
gateway; a retained compiler application is audited separately. These are
applications of established methods, with scoped independent agent reviews
and executed checks linked below. Historical novelty and external human
peer review are not claimed.

| Effective input and question | Decision result |
| --- | --- |
| Algebraic polynomial coefficients and exponents; identity on an open box or sign at an algebraic point | Exact terminating decision, unconditionally |
| Explicitly algebraic constants with arbitrary finite exponential nesting; general first-order real predicates | Exact terminating decision conditional on real Schanuel |
| Finite nested terms with certified domains; compact-box quantified weak-comparison formulas and positive delta | Unconditional delta decision with the stated overlap semantics |
| Coefficients supplied only by computable approximation programs; exact zero/sign/constant identity | No total exact algorithm, even with rational-valued coefficient promises |

## Unconditional polynomial exponent identity theorem

Let \(A=\overline{\mathbb Q}\cap\mathbb R\), with each algebraic number
encoded by an integer polynomial and a rational isolating interval.
An admitted expression in \(d\geq1\) real variables is any finite expression
built using addition, subtraction and multiplication from \(A[x_1,\ldots,x_d]\)
and terms \(\exp(Q(x))\), where \(Q\in A[x_1,\ldots,x_d]\).
There is no bound on the finite number of terms, variables or polynomial
degrees. Exponentials inside exponents are outside this first class.

**Theorem 1.** There is a terminating algorithm which, for any two admitted
expressions \(E,F\), decides whether they agree on a supplied nonempty open
rational box \(U\subset\mathbb R^d\). When they disagree, it can return a
rational point \(a\in U\) and a certified rational interval excluding zero
that contains \(E(a)-F(a)\). It also decides the sign of an admitted expression
at every supplied real-algebraic point. The witness point can be found in a
finite rational grid whose size is computed from the input polynomial
degrees, as specified below; no unbounded search over candidate points is
needed.

**Normal form.** Expand products and combine exponentials to obtain

\[
H(x)=E(x)-F(x)=\sum_{i=1}^{N}P_i(x)e^{Q_i(x)}.
\]

Write \(Q_i=R_i+c_i\), with \(c_i=Q_i(0)\) and \(R_i(0)=0\).
For each distinct pair \((R,c)\), compute exactly

\[
B_{R,c}(x)=\sum_{i:R_i=R,\ c_i=c}P_i(x)\in A[x].
\]

Then the complete identity criterion is

\[
\boxed{\quad H|_U\equiv0
\quad\Longleftrightarrow\quad
B_{R,c}\equiv0\text{ for every }(R,c).\quad}
\]

**Proof and finite witness bound.** Grouping by \((R,c)\) is exactly grouping
identical full polynomial exponents \(Q=R+c\). Remove zero grouped
coefficients. If no term remains, the identity is established by finite
algebra. Otherwise write the remaining terms as \(P_i e^{Q_i}\), with
distinct \(Q_i\) and nonzero \(P_i\), and choose one coefficient \(P_*\).
The polynomial

\[
W=P_*\prod_{i<j}(Q_i-Q_j)
\]

is nonzero because every factor is nonzero over the algebraic coefficient
field. A valid total-degree bound is

\[
D=\deg P_*+\sum_{i<j}\deg(Q_i-Q_j).
\]

A nonzero polynomial of degree at most D in each variable cannot vanish on
the entire tensor product of D+1 distinct coordinates per variable. Prove
this by induction on the number of variables: the univariate root bound
forces each coefficient polynomial to vanish on the remaining grid, then
apply the induction hypothesis.

Choose those coordinates rationally inside each interval of U. Among at
most \((D+1)^d\) grid points there is a point a with W(a) nonzero. It can
be located by exact algebraic evaluation of the factors, without expanding
their product. At this point all Q_i(a) are distinct algebraic numbers and
P_*(a) is nonzero. Lindemann–Weierstrass implies
\(\sum_i P_i(a)e^{Q_i(a)}\ne0\). Thus a surviving grouped term precludes
identity on U and supplies the desired rational witness.

The empty product is one. Single-term and D=0 cases therefore use the same
proof with a one-point grid when appropriate. A sharper coordinate bound
uses D_j = deg_(x_j) P_* + sum_(i<k) deg_(x_j)(Q_i-Q_k), giving at most
product_j(D_j+1) candidates. These bounds count candidate points; they do
not bound the bit cost or numerical precision needed for a sign enclosure.

At an algebraic point, the evaluated expression is a finite sum
\(\sum_j b_j e^{a_j}\), with algebraic \(a_j,b_j\). Group equal \(a_j\).
Lindemann–Weierstrass decides exact zero by testing whether all grouped
coefficients vanish. Otherwise certified interval approximations converge
to a nonzero number, so refinement eventually decides its sign.

At the rational witness just constructed, refine its certified enclosure
until it excludes zero. This terminates by the proved nonzero value.
All remaining operations are effective algebraic arithmetic.
\(\square\)

For example,

\[
e^{x^2+2x}e^{-2x}-e^{x^2}=0
\]

is certified by combining its polynomial exponents. In contrast,

\[
e^{x^2+\sqrt2}-e^{x^2+1}
=e^{x^2}(e^{\sqrt2}-e)
\]

has two different algebraic constant shifts in the same \(R=x^2\) group
and is a nonidentity. It is positive at every real point by monotonicity.

## Conditional decision theorem for arbitrary finite nesting

Use finite expressions generated from algebraic constants, real variables,
\(+,-,\times\), and \(\exp\), with arbitrary finite nesting depth. Permit
division and \(\log\) with their usual definedness conditions; interpret
\(a^b\) for a positive base by \(\exp(b\log a)\). Arbitrary real constants
given only by numerical approximations are outside this input language.

**Theorem 2, conditional on real Schanuel.** Every first-order sentence about
these expressions is decidable. In particular, one can decide definedness,
equality and sign of closed expressions, equality throughout a definable
domain, and existence of one shared real parameter tuple satisfying any
supplied finite Boolean combination of equations and inequalities. A domain
is supplied as a finite formula in this language with encoded algebraic
parameters; an arbitrary unnamed definable set is not an effective input.

Here real Schanuel means: for any finite tuple of real numbers linearly
independent over the rationals, the tuple together with its exponentials
has transcendence degree at least the tuple length over the rationals.

For partial terms, fix guarded atomic semantics. An equality or inequality
is false if one of its terms is undefined; ordinary Boolean connectives are
then applied to these predicates. Thus the negation of an undefined equality
is true. A guarded inequality is a distinct predicate and remains false when
undefined. If the intended question requires every appearing term to be
defined, conjoin those definedness conditions explicitly. Closed-expression
sign classification returns undefined, zero, positive or negative.

**Proof.** For each syntax node introduce a value variable and its graph
equation, recursively including the graphs of all child terms. An
exponential node gives \(z=e^u\). A division node gives
\(v\ne0\) and \(zv=u\), together with definedness of both children. A log
node gives \(u>0\) and \(e^z=u\). These recursive graph formulas express
the partial functions without treating undefined values as equal. Quantify
each atom's graph variables inside that atom, beneath its free-variable
quantifiers. Do not hoist value variables across a universal quantifier or
require unused disjunction branches to be defined.

Replace each algebraic constant by its uniquely isolated polynomial root.
Translate the requested predicate to a first-order sentence in the ordered
real field with exponential. For example, equality on a domain \(D\) means
that both expressions are defined there and

\[
\forall x\,[D(x)\Rightarrow
\exists u,v\,(\operatorname{Graph}_E(x,u)\land
\operatorname{Graph}_F(x,v)\land u=v)].
\]

Under real Schanuel, apply decidability of that theory, due to Macintyre
and Wilkie. Berarducci and Gallinaro provide a later axiomatization route
to the same conditional conclusion. The translation is finite and effective.
\(\square\)

This is a corollary of the cited conditional decision theorem. Removing its
conjectural hypothesis for unrestricted first-order real-exponential truth
would require a result beyond the established theorem used here. The
unconditional model-completeness result for a restricted exponential theory
does not remove that hypothesis.

## Unconditional bounded decision with numerical relaxation

**Theorem 3.** For finite nested exponential terms, weak comparison atoms,
conjunction/disjunction and finitely many quantifiers over supplied nonempty
compact rational boxes, a terminating unconditional algorithm can return
either exact falsity of the original formula or truth of its delta-weakening,
for any supplied rational delta > 0. Each weak atom f >= 0 is weakened to
f >= -delta. Under a supplied positive robustness-margin promise, the same
construction decides exact truth. Guarded log/division/positive-base powers
are permitted when uniform positive domain bounds are certified.

The [full proof and fixed-source-chart corollary](research/COMPACT-DELTA-THEOREM.md)
give explicit Lipschitz bounds, a finite-grid error budget and the output
threshold. For a source chart, one parameter tuple remains shared by every
observation, and only response residuals are relaxed. Protected physical
constraints remain exact by chart construction. A TRUE_DELTA result alone
does not certify exact attainment. This is a specialization of established
delta-decision methods, independent of Schanuel.

## Exact decisions with computable coefficient programs

**Theorem 4.** If coefficients are supplied by programs returning certified
rational approximations to arbitrary precision, no total algorithm decides
whether exp(c)-1 is zero for all valid inputs, even when c is promised to be
rational and lie in [0,1/2]. Exact sign and constant-function identity are
likewise undecidable for that representation.

The [proof and representation boundary](research/COMPUTABLE-COEFFICIENT-BOUNDARY.md)
give a uniform halting reduction. This richer program input is essential;
the result does not prove undecidability of the explicitly algebraic finite
language in Theorems 1 and 2 or of original finite-input G3.
The [independent coefficient-boundary review](reviews/INDEPENDENT-COEFFICIENT-BOUNDARY-REVIEW.md)
checks the uniform approximation promise and the reduction.

## How this connects to Research Commons

The [source-pinned compiler audit](research/COMMONS-COMPILER-BRIDGE.md)
traces the actual retained manuscript, PROOFS.md Section 4.5 Theorem 8, and
its `metric_law.py` implementation. It finds finite sums of constants times
exponentials of affine functions of all merger times, with complete ranked
history/calendar coverage in its positive constant-rate model. This compiler
uses no spectral decomposition or integration of hidden merger times.

**Application corollary, hand-derived.** Equality of the complete rooted
labeled calendar-metric genealogy laws of two supplied networks in that
same dated binary, positive constant-rate, mode-correct COMMON/INDEPENDENT
model remains decidable when their ages, rates and inheritance probabilities
are effectively real algebraic. Retain the same contemporaneous sampled
labels sampled at age zero in one common calendar origin, retain strict
chronology, and verify the required source admission.

Exact algebraic ordering constructs the common calendar partition. Finite
event updates preserve algebraic coefficients, intercepts and slopes.
Theorem 1 decides each cell-density identity; the positive finite-rate model
assigns zero mass to fixed calendar boundaries and simultaneous mergers,
and its positive ancestral rate gives eventual completion. Thus the finite
comparison covers the full law. A negative answer can supply a ranked
history and rational interior merger-time tuple with a certified nonzero
density difference. Continuity then gives an open region of disagreement.

The retained Python API uses `Fraction` and remains rational-only. This is a
mathematical extension, not an implemented algebraic API. Different models
with forced mergers, atoms, singular strata or integrated hidden transitions
require their own coverage and expression-class arguments; this source audit
does not establish those transfers.

Theorem 2 can decide a supplied finite real-exponential feasibility formula
under its hypothesis. It supplies neither a finite formula covering arbitrary
source size nor a terminating all-size NO search. The existing Commons
exponential-proof-certificate result already distinguishes arithmetic
decidability from source-specific invariant coverage. That distinction is
retained here: general G3 and finite legal INDEPENDENT G4 forcing stay open.

The exact statement to insert into the main paper must be selected after
Dot identifies the intended manuscript, grammar and predicate. This draft
does not select a new biological model, adopt source code or release any
compiler hold.

## Sources and verification

- Classical dependency: Lindemann–Weierstrass. A modern primary exposition is
  [Popescu, 2023](https://arxiv.org/abs/2306.14352v2).
- Conditional dependency: [Berarducci and Gallinaro,
  version 3](https://arxiv.org/html/2603.08365v3), Introduction and Theorem 14.4,
  with attribution there to Macintyre–Wilkie. The Commons certificate note
  used version 1 and its different theorem numbering; those numbers should
  not be silently transferred to version 3.
- Retained application: [rational fixed-state calendar-law comparison](https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/communications/2026-09-30-astra-joint-law-1744z-delivery.md).
- Bounded decision prior: [Gao, Avigad and Clarke, 2012](https://arxiv.org/abs/1204.6671).
- Existing logic/source boundary: [exponential proof certificates and source
  coverage](https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/research/2026-10-09-dot-full-attempt-wave-0542z/g3-certificates/EXPONENTIAL-PROOF-CERTIFICATES-AND-SOURCE-COVERAGE.md),
  inspected Git blob `a11bff90e34a97ef59af0c85816aecc30484804d`.

The [independent agent review of the first draft](reviews/INDEPENDENT-PROOF-REVIEW.md)
supports Theorem 1 and recommends the explicit partial-term semantics now
included in Theorem 2. The
[finite-witness review](reviews/FINITE-WITNESS-BOUND-REVIEW.md) checks the
subsequent constructive proof and degree-based grid bound. The
[bounded-decision review](reviews/INDEPENDENT-DELTA-REVIEW.md)
checks the core proof of Theorem 3. Review pins identify the exact revisions
read; they do not automatically cover subsequent edits. The
[SMT evidence](verification/smt/README.md) records 19 bounded native controls,
including ten UNSAT answers with proof terms, eight SAT countermodels
independently replayed with exact rational arithmetic, and one genuine
resource-limited UNKNOWN. Those controls are distinct from the hand proofs
and application corollary. Thirteen parser regressions separately check
outcome classification; they are not native proof jobs.

Verification level: hand argument and source reading, with scoped independent
agent review and separately recorded finite SMT controls. No universal
executable decision engine, Lean proof or biological solver acceptance is
claimed. Current-source navigation was checked at Commons commit
`c3f9e5b60e83719902da8636dfa0fd208a2d41b4`.
