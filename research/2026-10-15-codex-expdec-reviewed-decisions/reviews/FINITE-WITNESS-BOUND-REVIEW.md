# Independent review of the finite rational witness bound

Date: 15 October 2026. Reviewer: `/root/independent_proof_review`, a separate Codex reasoning agent. Hand review only; no external human review, proof-assistant verification or historical novelty claim.

The reviewed proposal is the root agent's supplied replacement proof for Theorem 1: group by full exponent polynomial, multiply one nonzero grouped coefficient by all pairwise exponent differences, and use a finite rational tensor grid to obtain a Lindemann–Weierstrass witness.

For context, the existing theorem source inspected before replacement was `EXPONENTIAL-EXPRESSION-THEOREM.md`, SHA-256 `4d0209f9cbfb7152709481f4194499146496c31ea6b25eedcdc74d8d4c2c63b8`, Git blob `cf8329bc2e13bb8fbc982bcdf5bb9e7b369fdd27`, at repository HEAD `b72886fed188a8adb7db5a50ba3ad44b44fcb47d`. This review covers the explicit proposal restated below, not an uninspected later edit.

## Verdict

The replacement proof and witness-point bound are correct. They can replace the generic-ray and analytic-continuation proof entirely for the stated algebraic-coefficient grammar. They also replace the unbounded rational-point enumeration by a finite, explicitly bounded collection of exact polynomial point checks.

There is no resulting fixed bound on the numerical precision required to produce the final nonzero sign enclosure. Numerical refinement remains adaptive and terminates because the selected value is already proved nonzero.

## Exact statement and proof

Expand the admitted expression difference and combine equal **full** exponent polynomials:

\[
H(x)=\sum_{i=1}^{s}P_i(x)e^{Q_i(x)},
\]

where the `Q_i` are pairwise distinct in `A[x_1,...,x_d]`, `A` is the field of effectively encoded real algebraic numbers, and all zero grouped coefficients have been removed.

If `s = 0`, the expression is identically zero. Otherwise choose one nonzero grouped coefficient `P_*` and put

\[
W(x)=P_*(x)\prod_{1\leq i<j\leq s}(Q_i(x)-Q_j(x)).
\]

Every factor is a nonzero algebraic polynomial. The polynomial ring over `A` is an integral domain, so `W` is nonzero. Its total degree is

\[
D=\deg(P_*)+\sum_{i<j}\deg(Q_i-Q_j).
\]

An effectively computed upper bound for this quantity also suffices. There is no need to expand the product `W` to evaluate whether one of its values is nonzero: test the selected coefficient and every exponent difference separately.

Let the supplied open rational box be

\[
U=\prod_{j=1}^{d}(a_j,b_j).
\]

Choose any `D+1` distinct rational coordinates in each interval and form their Cartesian product `G`. For finite rational endpoints, one explicit choice is

\[
S_j=\left\{a_j+\frac{k}{D+2}(b_j-a_j):
1\leq k\leq D+1\right\},
\qquad G=\prod_j S_j.
\]

All coordinates lie strictly inside the interval. If the input convention permits an unbounded open interval, first select a nonempty bounded rational subinterval and use the same construction there.

A nonzero polynomial of degree at most `D` in each individual variable cannot vanish at every point of a tensor grid with `D+1` distinct coordinates per variable. To verify the lemma, regard the polynomial as a univariate polynomial in the final variable. If it vanishes at all grid points, fixing the other grid coordinates gives a univariate polynomial with more roots than its degree, so each of its coefficient polynomials vanishes on the smaller-dimensional grid. Induction on the number of variables makes every coefficient polynomial zero. This contradicts nonzeroness.

Total degree at most `D` implies degree at most `D` in every variable. The lemma therefore yields a point `q` in `G` with `W(q) != 0`. At that point,

\[
P_*(q)\ne0,\qquad Q_i(q)\ne Q_j(q)\quad(i\ne j).
\]

The coefficients `P_i(q)` and exponents `Q_i(q)` are algebraic, because the point is rational and the polynomial coefficients are algebraic. The exponent values are distinct, and at least the selected coefficient is nonzero. Lindemann–Weierstrass consequently gives

\[
H(q)=\sum_i P_i(q)e^{Q_i(q)}\ne0.
\]

This is exactly the usual algebraic linear-independence form of that theorem; the [Popescu v2 abstract](https://arxiv.org/abs/2306.14352v2) states the relevant form.

Thus a nonempty active grouped sum has a nonzero rational evaluation inside **every** supplied nonempty open rational box. Conversely, an empty active sum is zero everywhere. This proves the complete identity criterion directly, without needing real-analytic uniqueness or an asymptotic ray.

## Constructive algorithm and bound

All candidate checks require only exact evaluation, zero comparison and polynomial arithmetic over the effective algebraic field:

1. Group identical full exponent polynomials and delete zero coefficient groups.
2. If there are no active groups, report identity.
3. Otherwise choose `P_*`, compute `D`, and generate the stated finite grid.
4. At each candidate, test whether `P_*(q)` and every `Q_i(q)-Q_j(q)` are nonzero.
5. At the first point passing all these tests, use certified exponential and arithmetic enclosures to refine the value of `H(q)` until its rational interval excludes zero.

Step 4 finds such a point after at most

\[
|G|=(D+1)^d
\]

candidate points. No exponential approximation is needed to choose it. Step 5 terminates by the established nonzeroness and effective approximation. The bound counts point candidates; it is not a bit-operation, algebraic-degree, memory, running-time or sign-separation bound.

Grouping by `Q` is equivalent to the old draft's grouping by the pair `(R,c)` with `Q=R+c` and `R(0)=0`: that decomposition is unique. Replacing the grouping presentation therefore does not change the identity criterion.

## Edge cases challenged

- **No active group:** report the zero identity directly. There is no `P_*` or need to define a degree for the zero polynomial.
- **One active group:** the pair product is the multiplicative identity one, so `W=P_*`. The grid lemma finds a point where the coefficient is nonzero.
- **Degree zero:** `W` is a nonzero constant. One rational coordinate per dimension suffices, and the candidate bound is one. This includes the single nonzero constant-coefficient term case.
- **Constant but distinct exponents, or constant exponent differences:** each difference is a nonzero degree-zero factor. It imposes no additional degree cost, and it never vanishes at a candidate point.
- **Some other grouped coefficients vanish at the chosen point:** harmless. Lindemann–Weierstrass requires at least one nonzero coefficient, which `P_*` supplies.
- **Exponent collisions elsewhere:** harmless. The point-selection polynomial explicitly prevents collisions at the selected witness.
- **Zero exponent polynomial:** allowed as one of the distinct `Q_i`; it introduces no special case after grouping.
- **Real-algebraic rather than rational coefficients:** allowed. The grid lemma holds over any field containing the distinct rational grid coordinates, and exact algebraic evaluation provides the required tests.

The algebraic coefficient representation remains essential. The argument does not work merely from approximation-program access to arbitrary computable coefficients, because its exact polynomial zero tests and the linear-independence hypothesis would no longer be available in that form.

## Optional tighter grid

A coordinate-specific version is also valid. Define

\[
D_j=\deg_{x_j}(P_*)+\sum_{i<k}\deg_{x_j}(Q_i-Q_k).
\]

Then take `D_j+1` rational coordinates in dimension `j`. The same interpolation induction gives a candidate bound `product_j (D_j+1)`, which is at most `(D+1)^d`. Coordinates absent from `W` need only one sample. Choosing a coefficient of smaller degree may further reduce the conservative bound. These are optional refinements; the proposed uniform total-degree bound is already sound.

## Verification boundary

Performed: exact inspection of the pre-replacement theorem source, independent proof reconstruction, and hand examination of the listed edge cases. The polynomial-grid lemma is proved above rather than inferred from finite examples.

Not performed: source theorem edits, executable witness construction, numerical runs, SMT jobs, compiler builds, tool installation, staging, commits or proof-assistant checks. No novel-result claim or biological/compiler/G3 implication follows from this review. Final integrated wording should carry its own source pin.
