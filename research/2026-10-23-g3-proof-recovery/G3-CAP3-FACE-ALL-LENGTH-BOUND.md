> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# An input-effective word bound on the paired cap-three ordinary face

Authored 2026-10-21. New HAND theorem, not independently reviewed or checked
in Lean. It concerns the fresh private paired cap-three kernel on
`C3=C2^3`; original G3 on arbitrary cores, higher caps and menus remains open.
The proof does not use a source-size or complete-exclusion premise.

## The bound

Use the coordinates of `G3-CAP3-TWO-CELL-CRITERION.md`:

\[
 (C_2,C_3,Q_I,R_I)=(c,c^3,cq,c^3r),\quad 0<c<1,
\]

and physical equal-arm cells `u_i>1`, `0<t_i<=1/4`, ordinary bank `A<1`:

\[
 c=A/\prod u_i,\quad
 q=\prod[1+2t_i(u_i-1)],\quad
 r=\prod[1+3t_i(u_i^2-1)].
\]

Let `B=1/c`, and let `K` be the least positive integer such that
`(4/3)^K>=B`. Set

\[
                    M(c)=\max\{4,K+2\}.
\]

**HAND theorem.** If any finite strict private word realizes these four
coordinates, then a strict word with at most `M(c)` cells realizes the same
coordinates on one tuple. Its cost can be no greater than the supplied
word's cost. Thus its ordinary bank remains strictly below one.

The bound is deliberately conservative. In particular the arbitrarily weak
minimum-three examples have `M(c)=4`, and are consistent with this theorem.
The older unbounded-minimum family has rapidly increasing `B`; it is also
consistent. This is a one-witness bound, not a bound on all word lengths.

## Compact optimization at a supplied finite length

Put `q_i=1+2t_i(u_i-1)` and

\[
 R_i=1+\tfrac32(q_i-1)(u_i+1).
\]

Fix the supplied word's finite length `n`, ratio `q>1` and cost `U<B`.
In the closed semialgebraic set

\[
 u_i\ge1,\quad 1\le q_i\le(u_i+1)/2,\quad
 \prod u_i\le U,\quad \prod q_i=q,
\]

maximize `product R_i`. This is an ordinary compact finite-dimensional
optimization: each `u_i<=U`. There is no optimization over an infinite union.
The maximum is at least the supplied `r`.

Every maximizer spends the full cost `U`: increasing an active `u_i` with
`q_i>1` increases its `R_i`. A factor `q_i=1,u_i>1` wastes cost; moving its
cost into any active factor strictly increases the objective. Consequently
all inactive factors have `q_i=u_i=1` and can be deleted.

At most one active factor is unbalanced, `u_i>2q_i-1`. Indeed, hold the
`q_i` fixed and transfer logarithmic cost between two such factors. Each
term of the logarithmic objective is

\[
 \log[1+\tfrac32(q_i-1)+\tfrac32(q_i-1)e^{x_i}],\quad x_i=\log u_i,
\]

strictly convex in `x_i`. A two-sided interior cost transfer cannot be a
local maximum. Every other active factor is balanced, `q_i=(u_i+1)/2`.

## At most two balanced strengths, with the weaker one occurring once

For balanced factors define

\[
 b(x)=\log[(e^x+1)/2],\qquad
 d(x)=\log[(3e^{2x}+1)/4],\qquad x>0.
\]

Hold the possible unbalanced factor fixed. Among the balanced variables,
both `sum x_i` and `sum b(x_i)` are fixed. If they have at least two distinct
strengths, these two constraint gradients are independent, since

\[
 b'(x)=u/(u+1),\quad d'(x)=6u^2/(3u^2+1),\quad u=e^x.
\]

Lagrange multipliers give `d'(x_i)=lambda+mu b'(x_i)`. As a function of
`a=b'(x) in (1/2,1)`, the left side is

\[
 J(a)=6a^2/(4a^2-2a+1).
\]

It is strictly concave on this interval. To check the sign without a
numerical plot, its first derivative expressed in `u` is

\[
 h(u)=\frac{12u(u+1)^2}{(3u^2+1)^2},\qquad
 h'(u)=\frac{-12(u+1)(3u^3+9u^2-3u-1)}{(3u^2+1)^3}<0
\]

for `u>1`. A strictly concave graph meets a line in at most two points.
Thus there are at most two distinct balanced strengths.

If they are `w<u`, the weaker one cannot occur twice. The secant slope
`mu` lies strictly between `J'(b'(w))` and `J'(b'(u))`. Therefore
`d''-mu b''` is positive at `w`. A tangent vector adding to one repeated
`log w` and subtracting from another preserves both constraints to first
order, and has positive second variation of the Lagrangian. The gradients
are independent, so the constraint set is a smooth local manifold and this
contradicts the second-order necessary condition for a maximum.

Accordingly the balanced part is either a single repeated strength, or
one weaker factor and a repeated stronger strength. If fewer than three
balanced factors exist, the eventual count is already at most three.

## Three identical weak balanced cells cannot occur at a maximizer

For three balanced factors of the same strength `u`, put

\[
 q_*=(u+1)^3/8,\quad r_*=(3u^2+1)^3/64,\quad U_*=u^3.
\]

A single factor of cost `U_*` and ratio `q_*` is feasible:

\[
 (U_*+1)/2-q_*=3(u-1)^2(u+1)/8>0.
\]

Its resulting triple ratio is `1+(3/2)(q_*-1)(U_*+1)`. The exact identity

\[
 1+\tfrac32(q_*-1)(U_*+1)-r_*
 =\frac{3(u-1)^3(u+1)^2(7-5u)}{64}>0
\]

holds for `1<u<=4/3<7/5`. Replacing those three factors by this one preserves
their cost and pair ratio and strictly increases the triple objective.
Two vacant identity positions keep the construction within the original
fixed `n`-factor optimization. This contradicts maximality.

Thus, if the repeated balanced strength is at most `4/3`, it occurs at
most twice. Including the possible weaker balanced factor and the possible
unbalanced factor gives at most four active factors. If the repeated strength
is larger than `4/3`, its multiplicity is bounded by the cost:
`(4/3)^k < U < B <= (4/3)^K`, so `k<K`. Adding the same two exceptional
factors is safely covered by `M(c)` above. The all-equal balanced case uses
the same triple replacement or the same cost bound and requires no
Lagrange-multiplier regularity assumption.

We have obtained a maximizer with at most `M(c)` active factors and ratio
`r_max>=r`, without assuming the supplied length was bounded.

## Returning exactly the requested ratio, not just a larger one

For every word, `r>=f(q)=3q^2-3q+1`, as proved in the two-cell note.
Starting at the bounded maximizer, decrease its possible unbalanced `u_i`
to `2q_i-1`, keeping its `q_i` fixed. Cost and triple ratio decrease
continuously. All factors are now balanced.

Choose a factor of largest `q_i`. Merge each other factor into it by
continuously increasing the larger factor's ratio and decreasing the other
to one, keeping their product `P` fixed. Let `s` be their ratio sum; it
increases toward `P+1`. Their balanced cost is `4P+1-2s`, and their triple
ratio is

\[
 f(P)+3(P+1-s)(2P-s).
\]

Both decrease during this merge. At a ratio of one, delete that identity
factor. This gives a continuous path of kernels, each with at most `M(c)`
physical active cells and cost at most `U`, ending at the single balanced
factor with ratio `q` and triple ratio `f(q)`. The intermediate value theorem
produces exactly the supplied `r` between `f(q)` and `r_max`.

All retained factors have `u_i>1` and `0<t_i<=1/4`; identities fold into
ordinary passages. Set `A'=c product u_i <= cU<1` and use the strict
telescoping ordinary-passage factorization from the two-cell note. This
restores a strict shared physical tuple and proves the theorem.

## Recognition consequence and verification boundary

For exact real-algebraic input on this interface, compute `K` by exact
comparisons of rational powers with `1/c`, then decide one finite real-closed
field formula with `M(c)` possibly inactive cells:

\[
 u_i\ge1,\quad 1\le q_i\le(u_i+1)/2,\quad
 \prod u_i<1/c,\quad \prod q_i=q,\quad
 \prod[1+\tfrac32(q_i-1)(u_i+1)]=r.
\]

Inactive cells are absorbed into ordinary passages. A sampled solution
gives `t_i=(q_i-1)/(2(u_i-1))` for each active cell; the same direct four-
coordinate check used by the two-cell solver certifies its reconstructed
tuple. Real-algebraic sampling exists whenever this algebraic formula has
a real solution. Invalid coordinates and the ordinary zero-cell case are
handled before this formula.

This is a terminating mathematical recognition algorithm for this private
paired face, conditional only on the HAND proof above, not a claim that a
large hosted elimination has completed. The exact two-cell fast path is
already implemented and passed its 11 controls. Wolfram additionally checked
the derivative and triple-improvement identities exactly, the two necessary
signs by quantified real elimination, and the earlier failed middle-cost
trial formulas. Those failures are retained, not used as evidence of gain.
The exact actual results and authenticated admission/finite-code source
supplement are encrypted in `[encrypted runtime receipt retained privately]`.
`VerifyCap3FaceWordBoundAlgebra.wl`
contains the final exact symbolic and quantified checks.

`Cap3FaceWordBound.wl` now implements the exact bound, finite-formula builder
and all-length consumer, reusing the existing two-cell fast path and direct
physical-word verifier. A supplied seed is only a directly checked positive
certificate. Without one, exact elimination is used. A caller's timeout is
UNKNOWN/Failure, never NO. Every all-length result exposes HAND_THEOREM as
its bound evidence and keeps GeneralG3Closed false.

Actual hosted controls passed: the weak-three example's bound four, its
three-cell seed's direct four-coordinate check and padded finite formula,
the exact power control c=1/2 giving K=3/bound five, the ordinary fast path,
and a simple all-length exclusion via the finite formula. Encrypted receipt
`[encrypted runtime receipt retained privately]`; reproducible authored controls are in
`VerifyCap3FaceWordBound.wl`. No hard unseeded three-cell elimination was
claimed completed. The theorem's general completeness rests on the HAND
optimizer/count/path proof, not those specified numerical cases.

Remaining work: independent mathematical review of that argument; difficult
practical elimination; native source/current-root/copy/calendar reflection
and the existing writer hold; extension beyond this face and cap. None
supplies unrestricted original G3 NO termination.
