> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Arbitrarily weak three-cell words can require three cells

Authored 2026-10-21. HAND private paired-kernel theorem. All parameters below
can be rational. This refutes the proposed local three-weak-to-two rule;
it does not refute every cost-dependent bound or decide original G3.

Use `G3-CAP3-TWO-CELL-CRITERION.md`, its equal-arm coordinates, and its
closed two-cell envelope `F(z;q,B)`. COMMON equality `C3=C2^3` forces equal
arms in every strict competing fresh private word; competitors' coins remain
free. A bound on the closed envelope therefore excludes every strict
competitor with at most two cells at this interface.

## A concrete exact example

Take three balanced cells with costs

\[
 (u_1,u_2,u_3)=(11/10,11/10,1000001/1000000)
\]

and ordinary bank `A=1-1/10^15`. Put `U0=product u_i`, `c=A/U0` and

\[
 q=882000441/800000000,\qquad
 r=857477286214643107/640000000000000000.
\]

The target is `(c,c^3,cq,c^3r)`. Three strict cells with any positive
ordinary-passage factorization of `A` attain it. Exact Wolfram elimination
found no `z` satisfying the two-cell envelope domain with `F(z;q,1/c)>=r`.
The new solver separately returned `NO_AT_MOST_TWO_PRIVATE_CELLS`.
An additional exact rational check verified `delta<=delta0` and
`L*(U0/A-U0)<g` from the uniform proof below, so the concrete example also
has that analytic certificate with its actual supplied strict bank.
Consequently the private paired minimum is exactly **three**. Neither check
is an all-core lower bound or a new native Lean execution.

## Uniform construction with all three costs arbitrarily close to one

Fix rational `u>1`, write `alpha=(u-1)^2`, and choose `delta>0` below the
explicit bound below. Use balanced cell costs `u,u,1+delta`. Define

\[
 U0=u^2(1+\delta),\quad
 q=(u+1)^2(2+\delta)/8,\quad
 r=(3u^2+1)^2(4+6\delta+3\delta^2)/64.
\]

At first optimize two cells at closed cost `U0`. For `z>=1` put

\[
\begin{aligned}
 D(z)&=1-2u-u^2-z-2uz+3u^2z+2z^2,\\
 E(z)&=1-6u-3u^2-3z-6uz+9u^2z,\\
 H(z)&=2u^2(u+1)^2(3z^2+1)-(3u^2+1)^2z(z+1).
\end{aligned}
\]

Direct polynomial expansion gives the exact identity

\[
 F(z;q,U0)-r=\frac3{64z(z+1)}
 \left[-(z-u)^2(4D(z)+2\delta E(z))+\delta^2H(z)\right].
\]

The four compact identities used in this proof were all checked exactly
by hosted Wolfram: this identity, the two expansions immediately below,
and the expansion of `H` about `u`. Those checks supplement the HAND bounds.

Writing `v=z-u`, we have

\[
\begin{aligned}
 D(z)&=2\alpha+(3u^2-2u+3)(z-1)+2(z-1)^2\ge2\alpha,\\
 E(z)&=6\alpha-8+3(3u+1)(u-1)(z-1)\ge-8,\\
 H(z)&=-M+H_1v+H_2v^2,
\end{aligned}
\]

where

\[
 M=u(u+1)\alpha(3u^2+1)>0,\quad
 H_2=-3u^4+12u^3-1,\quad
 H_1=2uH_2-(3u^2+1)^2.
\]

Choose any rational `0<delta<=delta0`, where

\[
 \delta_0=\min\left\{\frac\alpha4,\ 1,\
 \frac\alpha{1+|H_2|},\ \frac{2\alpha M}{1+H_1^2}\right\}>0.
\]

These choices give `4D+2delta E>=4alpha`,
`delta^2 |H2|<=alpha`, and `delta^2 H1^2<=2alpha M`.
Young's inequality

\[
 \delta^2 H_1v\le\alpha v^2+\frac{\delta^4H_1^2}{4\alpha}
\]

bounds the braced numerator above by

\[
 -2\alpha v^2-\delta^2M/2<0.
\]

This is a uniform strict exclusion, not a numerical optimizer estimate.

## Restoring strict ordinary passages

Set `Z=2q-1>1`. On the entire possible envelope interval `1<=z<=Z`, the
preceding bound gives the uniform gap

\[
 F(z;q,U0)-r\le-g,\qquad
 g=\frac{3\delta^2M}{128Z(Z+1)}>0.
\]

The envelope is affine in its budget and

\[
 0\le\partial_B F(z;q,B)
 =\frac{3(3z^2+1)}{8z}\left(\frac{2q}{z+1}-1\right)
 \le L=\frac{3(3Z^2+1)(q-1)}8.
\]

Choose rational `epsilon=g/[4(1+L)]`, set `B=U0+epsilon`, `c=1/B` and
`A=U0/B<1`. Then `F(z;q,B)-r<=-g+L epsilon<0` on the entire interval,
including every feasible two-cell envelope point. The supplied three cells
and strict ordinary bank `A` attain `(c,c^3,cq,c^3r)`. Thus their private
paired minimum is exactly three.

For any rational threshold `eta>1`, choose rational `1<u<eta` and then
`0<delta<=delta0` with `delta<eta-1`. Every supplied cost lies in `(1,eta)`.
This proves the arbitrarily weak version with an explicit rational recipe.

## Consequence and limits

A possible upper-bound proof cannot simply delete one cell from every
three-cell block whose arms are sufficiently weak. The exact cost slack and
attainment boundary matter even very near ordinary behavior. This result
does not show unbounded private length at a fixed `c`, does not establish
arbitrarily large weak-cell minima, and does not exclude an input-effective
one-witness bound. Original G3 remains open.

Actual weak-example and factorization receipts:
`[encrypted runtime receipt retained privately]` and
`[encrypted runtime receipt retained privately]`. The final four-zero identity check has
receipt `[encrypted runtime receipt retained privately]`; the five exact rational
concrete-example checks have receipt `[encrypted runtime receipt retained privately]`.
`VerifyCap3WeakMinimumThree.wl` contains both reproducible computations.
