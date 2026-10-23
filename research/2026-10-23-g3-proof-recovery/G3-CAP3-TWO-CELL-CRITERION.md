> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Exact two-cell criterion on the paired COMMON-ordinary face

Authored 2026-10-21. HAND theorem and exact algebraic implementation. This is
a bounded private-word result, not all-input G3 recognition or a source-size
bound. No new Lean candidate has been compiled.

## Interface and physical scope

Use the fresh, unexposed, all-colocated current-root cap-three interface of
`G3-CAP3-INDEPENDENT-COMPRESSION.md`. One physical word and its one parameter
tuple serve COMMON and INDEPENDENT. Write its four no-merger coordinates as

\[
 (C_2,C_3,Q_I,R_I)=(c,c^3,cq,c^3r),\qquad 0<c<1.
\]

The COMMON face equality forces every cell's two arm survivals to be equal:
each natural COMMON cell contributes
`(p x^3+(1-p)y^3)/(p x+(1-p)y)^3 >= 1`, with equality only at `x=y` for a
strict coin. Products equal one only when every factor equals one. This
uses fresh natural original bits; it is not a refresh rule for stored bits.

Put `u_i=1/s_i>1`, `t_i=p_i(1-p_i) in (0,1/4]`. If `A in (0,1)` is the
product of the strictly positive ordinary-passage survivals, then

\[
 c=A/\prod_i u_i,\quad
 q=\prod_i[1+2t_i(u_i-1)],\quad
 r=\prod_i[1+3t_i(u_i^2-1)].
\]

Thus the cost of a word is `U=product u_i < B=1/c`. Identity factors may
be folded into ordinary passages in intermediate closed optimization; a
returned source has strict arms, coins and ordinary passages. Identification
with the complete seven-state forest kernel is the existing HAND result;
native copy/forest/source reflection retains its separate formal suppliers.

## Statement

Define

\[
 f(q)=3q^2-3q+1,
\]

and

\[
 P(a)=(3a^2+1)[-a^2+(6q-1-3B)a+3(2q-1)B]-8ra(a+1).
\]

There is a strict witness with at most two private cells exactly when one of
the following holds:

1. `q=r=1` (zero cells).
2. `q>1`, `2q-1<B`, `r>=f(q)`, and the one-cell inverse
   `u=2(r-1)/(3(q-1))-1` satisfies `u<B`.
3. The three inequalities in item 2 hold, and there is a real `a` satisfying
   `1<=a<=2q-1`, `(a+1)(B+a)>=4qa`, and **`P(a)>0`**.

For a one-cell witness use `t=(q-1)/(2(u-1))`. The constraints ensure
`0<t<=1/4`. The strict sign in item 3 is essential: an optimizer requiring
`A=1` is not a strict positive-bookend witness.

## Necessity and the upper envelope

For one cell write `q_i=1+2t_i(u_i-1)`. Then

\[
 u_i\ge 2q_i-1,\qquad
 r_i=1+\tfrac32(q_i-1)(u_i+1)\ge f(q_i).
\]

The identity

\[
 f(s)f(t)-f(st)=3(s-1)(t-1)(2st-s-t)\ge0
\]

gives `r>=f(q)` for every finite word. Also
`product (u_i+1)/2 <= (product u_i+1)/2`, by the two-factor identity
`(u+1)(v+1)<=2(uv+1)` and induction. Hence `2q-1<B` is necessary.

Fix `q_1 q_2=q`. A two-cell word with cost below `B` can spend its unused
cost in an active cell, keeping `q_i` fixed by decreasing `t_i`. This
strictly increases `r`, and reaches closed cost `u_1u_2=B`. For those fixed
`q_i`, the product of the two affine expressions for `r_i`, with
`u_2=B/u_1`, is a constant plus `alpha u_1 + beta/u_1`, with nonnegative
coefficients. It is convex in `log u_1`; its maximum occurs at an endpoint
where one cell is balanced, `u_i=2q_i-1`.

Taking that balanced cell to have cost `a` gives

\[
 q_1=(a+1)/2,\quad q_2=2q/(a+1),\quad u_2=B/a,
\]

and the envelope

\[
 F(a;q,B)=\frac{3a^2+1}{4}
 \left[1+\frac32\left(\frac{2q}{a+1}-1\right)
                  \left(\frac B a+1\right)\right].
\]

The admissible domain is exactly `1<=a<=2q-1` and
`(a+1)(B+a)>=4qa`. Since `P(a)=8a(a+1)(F(a;q,B)-r)`, any strict two-cell
witness gives the strict quartic condition. A zero-effect endpoint instead
reduces to the one-cell case already covered.

## Constructive sufficiency

After the ordinary and one-cell cases, take an exact algebraic `a` satisfying
the quartic condition. Its endpoints cannot be the witness in this remaining
case: they give at most the one-cell envelope or `f(q)`. Thus `q_1,q_2>1`.
Put `bottom=f(q_1)f(q_2)`.

If `r>=bottom`, keep the first cell balanced and use

\[
 u_1=a,\ t_1=1/4,\quad
 u_2=\frac{2(r/f(q_1)-1)}{3(q_2-1)}-1,\quad
 t_2=\frac{q_2-1}{2(u_2-1)}.
\]

Here `u_2>=2q_2-1` and `a u_2<B`; the second inequality is precisely
`r<F(a;q,B)`. These are strict physical cells.

If `r<bottom`, let `k_0=min(q_1,q_2)`. The continuous balanced-pair
function `f(k)f(q/k)` runs from `f(q)` to `bottom` on `[1,k_0]`.
In fact, writing `h=k+q/k`, its excess over `f(q)` is
`3(q+1-h)(2q-h)`, which increases as `k` moves toward `sqrt(q)`.
The one-cell case has already handled `r=f(q)`. Therefore an algebraic
`1<k<k_0` solves `f(k)f(q/k)=r`. Use balanced costs
`2k-1` and `2q/k-1`. Their product `4q+1-2(k+q/k)` is strictly smaller
than the balanced endpoint cost, which is at most `B`.

For either branch set `A=c product u_i<1`. With `m=n+1` ordinary
passages choose

\[
 a_j=\frac{m-j+jA}{m-j+1+(j-1)A},\qquad 1\le j\le m.
\]

Every passage lies strictly between zero and one and their product is `A`.
Set `s_i=1/u_i` and `p_i=(1+sqrt(1-4t_i))/2`. This constructs one strict
physical tuple for the four requested coordinates. Direct substitution is
the final implementation check; no observation is reconstructed separately.

## Implementation and actual verification

`Cap3TwoCellCertificate.wl` uses the exact algebraic helpers from
`Cap3PrivateWordCertificate.wl`. `Cap3FaceTwoWitness[c,c3,QI,RI]` decides
the one-variable semialgebraic condition, reconstructs a witness, and verifies
all four physical coordinates on that same word using exact RootReduce
differences. It returns the private minimum 0, 1 or 2 for a successful
witness. `NO_AT_MOST_TWO_PRIVATE_CELLS` does not exclude longer words.
Off-face, inexact or unresolved input returns `Failure`, never unrestricted NO.

Actual hosted Wolfram execution passed all 11 controls in
`VerifyCap3TwoCellCertificate.wl`: ordinary, balanced and unbalanced one-cell,
two distinct minimum-two targets, the balanced reconstruction branch, the
strict two-cell frontier, the weak and previously known minimum-three
targets, off-face input and inexact input. Successful cases directly checked
their complete four-coordinate tuple. The hosted pre-evaluation undefined
symbol warnings are retained in the encrypted original result; they were
not reported as clean native Lean compilation.

Encrypted actual algebra/solver receipt:
`[encrypted runtime receipt retained privately]`. The weak-three family has its separate
HAND proof in `G3-CAP3-ARBITRARILY-WEAK-MINIMUM-THREE.md`.

The original G3 endpoint is still open: this theorem neither bounds the
number of arbitrary cells nor covers higher caps, arbitrary original cores,
fixed clocks, exposed controls, or all-input terminating NO.
