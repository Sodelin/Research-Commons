> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Exact strict image of paired two-current-root private words

Authored2026-10-22UTC. HAND theorem and exact rational implementation; no
historical novelty or independent mathematical review is claimed. The
existing original two-root source algebra was inspected in full in
G4TwoRootSourceStopping (Commons1138a5, source SHA
b5dd33d135fcb9267ae3297229e51434b5cfd434e08ef89ecacf34affd5e541d).
It supplies INDEPENDENT routing/product/positivity and a conditional rival
envelope; it does not state the paired all-word image proved here.

The scope is one fresh unexposed natural private slot with at most TWO
entering current roots, free strict arm/ordinary survivals and natural coins.
One physical word serves the paired COMMON/INDEPENDENT forest tuple. This
does not determine arbitrary synchronized tensors or higher-cap kernels.

## Complete all-length image

For one cell, with `p=P(parent0)` and `h=1-p`, write

\[
 C=px+hy,\qquad Q=p^2x+h^2y+2ph,\qquad0<x,y,p<1.
\]

For a word of `N` cells and positive ordinary bank `A<1`, the complete
two-root paired kernels have survivals `C_word=A product C_i` and
`Q_word=A product Q_i`. A merged root is absorbing; empty/one-root kernels
are identities. Thus matching these two coordinates matches every forest
coordinate through two roots, with entering subtrees restored opaquely.

**HAND theorem.** The exact finite strict word image is

\[
                         0<C\le Q<1.
\]

Equality `C=Q` has an ordinary zero-cell witness. Every `C<Q` in the strip
has a finite positive witness, using the SAME tuple in both modes.
Well-formed exact targets outside it are excluded for EVERY finite private
length. In particular `C<1,Q=1` is an exact nonattainment NO, despite being
approached by strict finite words. This is private-interface NO, not an
exclusion over arbitrary original core/observation alternatives.

Necessity follows from `Q-C=ph(2-x-y)>0`, positivity and `Q<1` in each
strict cell, together with the same ordinary factor in both products.

## A bare cell's upper boundary and strict constructor

The exact strict bare-cell image is `0<c<1, c<q<U(c)`, where

\[
 U(c)=\begin{cases}(c+2)^2/8,&c\le2/3,\\2c-c^2,&c\ge2/3.\end{cases}
\]

For the upper bound let `d=1-c`, `a=1-x`, `b=1-y` and assume `p>=h` by
arm symmetry. Minimize `1-q=p^2a+h^2b` at fixed `d=pa+hb` on the closed
cube. Loss first fills the smaller-weight arm. If `h<=d`, take `b=1` and
`a=(d-h)/p`; then `q=c+h(2-c)-2h^2`, optimized at `h=(2-c)/4` when
`c<=2/3`, or at the boundary `h=d` otherwise. If `h>=d`, the optimum is
`a=0,b=d/h`, giving `q=1-hd`, again maximized at `h=d`. This proves `U`.
Every upper optimizer uses a closed arm endpoint, so strict cells are below
it. The lower `q>c` is strict and is approached by a rare natural coin.

There is also a direct strict constructor. If `c<q<=(c+1)/2`, choose

\[
 x=y=c,\quad t=(q-c)/[2(1-c)],\quad p=(1+\sqrt{1-4t})/2.
\]

If `q>(c+1)/2`, choose the closed upper point

\[
 (p_*,x_*,y_*)=\begin{cases}
 ((c+2)/4,4c/(c+2),0),&c\le2/3,\\
 (c,1,0),&c\ge2/3.
 \end{cases}
\]

At this fixed coin the equal-arm point has
`q0=c+2p_*(1-p_*)(1-c)<q`. Set `lambda=(q-q0)/(U(c)-q0)` and
`x=(1-lambda)c+lambda x_*`, `y=(1-lambda)c`. Here `0<lambda<1`, so every
physical parameter is strict and the two coordinates equal `c,q` exactly.
For rational input the upper construction is rational. In the lower branch,
rational coins near the equal-arm coin also give strict rational arms by
the two linear coordinate equations; exact dyadic bisection finds one.

Actual Wolfram checks proved the bare upper inequality by real quantifier
elimination and returned zero for the coordinate/interpolation identities.
Those are algebra checks; the arbitrary-length conclusion uses the proof
below and does not follow merely from a fixed-cell elimination.

## Constructing a word for every strict strip point

For `0<C<Q<1`, choose ordinary bank `A=(1+Q)/2`, and put `u=C/A`, `v=Q/A`.
They satisfy `0<u<v<1`. For sufficiently large integer `N`, the positive
roots `c_*=u^(1/N)`, `q_*=v^(1/N)` lie in the strict bare image. An explicit
sufficient choice is

\[
 N>\max\{1,\ 3(1-u)/u,\ (1-u)^2/[u^2(1-v)]\}.
\]

Indeed the geometric-sum identities give

\[
 1-c_*\le(1-u)/(Nu),\qquad1-q_*\ge(1-v)/N.
\]

Hence `c_*>2/3` and `(1-c_*)^2<1-q_*`, so
`c_*<q_*<1-(1-c_*)^2=U(c_*)`. Construct one strict cell for that pair and
use its numerical parameters at `N` DISTINCT fresh sites. Equal parameter
values do not synchronize their natural bits. Factor `A` into `N+1` strict
ordinary survivals using

\[
 a_j=(N+1-j+jA)/(N+2-j+(j-1)A),\quad j=1,\ldots,N+1.
\]

Then the two physical products are exactly the requested `C,Q`. All
coordinates are real algebraic for real-algebraic input, and the usual
positive calendar/rate realization supplies finite positive edge rates.

For rational input, `g3_paired_cap2_word.py` additionally constructs an
ALL-RATIONAL witness suitable for the existing Source engine. It brackets
the positive roots by exact dyadic powers. Once their strict bare-image
neighbourhood is certified, choose rational first-cell coordinates near the
roots and use the exact rational product remainders for the last cell.
Openness ensures both are strict after finite refinement. The same-tuple
bare constructor then supplies rational arms/coins. The final direct product
check is mandatory.

The implementation doubles candidate counts and uses root-interval width
below `(1-v)/(16N)`. The piecewise `U` is increasing and 1-Lipschitz on
`[0,1]`. For `N` above the displayed bound with its last term doubled,
`U(c_*)-q_* >= (1-v)/(2N)`, so this interval test must succeed. No infinite
equality test at an earlier frontier or unproved stopping oracle is used.

## Even this small interface can need exponentially many explicit cells

For a cell write `dc=p(1-x)+h(1-y)` and
`dq=p^2(1-x)+h^2(1-y)`. The exact identity

\[
 dq[(1-x)+(1-y)]-dc^2=(1-x)(1-y)(2p-1)^2\ge0
\]

gives `dc^2<=2dq`. The lumped ordinary bank obeys the same weak bound.
For all `N+1` factors, product telescoping and Cauchy give

\[
 (1-C)^2\le(\sum dc_i)^2\le2(N+1)\sum dq_i
       \le2(N+1)(1-Q)/Q.
\]

Thus every rival private word satisfies

\[
                     N+1\ge Q(1-C)^2/[2(1-Q)].
\]

For rational targets `C=1/2`, `Q=1-1/j`, `j>=3`, this gives
`N>=(j-9)/8`. The constructive root-margin procedure succeeds by a dyadic
count at most `8j`. Their private minimum is therefore `Theta(j)`, whereas
the input bit length is `Theta(log j)`. A constant or polynomial-in-input-
length bound does not hold at this private interface; a total computable
bound and the simple strip decider do hold. No all-core minimum claim follows.

These words have INDEPENDENT pair survival tending to one, so a positive
lower I-anchor alone cannot extend the cap-three FACE bound to arbitrary
unequal-arm paired words. The face assumption is essential there.

## Actual integrated checks and remaining original scope

`verify_g3_paired_cap2_word.py` passed four strict bare constructors, five
paired words, four high-minimum-family controls, four exact exclusions and
two unsupported-input refusals. It then sent three new returned words
through the authenticated original Source constructor, admission checker,
strict calendar, stable native Code layout and COMMON/INDEPENDENT compiler.
All six original readout rows matched exactly. Full actual data/source are
encrypted in `[encrypted runtime receipt retained privately]`, ciphertext SHA256
a04c3642f38c92743c01a01a85340302b32e8d880e8fdd0875d2048b10681d03.
No old suite, native Lean or model job was replayed.

The exact original readouts included two-descendant-slot quartet
discordances `C/3,Q/3` and rooted-event probabilities `C/6,Q/6`. On the
three-descendant slot, quartet probabilities stayed fixed while rooted
events were `C/12,Q/12`. This demonstrates both a legal kernel-coordinate
readout and why that readout cannot be inferred from every coarsening.

The private image can now replace unbounded cap-two word quantification by
one semialgebraic predicate inside a supplied joint core chart. Full original
G3 still needs all higher-cap/paired/tensor interfaces, source-faithful formal
reflection and all-template coverage. Its goal remains open.

The exact universal bare-cell bound and coordinate identities are retained
in `[encrypted runtime receipt retained privately]`. The pair-loss identity, derivative
bound and seven-state quartet projection identity are retained in
`[encrypted runtime receipt retained privately]`, ciphertext SHA256
a847da9221276fb01ae8c5b43efa7e56db77461f6103a9fceca9b814da54478b.
These are symbolic calculations plus the separate HAND proofs above.
