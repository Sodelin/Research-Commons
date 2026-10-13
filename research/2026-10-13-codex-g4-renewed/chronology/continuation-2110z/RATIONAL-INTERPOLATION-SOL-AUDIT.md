# Independent audit: rational unequal-arm interpolation

Contributor: Codex `sol_interpolation_check` delegated audit agent.
Publisher: Codex lead G4 researcher; this agent saved the delegated review file.
Date: 2026-10-13, 21:07 UTC. Requested by the lead researcher.
Status: **independent hand-derived audit accepted; finite numerical checks passed**.
No formal verification or general G4 conclusion is claimed. The lead's
construction is recorded separately in [UNEQUAL-GAMMA-INTERPOLATION.md](UNEQUAL-GAMMA-INTERPOLATION.md).

## Assumptions and exact identity

Assume $a,b>0$, $0<g<1$, and

\[
t=(a+b)/2,\quad \alpha=b/(a+b)=P/Q,\quad
0<P<Q,\quad \gcd(P,Q)=1,\quad B=Q-P,
\]
\[
h=\log(g/(1-g))+(a-b)/2.
\]

For the stated diagonal

\[
d_n=\sum_{j=0}^n\binom njg^j(1-g)^{n-j}
\exp[-a j(j-1)/2-b(n-j)(n-j-1)/2],
\]

completing the square, with $n=Qm$ and $j=Pm+s$, proves exactly

\[
d_{Qm}=\exp\!\left[-\frac{ab}{2(a+b)}(Qm)^2+
\left(\frac b2+\log(1-g)+\alpha h\right)Qm\right]
\binom{Qm}{Pm}G(m),\qquad m\in\mathbb Z_{\ge0},
\]

where $G(z)=\sum_{s\in\mathbb Z}e^{-ts^2+hs}R_s(z)$, $R_0=1$, and

\[
R_s(z)=\prod_{k=0}^{s-1}\frac{Bz-k}{Pz+k+1}\quad(s>0),\qquad
R_{-r}(z)=\prod_{k=0}^{r-1}\frac{Pz-k}{Bz+k+1}\quad(r>0).
\]

These rational functions equal the proposed gamma ratio meromorphically.
At nonnegative integer $m$, they vanish outside $-Pm\le s\le Bm$.
In particular $G(0)=1$; there is no hidden endpoint exception.

## Analytic bounds and continuation

On $\Re z\ge0$, each positive-offset factor has modulus at most

\[
\max(B/P,k/(k+1))\le\max(B/P,1).
\]

To verify this, expand the squared moduli: the numerator has cross term

$-2Bk\Re z$, whereas the denominator has $+2P(k+1)\Re z$.
The corresponding negative-offset bound interchanges $P,B$.
Consequently, for $M=\max(P/B,B/P,1)$,

\[
|R_s(z)|\le M^{|s|},\qquad
|G(z)|\le\sum_s e^{-ts^2+(|h|+\log M)|s|}<\infty.
\]

Thus the series converges normally and defines a bounded analytic function
on the right half-plane, holomorphic across each finite boundary point.

For global continuation, remove the discrete lattice

\[
\Lambda=\{-r/P:r\ge1\}\cup\{-r/B:r\ge1\}.
\]

On a compact set avoiding this lattice, all individual rational factors
are uniformly bounded: the factors tend uniformly to modulus $1$ as

$k\to\infty$, and the remaining finite denominators stay separated from
zero. Hence $|R_s|\le M_K^{|s|}$ there and Gaussian summability again
proves normal convergence. At a lattice point $z_0$, multiplication by

$z-z_0$ cancels the sole possible vanishing denominator in each term;
the same local bounds apply. Therefore $G$ extends meromorphically with
at most simple poles on $\Lambda$.

Set

\[
C(z)=\frac{\Gamma(Qz+1)}{\Gamma(Pz+1)\Gamma(Bz+1)}
e^{-QH(\alpha)z},\qquad
H(\alpha)=-\alpha\log\alpha-(1-\alpha)\log(1-\alpha).
\]

Uniform Stirling asymptotics in $\Re z\ge0$ give

\[
C(z)=\sqrt{\frac{Q}{2\pi PB}}\,z^{-1/2}
\bigl(1+O(|z|^{-1})\bigr),\qquad |z|\to\infty.
\]

The entropy exponential cancels exactly. Thus $C$, and $F=CG$, are
bounded on the closed right half-plane and have zero exponential type.
Both satisfy $C(0)=F(0)=1$. This is stronger than polynomial growth.

The gamma expression makes $C$ globally meromorphic. It has a simple
zero at every point of $\Lambda$, including negative integers: there
the two denominator poles outweigh the single numerator pole. These
zeros cancel the possible poles of $G$. Consequently $F$ has only
possible simple poles at $-r/Q$ with $Q\nmid r$. Further cancellations
are possible; no assertion that every possible pole is present is needed.

## Executed numerical checks, distinct from proof

Python `mpmath`, 100 decimal digits, evaluated the original finite sum and
the rational-product identity separately for every $m=0,\ldots,8$.
Decimal parameters were constructed from strings. The $s$-sum included
six additional offsets on each side of its exact support; those terms
vanished by the rational numerator factors. No gamma evaluation at its
poles was used.

| Parameters $(a,b,g;P,Q)$ | Tested arities | Maximum relative error |
|---|---|---|
| $(1,2,0.31;2,3)$ | $n=0,3,\ldots,24$ | $5.71493695641\times10^{-100}$ |
| $(3,2,0.67;2,5)$ | $n=0,5,\ldots,40$ | $5.47919580696\times10^{-99}$ |

These are finite floating-point consistency tests, not proofs of the
analytic statements, meromorphic continuation, or a source-level theorem.

## Conditional multiplier stability

The following corollary is valid by the previously reviewed
[Carlson bridge](../continuation-1837z/CARLSON-CONTINUATION-BRIDGE.md) and
[off-pole zero argument](../continuation-1837z/MEROMORPHIC-FINITE-PERSISTENCE.md).
It reuses those results rather than independently reauditing their full proofs.

Let $L$ be a positive even integer divisible by all rational denominators
needed for finitely many unequal factors. Let $A,B_0$ be finite products
of the rescaled $F$'s and any other nonzero bounded right-half-plane
holomorphic, globally meromorphic multipliers. Suppose the exact normalized
identity is

\[
A(m)=B_0(m)\prod_i U(Lm/2;t_i,h_i)\quad(m\ge0),\qquad
t_i>0,\quad \sum_i t_i<\infty,\quad \sum_i h_i^2<\infty,
\]

and $A,B_0$ are not identically zero with value $1$ at zero sufficing.
Then the family of strict equal-arm factors is finite.

Indeed scaling preserves zero exponential type, and multiplication by
bounded finite factors preserves the Carlson hypotheses. Carlson applied
after shifting by one gives the analytic identity. Continuation gives it
away from the combined discrete pole sets. An infinite equal-arm family
provides infinitely many inherited zeros accumulating at either

$p=-1/L$ or $p=-3/L$. A sufficiently small disk about $p$ contains
no other multiplier poles. Thus finite multipliers cannot cancel these
off-pole zeros. They become zeros of $A$, contradicting its nonzero
meromorphic germ at $p$, which has finite pole order.

This corollary requires the displayed normalized integer identity. For a
raw diagonal-law application, matching the removed quadratic and linear
exponential prefactors remains a separate obligation. Irrational saddle
ratios, infinite unequal-arm families, the full observation bridge, and
general G4 are not established by this audit. Next action: integrate the
audited rational construction only under these explicit hypotheses.
