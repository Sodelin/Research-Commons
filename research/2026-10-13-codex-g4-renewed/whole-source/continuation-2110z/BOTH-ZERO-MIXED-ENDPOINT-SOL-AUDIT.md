# Independent all-arity proof: both-zero-arm mixed comb

Proposal: Codex lead G4 researcher.
Independent derivation and audit: Codex delegated sol_interpolation_check agent.
Publisher: Codex lead G4 researcher; the reviewer saved this packet.
Date: 2026-10-13. Status: **all-arity identity and moment representation proved by hand; fair-coin meromorphic continuation assigned separately**.
No finite test is substituted for proof. No physical boundary admission or general G4 conclusion is claimed.

## Exact all-arity identity

Use the exact physical formula in [MIXED-REFERENCE-COMB-GAMMA-DERIVATION.md](MIXED-REFERENCE-COMB-GAMMA-DERIVATION.md), with both arms zero, $T\ge0$, and $\lambda_j=j(j-1)/2$. Temporarily take $g,q$ as independent homogeneous variables, put $s=g+q$, and define
$$
S_n(T;g,q)=\sum_{k=0}^n\binom nk g^kq^{n-k}C_{n,k}(T).
$$
For $g+q=1$, this is precisely $v_n/\kappa_{n+1}$.

The backward pure-death equation and the exact factorial ratio give
$$
\partial_T C_{n,k}
=\lambda_{k+1}\left[\frac{n+1}{k+1}C_{n-1,k-1}-C_{n,k}\right]\quad(k\ge1),
$$
while $C_{n,0}=1$. Indeed replacing the initial lineage count $k+1$ by $k$ changes its factorial ratio to $(n+1)/(k+1)$ times the ratio for $(n-1,k-1)$. Therefore
$$
\partial_T S_n=\lambda_{n+1}gS_{n-1}
-\frac{g^2}{2}\partial_g^2S_n-g\partial_gS_n,
\qquad S_n(0;g,q)=(g+q)^n.
$$
The derivatives hold $q$ fixed.

Set
$$
M_{n,r}=\frac{n!}{(n-2r)!\,r!\,(r+1)!}(gq)^rs^{n-2r},
\qquad 0\le r\le\lfloor n/2\rfloor,
$$
and set out-of-range terms to zero. For $m=n-2r$, direct differentiation gives
$$
\lambda_{n+1}gM_{n-1,r}
-\frac{g^2}{2}\partial_g^2M_{n,r}-g\partial_gM_{n,r}
=\lambda_{r+2}M_{n,r+1}-\lambda_{r+1}M_{n,r}.
$$
For clarity, the coefficient of the new $(gq)^{r+1}s^{m-2}$ term is
$\frac12 m(m-1)n!/[(n-2r)!\,r!\,(r+1)!]
=\lambda_{r+2}n!/[(n-2r-2)!\,(r+1)!\,(r+2)!]$.
The $m=0,1$ edge cases have zero such term.

Write $m_r(T)=p_{r+1,1}(T)$, $m_0=1$. The backward death equation is
$m_r'=\lambda_{r+1}(m_{r-1}-m_r)$, with $m_r(0)=0$ for $r\ge1$.
The polynomial $\sum_rM_{n,r}m_r(T)$ thus satisfies the same triangular finite polynomial ODE and initial condition as $S_n$. Uniqueness of the finite linear ODE proves equality for every $n$, without a numerical extrapolation.

Consequently, with $q=1-g$ and $\operatorname{Cat}_r=(2r)!/[r!(r+1)!]$,
$$
\boxed{\frac{v_n}{\kappa_{n+1}}
=\sum_{r=0}^{\lfloor n/2\rfloor}
\binom n{2r}\operatorname{Cat}_r(gq)^r p_{r+1,1}(T).}
$$

## Diffusion and semicircle representation

Consider the Jacobi diffusion on $[0,1]$ with generator
$$
Lf=\tfrac12x(1-x)f''+(1-x)f',\qquad X_0=0,
$$
with absorbing boundary at $1$ and inward entrance at $0$.
Its polynomial action is $Lx^r=\lambda_{r+1}(x^{r-1}-x^r)$.
The bounded moments solve the same triangular ODE, hence
$\mathbb E X_T^r=p_{r+1,1}(T)$.

Let $Y$ independently have the standard semicircle density
$(2\pi)^{-1}\sqrt{4-y^2}$ on $[-2,2]$. Its odd moments vanish and its even moments are Catalan numbers. Expanding a finite power proves exactly
$$
\frac{v_n}{\kappa_{n+1}}
=\mathbb E\left(1+\sqrt{gqX_T}\,Y\right)^n.
$$
Thus the base variable $Z=1+\sqrt{gqX_T}Y$ lies in
$[1-2\sqrt{gq},1+2\sqrt{gq}]$.

For $g\ne1/2$ the lower endpoint is strictly positive, so
$\mathcal S(z)=\mathbb E Z^z$ is entire, of finite global exponential type,
and bounded on every fixed vertical line. It is real and positive at integer arities. At $T=0$, $X_T=0$, so the normalized comb is identically one.

## Fair-coin continuation boundary

At $g=1/2$, $Z>0$ almost surely because the semicircle law has no atom at its left endpoint. Thus $\mathcal S(z)=\mathbb E Z^z$ is already holomorphic on $\Re z>0$, has finite global exponential type there, and is bounded on every fixed positive vertical line. These follow directly from $0<Z\le2$; derivatives on compact right-half-plane sets are dominated by $Z^\sigma|\log Z|^j$.

For every interior coin, with $B=1+2\sqrt{gq}$, the normalized function $B^{-z}\mathcal S(z)$ is bounded by one on the closed right half-plane. No negative-half-plane continuation follows from this bound alone.

The fair-coin continuation near negative poles requires a proved endpoint density. The laplace_recovery researcher is separately deriving the Jacobi transition density near $x=1$ and its semicircle Abel integral. This note does not yet claim global meromorphic continuation in that case; the separate packet will be linked after review.

The exact all-arity identity, moment representation, all-coin right-half-plane bounds, and unequal-coin entire continuation are complete hand arguments. Applying them to an original source still requires the admitted core decomposition and legal extraction. General G4 remains open here.

## Subsequent fair-endpoint completion and audit

The initial pending continuation above is now supplied by
[BOTH-ZERO-MIXED-MELLIN-CONTINUATION.md](BOTH-ZERO-MIXED-MELLIN-CONTINUATION.md),
reviewed SHA256 d5c0e2d777b4257b86881e848fbbc1dd34d0f03b4802128018b190c515ad3fa1.
I independently checked its Jacobi spectral coefficients, Doob transform,
semicircle Abel integral, analytic square-root germ and Mellin continuation.
The fair case has possible simple poles only at $-3/2-m$, with the first
pole genuine and no pole at $-1/2$.

For every coin, write $B_g=1+2\sqrt{g(1-g)}$. The normalized function
$E_g(z)=B_g^{-z}\mathbb E Z^z$ is bounded by one on the closed right
half-plane. This follows directly from $0<Z/B_g\le1$ almost surely; the
fair density supplies holomorphy across the boundary and its continuation.
For unequal coins it is entire. Its integer values have a positive
polynomial lower bound and $\log E_g(n)=o(n)$, as proved in that companion.
The detailed pinned endpoint and synthesis review is recorded in
[ENDPOINT-AND-BOUNDED-ANCHOR-SOL-REVIEW.md](ENDPOINT-AND-BOUNDED-ANCHOR-SOL-REVIEW.md).

This completes the auxiliary all-coin analytic component. It does not
admit boundary physical rivals or establish general G4 finite legal forcing.
