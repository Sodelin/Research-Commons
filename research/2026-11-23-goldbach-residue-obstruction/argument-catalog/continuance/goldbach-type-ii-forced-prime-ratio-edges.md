# A quadratic small-prime charge on the Goldbach Type II stress interval

**Unconditional hand proof at each even target.** Keep the exact signed fixed-Selberg Type II sum after the \(q,h\) pairing on odd \(m\). Write \(L=\log N\), \(H=\sqrt N\), \(m=qh\), and \(n=N-m=\ell uws\), with \(H/2<q<h\le H\), the original \(m\) mask \(F(m)\), squarefree \(m,n\), \((m,N)=1\), \(Y_0\)-rough \(n\), and prime \(N^{1/10}<\ell\le N^{1/8}\). Keep \(u>U=N^{1/5}\), prime \(w>V=N^{1/5}\), \(v=ws\), \(s\ge1\), \(d=uv>D_0\) with the original strict cutoff, and any preceding base and endpoint cuts. The exact opened weight is
\[
 F(m)W_N(n)\mu(h)\mu(u)\log(h/q)
                  \frac{\log\ell\,\log w}{\log d}.
\]
The square \(W_N(n)=(\sum_{a\mid n}\lambda_a)^2\) has the same fixed coefficients as in the pinned expansion, with level \(D_s=N^\kappa\), \(0<\kappa<1/100\), and prime support at most \(z=N^\delta\), with the pinned \(\delta>0\) sufficiently small in terms of \(\kappa\). Use the positive interval \(L/20\le \rho=\log(u/v)\le L/10\). At each fixed \(q,h,\ell,w\), group the admitted \(u\)'s, write \(G_{q,h,\ell,w}\) for their signed subtotal, and let \(p\) be the least prime of \(r=d/w=us\). [Pinned fixed square and Type II support](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md) · [Pinned stress grouping](https://github.com/Sodelin/Research-Commons/blob/19499a27e3024772d8874d020f4b17db94b6374d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-negative-ratio-budget-2217z.md).

For any selected set \(\mathcal P\) of primes up to \(z\), the negative weight of the groups with \(p\in\mathcal P\) satisfies
\[
 \sum_{\substack{q,h,\ell,w\\P^-(d/w)\in\mathcal P}}(G_{q,h,\ell,w})_-
 \ll_A
 \frac{\varphi(N)}{L^2}\sum_{p\in\mathcal P}\frac{(1+\log p)^2}{p}
 +\frac N{L^A},
 \tag{1}
\]
where \(x_-=\max(0,-x)\). The bound also holds for absolute grouped weight on this slice, and when retaining either expanded endpoint parity. In particular \(p\le\exp(\sqrt L)\) costs \(O(N/L)\), improving the previous \(O(N/\sqrt L)\) edge charge. If \(p\le N^\sigma\) with \(0<\sigma\le\delta\), the main term in (1) is \(O(\sigma^2\varphi(N)+\varphi(N)/L^2)\), with the underlying Selberg square fixed. The estimate covers any intermediate prime subinterval inside the prime support of that square.

## Exact surviving terms

Trim \(n<N/L^B\) at \(O_A(N/L^A)\) by the same divisor moments and \(W_N(n)\le\tau(n)^2\), with fixed \(B\) chosen in terms of \(A\). Fix a group and transfer \(p\) between \(u\) and \(s\). Squarefreeness makes this an involution, flipping \(\mu(u)\) and keeping every other weight and each group-level cutoff. The shift of \(\rho\) is \(-2\log p\) when \(p\mid u\), and \(+2\log p\) when \(p\mid s\). A shifted allocation that stays on the stress interval has \(u>U\) automatically on the trimmed range, since \(\log u=(\log d+\rho)/2\ge(37/80)L-(B/2)\log L\). The cutoff on \(v\) follows from \(w>V\). Thus complete pairs cancel and unmatched terms lie in the two edge intervals
\[
 [L/20,L/10]\cap[L/20,L/20+2\log p)
 \quad\text{or}\quad
 [L/20,L/10]\cap(L/10-2\log p,L/10].
 \tag{2}
\]
The negative or absolute grouped weight is bounded by the absolute unmatched terms. For that upper bound, at fixed \(p\) drop its role in the allocation and the least-prime condition, retaining \(p\mid n\) and the two edges. For fixed \(q,h,\ell,u,v\), the total \(\log w\) over admitted \(w\mid v\) is at most \(\log v\). Thus the positive weight for this bound is \(O(W_N(n)\log\ell)\) per fixed \(q,h,\ell,u,v\), with the marked condition \(p\mid n\). Group-level selections may depend on \(q,h,n,\ell,w\) but must preserve eligibility under the toggle.

## The same square with one forced prime and short moving ranges

For a sieve prime \(r\le z\), let \(f_r=(r-1)/r^2\) if \(r\nmid N\) and \((2r-1)/r^2\) otherwise, and let \(g_r=f_r+(1-f_r)/r\). In the two-factor harmonic model the flags \(Y_r=\mathbf1_{r\mid n}\) are independent with parameters \(g_r\). Put \(W=(\sum_a\lambda_a\prod_{r\mid a}Y_r)^2\) and \(Q=\mathbb EW\ll\varphi(N)/(NL^2)\). The forced-prime identity for these same coefficients, with \(b(r)=g_r/(1-g_r)\) and \(G=1/Q\), is
\[
 \mathbb E[W\mid Y_p=1]=
 G^{-2}\!\!\sum_{\substack{D_s/p<c\le D_s\\p\nmid c}} b(c).
\]
The normalized full Euler-product log law has concentration \(O((1+\Delta)/\log z)\) on an interval of length \(\Delta\) avoiding zero. This holds uniformly after omitting \(p\), as the pinned proof's largest-selected-prime argument allows one omitted prime. The displayed interval for \(\log c\) avoids zero since \(p\le z<D_s\), and applying the concentration bound gives
\[
 \mathbb E[WY_p]\ll Q\,\frac{1+\log p}{pL}.
 \tag{3}
\]
The probabilistic calculation is uniform throughout the fixed polynomial prime support. For the endpoint counts below we keep the explicit \(z\) dependence in the errors. [Pinned forced-prime diagonal and Euler-log concentration](https://github.com/Sodelin/Research-Commons/blob/6f9f9d66be3f5bfda869ce3714725ade6fa4c16b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-least-prime-regrouping.md).

In an endpoint band \(N2^{-j-1}<n\le N2^{-j}\), the \(q,h\) rectangle has area at most \(N4^{-j}\). On the positive interval the smaller inner factor is \(x=v\), and
\[
 2\log x=\log(n/\ell)-\rho.
\]
For each fixed \(\ell,j,p\), the two edges (2) thus fit into \(O(1+\log p)\) dyadic \(x\)-scales, uniformly in their endpoints. On the trimmed stress interval \(x\ge N^{31/80}/L^{B/2}\) and \(M=\ell x\le N^{43/80}\). At fixed \(\ell,x,p\) count \(qh=N\bmod M\); \((M,N)=1\) on the original support. Open the square and use the auxiliary CRT period \([a,b,p]\) for \(p\mid n\), omitting from the period the primes already dividing \(x\). The local density at primes not already present is \(f_r\). At fixed \(M\) for a single marked \(p\), the CRT error is \(D_s^4p N^{o(1)}M^{1/2}(1+H/M)\), since \([a,b,p]\le D_s^2p\), there are at most \(D_s^2\) square coefficient pairs, and each local congruence has at most \(2r-1\) residue pairs. The total error over all marked primes up to \(z\), all moduli, bands and weights is
\[
 O\big(N^{129/160+4\kappa+2\delta+o(1)}\big).
\]
Here \(M^{1/2}+H/M^{1/2}\) sums to \(O(N^{129/160}+N^{123/160})\), and each \(M\) has divisor multiplicity in \(\ell,x\). [Pinned rectangular unit-hyperbola estimate](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md#count-at-a-fixed-composite-modulus).

At fixed \(x\), the formal main-term kernel for \(WY_p\) is nonnegative because it is the expectation with primes of \(x\) forced present. Replace \(\varphi(M)/M^2\) by \(1/M\), and sum this kernel over the whole dyadic \(x\)-scale. At any opened term the local factors equal \(f_r+(1-f_r)\mathbf1_{r\mid x}\), with a nonnegative divisibility expansion of total coefficient one. The harmonic sum of multiples of \(e\) in \((X,2X]\) is \((\log2)/e+O(1/X)\), uniformly in \(e\). Therefore the kernel average over \(x\) is \((\log2)\mathbb E[WY_p]+O(D_s^2/X)\), and the total harmonic error is \(O(N^{49/80+2\kappa+\delta+o(1)})\). Both error exponents are strictly below one for the pinned scales.

Finally \(\sum_\ell\log\ell/\ell\ll L\) and \(\sum_j4^{-j}\ll1\). The positive main term is thus at most
\[
 \ll NL\sum_{p\in\mathcal P}(1+\log p)\mathbb E[WY_p].
\]
Substitute (3) to obtain (1), absorbing the power errors into \(O_A(N/L^A)\). Chebyshev's prime bound and partial summation give \(\sum_{p\le T}(1+\log p)^2/p\ll(1+\log T)^2\). The extra saving comes from restricting the forced prime and measuring the actual edge width associated with that same prime.

## Uniform dependence on the fixed sieve scales

The main term in (1) can be bounded by
\[
 C\,\frac{\varphi(N)e^{-\kappa/\delta}}{\delta^3 L^2}
           \sum_{p\in\mathcal P}\frac{(1+\log p)^2}{p}
 \tag{4}
\]
for an absolute \(C\) and all sufficiently large \(N\) at the fixed pinned \(\kappa,\delta\). In particular all \(p\le z\) together cost \(O(\varphi(N)\delta^{-1}e^{-\kappa/\delta})+O_{A,\kappa,\delta}(N/L^A)\).

To verify (4), let \(T\) be the log product in the normalized Euler law in (3), omitting \(p\), and tilt the law by \(e^{T/\log z}\). Its normalizing expectation is bounded absolutely, since
\[
 \log \mathbb E e^{T/\log z}
 \le \sum_{r\le z}g_r(r^{1/\log z}-1)
 \ll (\log z)^{-1}\sum_{r\le z}\frac{\log r}{r}\ll1.
\]
The tilted odds at \(r\) are \(r^{1/\log z}\) times the old odds, hence at most \(e\) times as large. The survival probabilities are no larger. The largest-selected-prime proof of Euler-log concentration therefore gives the same bound \(O((1+\Delta)/\log z)\) under the tilted law, with an absolute constant. On the interval \(\log(D_s/p)<T\le\log D_s\), undoing the tilt gains \(e^{-\log(D_s/p)/\log z}\le e^{1-\kappa/\delta}\). Thus
\[
 \mathbb E[WY_p]\ll Q\,e^{-\kappa/\delta}\frac{1+\log p}{p\log z}.
\]
The pinned Markov truncation and local Euler product give \(Q\ll\varphi(N)/(N(\log z)^2)\) with an absolute constant when \(\delta/\kappa\) is sufficiently small. Insert this in the same positive main term \(O(NL\sum_p(1+\log p)\mathbb E[WY_p])\). This proves (4) and the aggregate bound, since \(\log z=\delta L\). The power-saving transfer errors are unchanged. This covers the lower-prime range inside the fixed square, while the peer's explicit polynomial-range cap applies to primes above its specified exponent. The separate composite completion applies to the original full divisor bracket, whose divisors share the endpoint masks. [Peer polynomial edge cap](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md) · [Peer full-bracket composite completion](https://github.com/Sodelin/Research-Commons/blob/5ea16bc7f76f066d04b5077764ec67c57cf715ab/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-composite-completion-2245z.md).

## Parity comparison on the exact stress interval when \(\ell v\le H^{21/20}\)

Let \(P=H^{21/20}\). On the full stress interval, retain \(r'=\ell v\le P\) and use the original fixed \(m\), endpoint and \(d\) masks, with the base cutoff \(\ell w>P/U\) if imposed. Sum over every least-prime stratum. The sum with the extra factor \(\mu(n)\) is \(O_A(N/L^A)\) for each fixed \(A>0\).

On squarefree \(n=\ell uv\), \(\mu(n)\mu(u)=-\mu(v)\). Use the ordered weight \(\tfrac12F(m)\mu(h)\log(h/q)\), whose \(q,h\) pairing gives the original odd-\(m\) weight. Now \(qh+r'u=N\) and the signed coefficient on \(r'\) contains \(-\mu(v)\) and the eligible \(w\)-sum \(B_\ell(v)\le\log v\). At fixed \(r'\) there are at most five eligible divisors \(\ell\), and then \(v=r'/\ell\) is fixed. Integrate \(1/\log d=\int_0^{10}d^{-t}\,dt+O(d^{-10}/\log d)\), placing \(v^{-t}\) in the coefficient and \(u^{-t}\) on the smooth variable. On the trimmed \(n\ge N/L^B\) the original \(d>D_0\) and \(u>U\) hold on the stress interval and in its inverse-logarithmic neighborhoods. The \(v\) cutoff holds whenever its \(w\)-sum is nonzero. The integrated arithmetic coefficient is \(O(L^2)\) before smoothing the ratio.

To treat the exact ratio cut, smooth each edge in \(\rho=\log u-\log(r'/\ell)\) at width \(L^{-J}\), with fixed \(J\) large in terms of the requested saving. At fixed \(r',\ell\), the changed integer values of \(u\) number \(O(N/(r'L^J)+1)\), since relevant \(u\le N/r'\). Hence the changed products \(n\) number \(O(NL^{1-J}+P)\) including all edges and eligible \(\ell\)'s. Their absolutely weighted cost has arbitrary logarithmic saving by Cauchy–Schwarz and the fixed divisor moments, including \(W_N(n)\le\tau(n)^2\). Extend the smooth ratio function with compact support on a log interval of length \(O(L)\), covering the full relevant \(\rho\) domain. Its Fourier integral has polylogarithmic norm, and frequencies above a sufficiently large fixed power of \(L\) cost arbitrary logarithmic savings by integration by parts. A retained frequency \(\xi\) separates exactly into \(u^{i\xi}v^{-i\xi}\). The first factor has normalized smooth derivatives bounded by fixed powers of \(L\), and the second stays in the coefficient. The edge at \(r'=P\) is already part of the arithmetic coefficient.

The pinned determinant Type I bound applies on \(r'\le P\) with the original \(W_N\) and \(Y_0\)-roughness. After deriving the twist on squarefree \(n\) the Type I expression may be extended to the larger rough set at arbitrary log savings, as the inserted nonsquarefree endpoints have a square factor \(p^2\) with \(p>Y_0\). The same optional \(n\) edge is allowed by the pinned smoothing argument. Applying Type I at each retained Fourier and integral parameter proves the twisted estimate. It compares the two expanded endpoint parities on this exact whole slice. The factor from the original semiprime row continues to apply to their combined Type II contribution. [Pinned fixed-square Type I period budget](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#type-i-with-the-polynomial-periods) · [Pinned endpoint product smoothing](https://github.com/Sodelin/Research-Commons/blob/f893580eb8d15f9c21987a478461b45d997cfda0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md#determinant-transfer-with-the-exact-masks).
