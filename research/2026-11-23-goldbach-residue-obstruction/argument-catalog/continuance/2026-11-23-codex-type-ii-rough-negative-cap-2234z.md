# An explicit negative-weight cap on the rough Type II slice

23 November 2026. Unconditional hand proof at every sufficiently large power of two. The bound uses a second Selberg square only for an upper count on the very rough slice of the fixed expansion. It gives a numerical charge on a ratio interval of width proportional to \(\log N\). Reference ID GB-ROUGH-NEGATIVE-CAP-2234. [Pinned Type II expansion](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md) · [Pinned least-prime grouping and budget](https://github.com/Sodelin/Research-Commons/blob/38ef35f193f2098942b64baf461128a06278482f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-negative-ratio-budget-2217z.md)

## Statement and exact support

Write \(N=2^k\), \(L=\log N\), \(H=\sqrt N\), \(m=qh\), and \(n=N-m=\ell uws\). Use the paired odd-\(m\) Type II sum with \(H/2<q<h\le H\), squarefree \(m\), \((m,N)=1\), and the original count and mark projector \(F(m)\). Keep squarefree \(Y_0\)-rough \(n\), \(Y_0=\exp(L^{.005})\), and the same \(W_N(n)\) with Selberg indices \(a\le N^\kappa\) supported on primes at most \(N^\delta\). Keep prime \(N^{1/10}<\ell\le N^{1/8}\), \(u>N^{1/5}\), \(w>N^{1/5}\) prime, \(s\ge1\), and \(v=ws\). Keep the original strict \(d=uv>D_0\) and any previously imposed base and endpoint cuts. The weight of an opened term is

\[
F(m)W_N(n)\mu(h)\mu(u)\log(h/q)\frac{\log\ell\log w}{\log d}.
\]

Use just the positive stress interval \(L/20\le\log(u/v)\le L/10\). Let \(r=d/w=us\) and \(G_{q,h,\ell,w}\) be the exact signed subtotal over the admitted \(u\)'s at fixed \(q,h,\ell,w\). For a fixed \(\sigma\) with

\[
0<\sigma<31/640,\qquad \sigma\ge \min(\kappa,\delta),
\]

write \(\mathcal D_{>N^\sigma}=\sum_{P^-(r)>N^\sigma}(G_{q,h,\ell,w})_-\), where \(x_-=\max(0,-x)\). The doubled charge satisfies

\[
2\mathcal D_{>N^\sigma}(N)\le (C_\sigma+o(1))N,\qquad
C_\sigma=\frac{9}{56000\,\sigma^2}
\left(\frac38-\frac{\log 2}{2}\right)
\prod_{p>2}\left(1+\frac{1}{p(p-1)}\right).
\tag{1}
\]

The factor of two is the one from the even-endpoint row of the exact remainder budget. In particular \(C_{1/25}<1/200\), so the doubled charge on this whole slice is at most \(N/200\) at each sufficiently large power of two. The same estimate bounds twice the sum of the individual absolute weights there. It allows every admissible factor count of \(r\).

## Sieve at the modulus \(\ell ws\)

Put \(D_\sigma=N^\sigma\). If \(P^-(r)>D_\sigma\), then \(u,s\) are both free of primes up to \(D_\sigma\). Also \(\ell,w>D_\sigma\). Every nontrivial index in \(W_N(n)\) has a prime factor at most \(N^{\min(\kappa,\delta)}\). Thus \(W_N(n)=1\) on this slice. This uses the original fixed weights in the exact signed expansion.

Trim \(n<N/L^B\) by the pinned divisor-moment estimate, at cost \(O_A(N/L^A)\) for sufficiently large fixed \(B\). At each \(n\) the number of placements is bounded by \(\tau(N-n)\tau(n)^3\), with absolute weight per placement \(O(L)\). Cauchy–Schwarz with fixed divisor moments therefore gives this trim even after taking absolute values. On the rest

\[
\log d\ge (7/8)L-B\log L,\quad
v^2=\frac{n}{\ell}\exp\bigl(-\log(u/v)\bigr),\quad
v\le N^{17/40},\quad s\le N^{9/40}.
\]

Fix \(\ell,w,s\) and set \(M=\ell ws=\ell v\). The bound \(M^2\le \ell N^{19/20}\) gives \(M\le N^{43/80}\). The modulus is odd and coprime to each prime at most \(D_\sigma\). The variable \(u=(N-qh)/M\) is determined by the unit hyperbola \(qh=N\bmod M\).

To upper bound the positive absolute count, enlarge the \(q,h\) domain to the full square and use the continuous nonnegative weight \((\log(h/q))_+\). Enforce the roughness of \(u\) by an auxiliary Selberg square \((\sum_{a\mid u}\lambda_a^*)^2\) with squarefree indices \(a\le D_\sigma\). Every rough \(u\) gives weight one. At a squarefree \(c=[a,b]\), the condition \(c\mid u\) is \(qh=N\bmod c\), independent of the unit-hyperbola condition by CRT. The densities are \(g(2)=3/4\) and \(g(p)=(p-1)/p^2\) for odd \(p\) since no odd prime divides \(2^k\). For example the three residue pairs with even product give \(g(2)\). The \(q,h\) coprimality and mask tests belong to the exact original sum and can be dropped in this positive upper count.

The pinned rectangle completion gives \(M^{1/2+o(1)}(1+H/M)\) error per residue pair at the modulus \(c\). In each pair of classes modulo \(c\), substituting the two progressions and shifting both variables by constants modulo \(M\) gives a unit hyperbola with right-hand side \(Nc^{-2}\bmod M\). There are at most \(c\,2^{\omega(c)}\) residue pairs. We use \(|\lambda_a^*|\le1\) and at most \(D_\sigma^2\) pairs of indices, so the opened error per \(M\) is \(N^{4\sigma+o(1)}(M^{1/2}+H/M^{1/2})\). To include the log weight, divide the square in \((q/H,h/H)\) into \(O(L^2)\) rectangles of mesh \(O(1/L)\) and take the supremum of the weight on each. The count is nonnegative and the upper integral differs from the exact one by \(O(1/L)\). Its normalized value tends to

\[
J=\int_{1/2}^1\int_x^1\log(y/x)\,dy\,dx=\frac38-\frac{\log 2}{2}.
\]

The number of possible triples \((\ell,w,s)\) at fixed \(M\) is at most \(d_3(M)=N^{o(1)}\). Including all log weights and summing \(M^{1/2}+H/M^{1/2}\) up to \(N^{43/80}\) now costs at most

\[
N^{129/160+4\sigma+o(1)}+N^{123/160+4\sigma+o(1)}=o(N).
\tag{2}
\]

This checks the total sieve error after all opening and decomposition choices. [Pinned rectangle completion with the same local densities](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md#count-at-a-fixed-composite-modulus)

## Main term with its constant

Extend \(g\) multiplicatively on squarefree integers. Let \(b(a)=\prod_{p\mid a}g(p)/(1-g(p))\) on squarefree \(a\) and \(b(a)=0\) otherwise. The auxiliary square has quadratic main term \(1/G_\sigma\), where \(G_\sigma=\sum_{a\le D_\sigma}b(a)\). For verification the coordinates \(y_c=\sum_{c\mid a}\lambda_a^*g(a)\) give

\[
\sum_{a,b_0}\lambda_a^*\lambda_{b_0}^* g([a,b_0])
=\sum_c y_c^2/b(c).
\]

Use only squarefree \(c\le D_\sigma\) in this sum. Choose \(y_c=\mu(c)b(c)/G_\sigma\) and invert. This gives \(\lambda_1^*=1\). For squarefree \(a\), the magnitude of \(\lambda_a^*\) is \(G_\sigma^{-1}\prod_{p\mid a}(1+b(p))\sum_{j\le D_\sigma/a,\ (j,a)=1}b(j)\), at most one because every \(j\) can be multiplied by all divisors of \(a\) inside the denominator sum. This is the pinned Selberg diagonal identity with the present one-dimensional densities. [Pinned diagonal calculation](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#the-weight-and-its-elementary-quadratic-identity)

To get its constant when the prime range extends to \(D_\sigma\), write \(b=(a\mapsto 1/a)*c_0\) by Dirichlet convolution. For odd \(p\), \(b(p)=1/p+O(p^{-2})\), so \(c_0(p)=b(p)-1/p\) and \(c_0(p^2)=-b(p)/p\) are \(O(p^{-2})\) and all higher local terms vanish. The factor at \(2\) is finite. Thus \(\sum_j |c_0(j)|\log(2j)<\infty\). Summing the inner harmonic series gives

\[
G_\sigma=C_g\log D_\sigma+O(1),\qquad
C_g=\prod_p(1-1/p)(1+b(p))
=2\prod_{p>2}\left(1+\frac1{p(p-1)}\right)^{-1}.
\]

The count at fixed \(M\) has main term \(N(J+o(1))\varphi(M)/(M^2G_\sigma)\). Bound \(\varphi(M)/M\le1\). For each fixed \(\ell,s\), the exact ratio and endpoint constraints allow only primes \(w\) in the interval

\[
\frac{N^{9/20}}{\sqrt\ell\,s\, L^{B/2}}\le w\le \frac{N^{19/40}}{\sqrt\ell\,s}.
\]

Intersect this interval with the original lower cutoff on \(w\). Its log width is at most \(L/40+O_B(\log L)\), and its retained lower end is at polynomial scale. Mertens' theorem gives \(\sum_w(\log w)/w\le L/40+o(L)\) uniformly. The prime-\(\ell\) sum is \(\sum_\ell(\log\ell)/\ell=L/40+o(L)\). For \(s\), use the positive bound

\[
\sum_{\substack{s\le N^{9/40}\\P^-(s)>D_\sigma}}\frac1s
\le\prod_{D_\sigma<p\le N^{9/40}}(1-1/p)^{-1}
=\frac{9}{40\sigma}+o(1),
\]

with \(s=1\) included. This uses the full reciprocal mass and keeps the actual \(w\) prime sum. Together with \(\log d\ge(7/8)L-B\log L\), the doubled main term divided by \(N\) is at most

\[
\frac{2J}{C_g\sigma}\cdot\frac{8}{7}\cdot\frac{1}{40^2}\cdot\frac{9}{40\sigma}+o(1)=C_\sigma+o(1).
\]

This proves (1). For a simple numerical enclosure, \(J<.029\) and the odd-prime product is at most \(\exp(\sum_{j\ge3}1/(j(j-1)))=e^{1/2}<1.65\). At \(\sigma=1/25\), \(9/(56000\sigma^2)=45/448\), giving \(C_{1/25}<8613/1792000<1/200\). An exact-rational check reproduced this numerical enclosure and the two error exponents \(773/800\) and \(743/800\).

## Fixed-target budget and remaining range

The previous bound charges \(P^-(r)\le P_1=\exp(\sqrt L)\) at \(o(N)\) on this strip. Equation (1) charges \(P^-(r)>N^\sigma\) using the exact same groups. Define \(\mathcal D_{\rm mid}\) using \(P_1<P^-(r)\le N^\sigma\). These are disjoint choices on the fixed group; the bound applies to both parities of the expanded \(n\). The remaining sufficient inequality is

\[
2\mathcal D_{\rm mid}(N)\le M_0(N)+E_{\rm other}(N)-(C_\sigma+\eta)N
\]

for some fixed \(\eta>0\) at all sufficiently large powers of two. Here \(M_0\) is the positive comparison term, and \(E_{\rm other}\) is the exact signed remainder outside the doubled stress interval. The comparison term has the existing lower bound \((\mathfrak S(2^k)/6+o(1))N\). The cap only assigns a charge to one slice of the remainder. The other signed rows and the middle least-prime range still need a same-target lower estimate. Plugging a fixed \(\sigma\) into the previous \(O(\sigma N)\) edge estimate alone gives no numerical allowance without bounding its constant.

The parallel complete-tail proof applies before any actual-\(u\) ratio selection. Its reflection estimate on two joined orientations requires both signs of \(\log(u/v)\). The present absolute cap is on the single positive strip and includes all allocations surviving its original cutoff. A next step is to sum the two edge contributions left by the least-prime toggle conditional on the exact intermediate prime \(p\), keeping the sign and the original support when combining the two edges. [Peer complete-tail and two-orientation proofs](https://github.com/Sodelin/Research-Commons/blob/509ffef9a4390db820bfed2bee5638a5addec8d1/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-complete-tail-and-inner-reflection.md) · [Pinned remainder inequality](https://github.com/Sodelin/Research-Commons/blob/38ef35f193f2098942b64baf461128a06278482f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-negative-ratio-budget-2217z.md#fit-to-the-fixed-target-budget)
