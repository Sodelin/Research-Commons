# An exact divisor allocation in the unmatched Goldbach row

Let \(N=2^k\), \(L=\log N\), \(H=\sqrt N\), \(Q=N^{1/4}\), and \(\alpha=H/L^{K_0}\) for fixed \(K_0\). For sufficiently large \(N\), \(Q<\alpha<H/2\). In the unmatched part of \(A_{02}\) keep the actual masks \(Q\le q\le\alpha\), \(h>H\), \(qh<N\), and both variables odd. Its weight on squarefree \(m=qh\) is \(-\Lambda(N-m)\mu(h)\log h\). Omitting the possible \(N-m=2\) term changes the whole row by at most \(N^{o(1)}\) by the divisor bound, and higher powers of two have \(4\mid m\) and vanish. The following statements concern actual raw pieces. The prime-density model for the whole row need not be negligible on an arbitrary one of these selections. [Pinned regroup and full centered model](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0)

## Divisor allocation and exact signs

Select odd squarefree endpoints \(m=suv<N\) with primes \(Q\le u\le\alpha\) and \(v>H\). Then \(s<Q\), and the two marked primes are unique. Every admissible divisor \(q\) must contain \(u\), since a divisor of \(s\) alone is smaller than \(Q\) and \(v>\alpha\). Write \(q=u(s/d)\), \(h=vd\), and \(R=us/\alpha\). The original strict long condition \(h>H\) holds for all such \(d\), and its actual cutoff on \(q\) becomes \(d\ge R\). Thus the entire group at this one endpoint is
\[
\Lambda(N-suv)\sum_{\substack{d\mid s\\d\ge R}}\mu(d)\log(vd).
\tag{1}
\]

If \(R\le1\), all allocations are present. The sum in (1) equals \(\log v\) for \(s=1\), equals \(-\log p\) for \(s=p\) prime, and vanishes for \(\omega(s)\ge2\). The first case is favorable. For \(R>1\), the omitted divisors satisfy \(d<R<L^{K_0}\), since \(us=m/v<H\). When \(\omega(s)\ge2\), let \(r\) be the product of the primes dividing \(s\) that are strictly smaller than \(R\). If \(r<R\), all omitted divisors are precisely the divisors of \(r\). The retained weight in (1) is then \(-\Lambda(N-suv)\log v\) if \(r=1\), is \(+\Lambda(N-suv)\log p\) if \(r=p\) is prime, and is zero if \(\omega(r)\ge2\). The endpoint \(d=R\), if integral, stays in the original sum.

## A uniform sieve for the remaining long prime

Fix \(a=us\), with \(Q\le a<H\), and use the two forms \(v\) and \(N-av\) on odd \(v\) in \((H,N/a)\). Exclude proper prime powers on the second form at total cost \(N^{1/2+o(1)}\), from the number of endpoints and the divisor bound. Likewise the endpoints \(N-av\le N^{.374}\) cost \(N^{.374+o(1)}\). Use a Selberg upper square of level
\[
D_a=\left\lfloor N^{499/1000}/\sqrt a\right\rfloor.
\]
Both retained primes exceed \(D_a\). Let \(C_2=\prod_{r>2}(1-(r-1)^{-2})\), and put \(\kappa(a)=\prod_{r\mid a}(r-1)/(r-2)\), over odd primes. The local forbidden fractions at odd \(r\) are \(g(r)=2/r\) if \(r\nmid a\) and \(1/r\) if \(r\mid a\), since \(N=2^k\). Opening the square on the odd progression gives its main term at most \((N/(2a))/G_a(D_a)\), where
\[
G_a(D)=\sum_{\substack{b\le D\\b\text{ odd squarefree}}}
 \prod_{r\mid b}\frac{g(r)}{1-g(r)}.
\]
The standard optimal coefficients have \(\lambda_1=1\), \(|\lambda_b|\le1\), and the reciprocal norm above. The individual floor error is \(D_a^2N^{o(1)}\), since each least common multiple has at most \(2^{\omega(\cdot)}\) forbidden residues. Even if it is weighted by \(L^2\tau(s)\), summing over \(u,s\) costs \(N^{.998+o(1)}\sum_{u,s}1/(us)=o(N)\). [Selberg diagonal formula](https://github.com/Sodelin/Research-Commons/commit/b8d0afa3e5fab3380f662ce172eacad56ea05316)

Uniformly in \(a\), one has \(G_a(D_a)\gg L^2/\kappa(a)\). Use primes \(r\le D_a^c\) for a small fixed \(c>0\) and first sum over their unrestricted squarefree products. The Euler product has order at least \(L^2/\kappa(a)\) by Mertens. In the normalized Euler measure a prime occurs with probability \(g(r)\), so the mean of the logarithm of the product is at most \(2\sum_{r\le D_a^c}\log r/r=O(c\log D_a)\). Markov's inequality keeps at least half the mass on products at most \(D_a\) for sufficiently small \(c\). The resulting two-form count is \(\ll N\kappa(a)/(aL^2)+D_a^2N^{o(1)}\).

For \(a=up\) with both marks prime, the leading constant can be kept uniformly:
\[
G_a(D_a)=\frac{(\log D_a)^2}{8C_2\kappa(a)}+O(\log D_a).
\tag{2}
\]
To see this, factor the Dirichlet series for \(G_a\) as \(\zeta(1+w)^2\) times its corrected Euler product. At ordinary odd primes its leading corrected coefficient is \(O(r^{-2})\); at the at most two exceptions it is \(O(r^{-1})\). The log-squared absolute moment of the correcting Dirichlet coefficients is bounded uniformly, since \(\log^2(r)/r\) is bounded and there are at most two exceptions. The correcting factor at \(w=0\) is \(1/(4C_2\kappa(a))\). Convolution with \(\sum_{j\le X}\tau(j)/j=(\log X)^2/2+O(1+\log X)\) gives (2), including its uniform error. After the odd progression factor of one half, the two-form upper main term is \((4C_2+o(1))\kappa(a)N/(a\log^2 D_a)\).

## Pointwise charges

**All incomplete \(s=p\), for \(u\ge Q\), cost \(o(N)\).** Incompleteness forces \(\alpha<up<H\). For fixed \(p\), the sum of \(1/u\) over primes \(u\ge Q\) in \((\alpha/p,H/p)\) is \(O((1+\log L)/L)\), by partial summation from Chebyshev's prime bound and \(H/\alpha=L^{K_0}\). The weight is at most \(L^2\). With the upper sieve, \(\kappa(up)\ll1\), and \(\sum_{p\le Q}1/p\ll\log L\), the total cost is \(O(N(1+\log L)^2/L)+o(N)\).

**Other incomplete groups.** If \(s\) has all primes greater than \(Y\) with \(\log Y\gg\log L\) in the sense \(\log Y/\log L\to\infty\), the sole omitted divisor is 1. The absolute weight of the entire group is at most \(L^2\), also allowing \(s=p\). Again \(\alpha<us<H\). The bound for the reciprocal sum over \(u\) stays the same, and the squarefree Euler upper bound gives \(\sum_{s<Q,\ P^-(s)>Y}\kappa(s)/s\ll L/\log Y\) when \(Y\le Q\). The charge is therefore \(O(N(1+\log L)/\log Y)+o(N)=o(N)\). Alternatively for all incomplete \(s\le S_0\), without a roughness assumption, use the bound \(L^2\tau(s)\) and \(\sum_{s\le S_0}\mu^2(s)\tau(s)\kappa(s)/s\ll(1+\log S_0)^2\). This costs \(o(N)\) whenever \((1+\log S_0)^2(1+\log L)=o(L)\).

**Complete groups with \(s=p\).** For any \(u\ge Q\), restricting \(p\le Y=N^{o(1)}\) costs \(O(N(1+\log Y)/L)+o(N)\). This uses the reduced weight \(\log p\,L\), \(\sum_{Q\le u\le H}1/u=O(1)\) over primes, and \(\sum_{p\le Y}(\log p)/p\ll1+\log Y\). For \(u>N^{23/50}\), the whole complete \(s=p\) piece costs strictly less than \(0.070N\) for all sufficiently large powers of two, without a subpower restriction on \(p\). Indeed, put \(z=23/50\), \(x=(\log p)/L\), \(y=(\log u)/L\) and \(c(x,y)=499/1000-(x+y)/2\). The primes \(p\le L^2\) cost \(o(N)\) as just shown, and on the rest \(\kappa(up)=1+o(1)\) uniformly. By (2), the upper coefficient after reinstating \(\log p\,L\) is at most
\[
4C_2 \int_0^{1/2-z}\int_z^{1/2-x}\frac{dy\,dx}{y\,c(x,y)^2} + o(1).
\tag{3}
\]
The reciprocal prime limits follow from the prime number theorem and a fixed mesh for the bounded continuous integrand. The enlarged domain \(x+y\le1/2\) contains the exact \(up\le\alpha\) support. The marked large prime \(v>H\) remains in the lattice count. To bound (3) by rational arithmetic, write \(t=x+y-z\), \(\gamma=1/2-z=1/25\), \(b=499/500-z=269/500\). Then its integral part is
\[
16C_2\int_0^\gamma \frac{\log(1+t/z)}{(b-t)^2}\,dt.
\]
The odd Euler product through 23 already gives \(C_2<2/3\). Set \(f_0=b^{-2}\), \(f_1=(b-\gamma)^{-2}\), and \(B=(1/2-\gamma/(3z))/z^2\). For \(0\le t\le\gamma\), the alternating log bound gives \(\log(1+t/z)\le t/z-Bt^2\) and the latter is nonnegative. Convexity bounds \((b-t)^{-2}\) by the secant between \(f_0,f_1\). Hence (3) is at most
\[
\frac{32}{3}\left[\frac{\gamma^2}{z}\left(\frac{f_0}6+\frac{f_1}3\right)
 -B\gamma^3\left(\frac{f_0}{12}+\frac{f_1}{4}\right)\right]+o(1)
=\frac{34026578240000}{491280211892583}+o(1)<0.070.
\]

These results remove some actual contributions on the genuine moving overlap-free support at every sufficiently large target. They leave endpoints without a prime factor \(v>H\) or without the other prime mark \(u\ge Q\), complete \(s=p\) groups with polynomial-sized \(p\) and smaller \(u\), and incomplete groups outside the favorable or sieve-controlled cases. These are hand arguments. Only the displayed rational constant was evaluated by exact arithmetic. No Lean verification or average over \(N\) is used.
