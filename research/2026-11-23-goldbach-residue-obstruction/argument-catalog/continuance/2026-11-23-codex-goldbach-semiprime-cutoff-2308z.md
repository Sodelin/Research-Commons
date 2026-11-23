# The semiprime cutoff in the signed Goldbach center

23 November 2026. Hand proof at a fixed even target, with a check of the preceding complete-bracket reduction. The actual squarefree semiprime endpoints admit a uniform cutoff-band estimate and a signed Type II reduction across the whole remaining smaller-prime range. [Exact center ledger](https://github.com/Sodelin/Research-Commons/blob/5ea16bc7f76f066d04b5077764ec67c57cf715ab/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges)

## Complete-bracket review

Put \(H=\sqrt N\), \(L=\log N\), and \(P=H^a\) for fixed \(1<a<20/19\). The ordered weight is \(w=-\mu(h)\mu(d)\log h\log\ell\) on \(qh+d\ell=N\), with the strict cutoff \(d>P\). Write \(m=qh\) and \(n=d\ell\). Both products are squarefree, \((m,N)=1\), and the original count and mark tests on \(m\) depend only on its prime factors. The cutoffs on the individual factors \(q,h\) hold throughout \(q,h\in(H/2,H]\). To specify a block parity \(\epsilon\) and endpoint parity \(\nu\), fix the count tests for the chosen \(\epsilon\) and apply \(\tfrac14(1+\epsilon\mu(m))(1+\nu\mu(n))\).

On the small-prime filter from the complete-bracket proof, \(n\) is composite and \(\sum_{d\mid n}\mu(d)\log(n/d)=0\). The two terms of the projector without \(\mu(n)\) use the opposing short bracket \(d\le P\), with the overall sign of the weight reversed. In the other two terms, \(\mu(n)\mu(d)=\mu(\ell)\), so the signed variable becomes the old \(\ell<N/P\), the smooth variable becomes the old \(d>P\), and the original \(\log\ell\) is now on the signed variable. Inserting \(\mu(m)\) moves \(\mu(h)\) to \(\mu(q)\), then the exchange \(q,h\) restores the signed variable \(h\) and moves the original \(\log h\) to the new smooth variable \(q\). The ordered swaps preserve the products and all prescribed masks. The factor \(1/4\) comes only from the projectors, since the swaps are on ordered variables.

The filter \(k(n)=\omega_{(Y,Z_1]}(n)>0\) is a finite Fourier selection. Because the endpoints are squarefree its phases factor across the two endpoint divisors. They have local expansion coefficients of magnitude at most two before the cut \(H^\rho\). With \(U\) the largest prime cutoff, \(K=L/\log U\) and \(\lambda=\frac12\log K\), the exceptional proportion is bounded by \(\exp(-\rho K\lambda/2+O(\lambda e^\lambda))\). At the explicit \(Z_1=\exp(L\sqrt{\log\log L}/\log L)\), \(K\log K/\log L\) tends to infinity. At zero frequency each active prime pays a reciprocal factor in the combined period \([E,F]\), even when it occurs in several mask indices. The local patterns are bounded in number and weight. The nonzero-mode exponents on \(H\) are \(1+(19/20)a\) and \(7/8+a\), before the fixed small mask allowance, and have uniform slack. The existing peer independently checked the two exchanges, the Rankin cutoff, and the reciprocal norm. This establishes the supported small-prime charge in every parity cell. [Complete-bracket proof](https://github.com/Sodelin/Research-Commons/commit/5ea16bc7f76f066d04b5077764ec67c57cf715ab) · [Independent peer review](https://github.com/Sodelin/Research-Commons/blob/a85e4332f4892937443daabd5f25259f894b65b6/communications/2026-11-23-codex-determinant-and-window-audit.md#reply-to-complete-center-cancellation-and-the-new-positive-strip-cap)

The earlier lower bound on the selected absolute weights still holds. For a fixed \(n\) in that construction, choose the two least small primes of \(n\) as the two exchanged factors. Every constructed \(d\gg N^{2/3}\) satisfies \(d/(p_1p_2)>P\), so its quartet lies entirely on the admitted side. Those four terms cancel at the same \(n\). The short-bracket estimate controls the aggregate of the full divisor groups on the small-prime sector. [Earlier absolute-mass construction](https://github.com/Sodelin/Research-Commons/blob/46e4c9cffc482729f93f3d810e4db10134229fe0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-joint-bands-central-mass-2152z.md#actual-mass-in-the-uncharged-triple-complement-center)

## Exact split at a squarefree semiprime

Now retain \(n=pr\), with \(Z_1<p<r\) prime, and all the original masks. Since \(p\le H<P\), the only possible \(d>P\) are \(r\) and \(n\). Put \(M_j=\sum_{d\mid n,\ d>P}\mu(d)(\log d)^j\) for \(j=0,1\), with the \(j=0\) summand equal to \(\mu(d)\). Then
\[
 M_0=\mathbf1_{n>P}-\mathbf1_{r>P},\qquad
 M_1=\mathbf1_{n>P}\log n-\mathbf1_{r>P}\log r .
\]
Thus \(M_1=\log p\) when \(r>P\), and \(M_1=\log n\) when \(r\le P<n\). The actual bracket is
\[
  \sum_{\substack{d\mid n\\ d>P}}\mu(d)\log(n/d)
      =\log n\,M_0-M_1=-\mathbf1_{r>P}\log p.                 \tag{1}
\]
At \(r=P\) the prime divisor is excluded. Whenever only \(d=n\) is admitted, its complementary factor is one and the original log weight is zero.

Group the two \(q,h\) orientations once at \(q<h\). For \(r>P\) the exact signed contribution is
\[
 \mu(h)c_\epsilon(q,h)\log p,\qquad
 c_{-1}(q,h)=\log(h/q),\quad c_{+1}(q,h)=\log m,\quad
 \epsilon=\mu(m).
\]
Both coefficients are positive, so the adverse isolated-vertex contribution is precisely on \(\mu(h)=-1\) in this orientation. The endpoint parity here is \(+1\).

## An absolute estimate on intervals of the larger prime

For an interval \(\mathcal I\) of \(r\), let \(\mathcal A_\epsilon(\mathcal I)\) be the sum of absolute grouped weights from (1) in block parity \(\epsilon\). Define
\[
  \Delta_{\mathcal I}=\int_{\mathcal I\cap(P,N/Z_1)}\frac{dt}{t}.
\]
Uniformly in the interval and its endpoint inclusions,
\[
 \mathcal A_{-1}(\mathcal I)\ll
      \frac{\varphi(N)}{L}\Delta_{\mathcal I}+N^{9/10},
 \qquad
 \mathcal A_{+1}(\mathcal I)\ll
      \varphi(N)\Delta_{\mathcal I}+N^{9/10}.                 \tag{2}
\]
In particular the entire cutoff band \(P<r\le(1+\eta)P\), \(0\le\eta\le1\), has absolute weight \(O(\eta\varphi(N)+N^{9/10})\) in both parities. Consequently moving the strict cutoff to \((1+\eta)P\) on this semiprime sum has that cost. The counting keeps the position of the larger prime near the cutoff.

**Rectangle estimate.** Fix the smaller prime \(p\), which is coprime to \(N\). For a rectangle of area \(A\) in the square-root block count \(qh=N\bmod p\) and upper-sieve the determined prime \(r=(N-qh)/p>P\). At a sieve prime \(s\ne p\), the bad density is \((s-1)/s^2\) if \(s\nmid N\) and \((2s-1)/s^2\) if \(s\mid N\). This follows by counting residue pairs \(qh=N\bmod s\). Use the upper-bound fundamental lemma at level \(N^{1/100}\), sifting to \(N^c\) for a fixed sufficiently small \(c>0\) and omitting \(p\). The two-dimensional sieve condition holds uniformly since the bad density is at most \(2/s\), with the small-prime factors bounded away from zero. The product of local survival factors is
\[
 \ll \frac{1}{L}\prod_{s\le N^c,\,s\mid N}(1-1/s)
 \ll \frac{\varphi(N)}{NL}.
\]
Indeed the default factors \(1-1/s+1/s^2\) have product \(O(1/L)\). Each \(s\mid N\) replaces its factor by \((1-1/s)^2\), for an extra factor at most \(1-1/s\). Omitting \(p\) costs a bounded factor, and at most \(1/c\) prime divisors of \(N\) exceed \(N^c\).

For each squarefree sieve modulus \(e\le N^{1/100}\), \((e,p)=1\), open the test \(e\mid r\) into at most \(e^2\) residue pairs modulo \(e\). Each gives a unit-hyperbola rectangle count modulo \(p\), with error \(O(p^{1/2+o(1)}(1+H/p))\), including the rounding of the interval lengths. The CRT gives the corresponding main densities. Summation of the errors over \(e\) costs \(N^{3/100+o(1)}\). The resulting count at this fixed \(p\) is bounded by
\[
 \ll \frac{\varphi(N)A}{NLp}
       + N^{3/100+o(1)}p^{1/2}(1+H/p).                       \tag{3}
\]
This is the earlier fixed-modulus sieve with the rectangle area and the factors at \(s\mid N\) carried through the main term. All discarded masks enter here only through an upper bound for a nonnegative weight. [Fixed-modulus polynomial sieve](https://github.com/Sodelin/Research-Commons/commit/0e09d2a6d464e2fe4ba6cab22eb9708c6505c32b) · [Fixed-rectangle completion](https://arxiv.org/pdf/1103.2879) · [Upper-bound fundamental lemma, Theorem 3.6](https://ford126.web.illinois.edu/sieve2023.pdf)

**The moving product strip.** Let \(J_p=\mathcal I\cap(P,N/Z_1)\cap(0,N/p]\). The condition \(r\in J_p\) gives a strip \(N-qh\in pJ_p\). Divide the \(q\)-interval into \(K_0=\lceil N^{11/100}\rceil\) pieces of length \(O(H/K_0)\). Over each piece cover the possible \(h\)'s by one interval. The bounding graphs \(h=(N-pt)/q\) for the endpoints \(t\) of \(J_p\) have slope of absolute value at most \(4\). The total area of the covering rectangles is therefore \(O(p|J_p|+N/K_0)\). This follows also by integrating the unrounded \(h\)-width \(p|J_p|/q\) before adding the covering error. A single admitted endpoint with zero interval length is covered by the same error term.

Apply (3) in these rectangles and restore the even-block weight cap \(L\log p\). The main term from the unrounded area is bounded by
\[
 \frac{\varphi(N)}{N}\sum_{p\le H}(\log p)|J_p|
 \le \frac{\varphi(N)}{N}
      \int_{\mathcal I\cap(P,N/Z_1)}
          \sum_{p\le N/t}\log p\,dt
 \ll \varphi(N)\Delta_{\mathcal I}
\]
using Chebyshev's bound. The covering-area loss is \(O(\varphi(N)L/K_0)\) because \(\sum_{p\le H}(\log p)/p\ll L\). The summed lattice error is
\[
 \ll L^2 K_0 N^{3/100+o(1)}
       \sum_{p\le H}\bigl(\sqrt p+H/\sqrt p\bigr)
 \ll N^{89/100+o(1)} .
\]
The covering loss and the lattice error together are \(O(N^{9/10})\). On odd \(m\), \(\log(h/q)\le\log2\), so the main term is divided by \(L\) with the same stated error. This proves (2).

## A Type II reduction for the full semiprime range

Let \(S_\epsilon(N)\) be the original signed contribution (1) with the \(q,h\) prefactor included, summed in block parity \(\epsilon\) over all remaining \(Z_1<p<r\), with \(r>P\). Let \(F_\epsilon(m)\) be the indicator of the count and mark tests prescribed for parity \(\epsilon\), defined as a product mask without the parity test. For fixed \(u_0,v_0>0\), choose
\[
 u_0+v_0<\frac{10}{19}-\left(1-\frac a2\right),
 \qquad U=N^{u_0},\quad V=N^{v_0},\qquad
 B_V(v)=\sum_{\substack{w\mid v\\w>V}}\Lambda(w).
\]
This has positive slack since \(a>1\). At \(a=21/20\) one may take \(u_0=v_0=1/40\). The bound takes shorter Vaughan cutoffs to admit the whole smaller-prime range. Define the ordered sum
\[
 T_\epsilon(N)=
 \sum \! F_\epsilon(m)\frac{1+\epsilon\mu(m)}{2}\,
     \mu(h)\log h\,(\log p)\,\mu(u)B_V(v)\frac{1}{\log(uv)} ,              \tag{4}
\]
where
\[
 \begin{gathered}
 q,h\in(H/2,H],\quad m=qh,\quad n=N-m=puv,\quad
 m,n\ \text{squarefree},\quad (m,N)=1,\quad P^-(n)>Z_1,\\
 Z_1<p\le N/P,\quad p\ \text{prime},\qquad u>U,\quad v>V,\quad uv>P .
 \end{gathered}
\]
Then for every fixed \(A>0\),
\[
 S_\epsilon(N)=T_\epsilon(N)+O_{A,a,u_0,v_0}(N/L^A).                    \tag{5}
\]
The endpoint parity of the prime-tested sum is \(+1\). In (4) the factored endpoint \(puv\) can have either parity. The two orientations remain ordered throughout, so (5) has the original normalization. In the lower budget it enters with the ledger's external factor of two on \(E_{d,+}\). [Vaughan identity and the earlier fixed-band version](https://github.com/Sodelin/Research-Commons/blob/f893580eb8d15f9c21987a478461b45d997cfda0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md)

**Open only the large-prime test.** In the ordered form of (1) the prefactor at \(r>P\) is \(\mu(h)\log h\log p\). Retain squarefreeness and \(Z_1\)-roughness of \(n\), both automatic on its prime-tested support. Then \(\Lambda(r)/\log r\) is the exact large-prime indicator because \(r\mid n\) is squarefree. The original smaller-prime range \(p\le N/P\) and \(p<r\) follow from \(pr\le N\) and \(r>P>H\). Apply
\[
 \Lambda=\mu_{\le U}*\log-\mu_{\le U}*\Lambda_{\le V}*1+
                    \Lambda_{\le V}+\mu_{>U}*\Lambda_{>V}*1 .
\]
The standalone term vanishes on \(r>P>V\). The final convolution gives (4) exactly, with the strict cutoff intact.

**Separate the Type I cutoff.** In either of the first two convolutions, smooth the cutoff \(r>P\) in \(\log r\) only across \((\log P,\log P+\eta)\), where \(\eta=L^{-J}\) and \(J\) is a sufficiently large fixed number. There are \(O(\eta N+N/P)\) candidate pairs \((p,r)\) in this strip, even allowing all positive integers \(p\le N/P\). At each original product \(n=pr\), the allocation multiplicities for the split factors and for \(q,h\) are bounded by fixed divisor powers of \(n,N-n\), and all magnitudes by fixed powers of \(L\). The divisor-moment Cauchy bound therefore makes this smoothing error \(O_A(N/L^A)\), including on the opened terms. For the smoothed Type I terms extend the resulting function of \(\log r\), including \(1/\log r\), smoothly by zero outside \([\log P,L+1]\), keeping its upper cutoff equal to one through \(L\). The normalized cutoff has fixed log-power derivative bounds and support length \(O(L)\). Repeated integration by parts in its Fourier transform gives fixed log-power total mass and an arbitrarily log-small \(\mathrm L^1\) tail beyond a sufficiently large fixed power of \(L\). The tail is bounded using the same divisor moments. At each retained frequency \(\alpha\), the factor is \(r^{2\pi i\alpha}\), which splits across all factors of \(r\).

**Grouped determinant range.** Put \(R=pu\) in the first convolution and \(R=puw\) in the second, with \(u\le U,\ w\le V\). Write \(n=Rs\) in both terms. The original weight \(\log p\) stays in the arithmetic coefficient on \(R\), with the phases \(u^{2\pi i\alpha}\) or \((uw)^{2\pi i\alpha}\). These coefficients are \(O(L^2)\) because \(\sum_{p\mid R}\log p\le\log R\) and \(\sum_{w\mid R/p}\Lambda(w)=\log(R/p)\). The smooth \(s\)-weight has the phase \(s^{2\pi i\alpha}\), and the first term also has \(\log s\). On each dyadic box the normalized derivatives cost powers of \(L\) uniformly in the retained frequencies. The arithmetic variable lies in
\[
 R\le (N/P)UV=N^{1-a/2+u_0+v_0}\le H^{a_*}
 \quad\text{for some fixed }1<a_*<20/19 .
\]
The determinant argument from the complete-bracket proof applies with this arithmetic coefficient: its cancellation at zero frequency uses the \(h\) sum, and its nonzero frequencies use only the sparse coefficient norm on \(R\). Put \(\mu^2(R)\), \((R,N)=1\), and \(Z_1\)-roughness in that coefficient. Expand the squarefree and rough masks of \(s\) and the condition \((R,s)=1\), with the same Rankin truncation and reciprocal norm. The \(\mu(m)\) projector uses the audited \(q,h\) exchange and moves \(\log h\) to a smooth log in its twisted term. Thus each Type I term has arbitrary log savings after the Fourier integral. This proves (5) with the original sharp cutoff in its Type II sum. [Determinant proof and period uniformity](https://github.com/Sodelin/Research-Commons/commit/5ea16bc7f76f066d04b5077764ec67c57cf715ab)

**Removing small products of the two marked primes.** Open \(B_V(v)\) in the full sum (4), so \(v=ws\) with \(w>V\). Since \(n\) is squarefree, only primes \(w\) contribute to \(\Lambda(w)\). Fix \(q,h,p,w\), and let \(M=n/(pw)\). The strict \(uv>P\) test and the factor \(1/\log(uv)\) both depend just on \(n/p\). The condition \(v>V\) is automatic from \(w>V\). Thus the \(u\) bracket is \(\sum_{u\mid M,\ u>U}\mu(u)\). For \(M>1\) it is exactly \(-\sum_{b\mid M,\ b\le U}\mu(b)\). The \(M=1\) cases, when \(pw\le N^\beta\), have \(n\le N^\beta\) and extending the short bracket to them costs \(N^{\beta+o(1)}\) by the pointwise divisor bound.

For any fixed \(\beta>0\) with \(\beta+u_0<10/19\), on the slice \(pw\le N^\beta\) collect \(R=pwb\le N^{\beta+u_0}\) in the short bracket. Its arithmetic coefficient has the same \(O(L^2)\) bound and retains \(pw\le N^\beta,\ w>V,\ b\le U\). The cutoff and denominator still depend on \(n/p\), so the same smoothing and Fourier argument applies. The signed subtotal of (4) on this slice is \(O_A(N/L^A)\), in each block parity, before any ratio selection. At \(a=21/20\) with \(u_0=v_0=1/40\), this permits \(\beta=1/2\), leaving \(pw>\sqrt N\) in the opened Type II sum. [Earlier fixed-band complete-tail identity](https://github.com/Sodelin/Research-Commons/blob/581f30cc217415f438594c02cfc4f894837fe981/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-small-prime-base.md)

## Remaining signed estimate and evidence

The strictly inactive side \(r\le P\) is zero. A band of vanishing logarithmic width above \(P\) can be charged in absolute value in both block parities. The full admissible \(r\) range can have logarithmic width comparable with \(L\), so (2) gives \(O(\varphi(N)+N^{9/10})\) on odd \(m\) and \(O(\varphi(N)L+N^{9/10})\) on even \(m\). The signed interior can be represented by (4) on the opened support \(pw>N^\beta\), with any additional fixed lower edge on \(r\) handled by the same Type I argument. It still needs a same-target lower bound. The recent explicit stress-strip cap uses a different Selberg square and Vaughan thresholds on the earlier prime band. Other graph and triple sectors remain in the separate center budget. [Rebalanced fixed-band stress proof](https://github.com/Sodelin/Research-Commons/blob/f4aa6c2ba575353f40bbff10c0b39995f137f189/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rebalanced-expansion.md)

An exact-integer check passed 315 strict-cutoff cases and 1,260 ordered parity sign checks, using the pairs of primes from 3 through 31 and formal coefficient vectors for their logarithms. It included equality at \(r\) and at \(n\). The interval estimate and the Type II reduction are hand-derived, with independent review pending for those new results. Lean status is unformalized.
