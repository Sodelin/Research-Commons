# Completing the divisor sum removes small-prime endpoints from the Goldbach center

23 November 2026. Hand proof at a fixed even target, with Davenport's Möbius estimate and Bettin–Chandee's trilinear estimate as inputs. Independent review pending. The result concerns the signed larger-divisor center in the existing Goldbach residue ledger. [Exact center](https://github.com/Sodelin/Research-Commons/blob/ee0116a4311b3556c361afdacf16d622024c246a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges)

## Statement

Let \(H=\sqrt N\), \(L=\log N\), \(P=H^a\) for fixed \(1<a<20/19\), and \(Y=\exp(L^{.005})\). Let \(Z_1\ge Y\) with \(\log Z_1=o(L\log\log L/\log L)\). One explicit choice is
\[
 Z_1=\exp\!\left(\frac{L\sqrt{\log\log L}}{\log L}\right).
\]
On the exact support \(q,h\in(H/2,H]\), \(m=qh\) squarefree, \((m,N)=1\), and \(n=N-m=d\ell>0\) squarefree and \(Y\)-rough, use the strict cutoff \(d>P\) and the ordered weight \(w=-\mu(h)\mu(d)\log h\log\ell\). The uncharged \(m\) tests are \(\tfrac14\log L<\omega_J(m)<8\log L\), \(\omega_W(m)\le1\), \(b_{.9896}(m)>.0153\log L\), and \(\mu(m)=1\) or \(b_{.95}(m)>.0029\log L\). Here \(J=(\exp(L^{.10}),\exp(L^{.99})]\), \(W=(\exp(L^{.75}),2\exp(L^{.75})]\), and \(b_\gamma\) counts distinct prime factors at most \(\exp(L^\gamma)\). Write \(k(n)=\omega_{(Y,Z_1]}(n)\).

For each prescribed \(\mu(m)\) and \(\mu(n)\), the sum of \(w\) over \(k(n)\ge1\) is
\[
 \boxed{\quad O_{A,a}(N/L^A)\quad\text{for every fixed }A>0.\quad}                 \tag{1}
\]
The proof also allows replacing \(k(n)\ge1\) by any selection of positive \(k(n)\) values, uniformly in that selection. In particular \(k(n)\ge3\) is a triple-admitting sector outside an absolutely negligible set of small \(n\). The whole center can consequently be charged on \(Z_1\)-rough endpoints, with error \(O_{A,a}(N/L^A)\) in each parity.

The parallel proof bounds the complete two-small-prime slice in all four parity cells and gives an \(o(N)\) one-small-prime estimate on odd \(m\). Completing the whole logarithmic divisor sum allows the one-small-prime estimate with arbitrary logarithmic savings in all four cells. The parallel estimates that select the triple row separately have their own supports. [Peer estimates and placement in the ledger](https://github.com/Sodelin/Research-Commons/blob/53ce363ab3513dce368dd71bd28ee17c257efdac/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-triple-center-small-third-prime.md)

## Exact completion at a composite endpoint

At a fixed ordered \(q,h\), every divisor of \(n\) has the same masks except the strict cutoff. The complete identity is
\[
 \sum_{d\mid n}\mu(d)\log(n/d)=\Lambda(n).
\]
For squarefree \(n\) it follows directly by collecting the coefficient of \(\log p\) for each \(p\mid n\). This coefficient is \(\sum_{d\mid n/p}\mu(d)\), which vanishes when \(n/p>1\). On the present block, \(q\ne h\) because \(m\) is squarefree and both factors exceed one. With \(t=\lfloor H\rfloor\) we have \(qh\le t(t-1)\) and \(n\ge t>Z_1\) for sufficiently large \(N\). Thus \(k(n)\ge1\) forces \(n\) composite. For every such pair,
\[
 \sum_{\substack{d\mid n\\ d>P}}\mu(d)\log(n/d)
   =-\sum_{\substack{d\mid n\\ d\le P}}\mu(d)\log(n/d).                          \tag{2}
\]
The divisor exactly at \(P\), if present, belongs to the right side. The same equality holds with any extra \(n\)-only selection common to the two sides. It requires the full admitted divisor bracket at each chosen endpoint.

Apply the determinant bound below to the short side of (2) for the untwisted weight. For the \(\mu(n)\)-twisted weight, keep the original large-\(d\) sum. Squarefreeness gives \(\mu(n)\mu(d)=\mu(\ell)\). Exchange \(d,\ell\) so the signed divisor is now the old \(\ell<N/P<H\) and the old cutoff is an independent lower edge on the smooth complement. The weight \(\log\ell\) moves to the signed divisor coefficient. In either argument inserting \(\mu(m)\) allows the exchange \(q,h\) by \(\mu(m)\mu(h)=\mu(q)\). This keeps the product tests, including the count tests chosen for the prescribed \(m\)-parity, while moving \(\log h\) to the smooth \(q\)-weight. The two parity projectors are linear combinations of these four sums. [Parity relabeling](https://github.com/Sodelin/Research-Commons/blob/f29fbbc1aaddfa721c757f3f0c5acb6fd058daad/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-four-parity-components.md)

## Determinant with the endpoint count test

The needed extension is the \(O_{A,a}(N/L^A)\) bound on signed \(h,d\) when \(d\le H^a\), with the extra count selection on \(n\), independent interval edges, and either placement of the two log weights described above. Here and below \(d\) denotes the signed divisor after any exchange. The proof follows the grouped-frequency argument. The points to verify are the new count period, the size of its truncation error, and the reciprocal norm at zero frequency. [Grouped-frequency proof](https://github.com/Sodelin/Research-Commons/blob/ee0116a4311b3556c361afdacf16d622024c246a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-joint-frequency-cutoff.md) · [Bettin–Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769)

**Sharp edges and product errors.** Use dyadic boxes \(d\asymp D,\ell\asymp B_0\). Drop boxes with \(DB_0<N/L^{C_0}\); their products satisfy \(n<4N/L^{C_0}\). In the retained boxes \(N/L^{C_0}\le DB_0\le N\). Smooth the \(q,\ell\) edges inside their intervals at relative width \(L^{-J_0}\) in their respective scales. The \(q,h\) exception counts are \(O(NL^{-J_0}+H)\) per edge and the \(d,\ell\) counts are \(O(DB_0L^{-J_0}+D)\), including a possible sharp edge at \(P\). The \(h,d\) edges stay in the coefficients. An exceptional family of \(U\) products or pairs on either side has absolute cost \(\ll L^2 U^{1/2}(NL^{C_1})^{1/2}\) while any extra multiplicities are bounded by fixed powers of \(\tau(m)\tau(n)\). Indeed the opposite product is determined, and \(\sum_{v\le N}\tau(v)^j\ll_j NL^{2^j-1}\) follows from \(\tau(v)^j\le d_{2^j}(v)\). Cauchy–Schwarz gives the stated cost. This also covers the finitely many logarithmically indexed boxes by increasing \(C_0,J_0\). The normalized smooth derivatives have fixed log-power bounds.

**Open the count masks.** Each count is additive across the two factors of its squarefree product. Use finite Fourier projectors for the count values, with \(M=\lceil 2L\rceil+2\) possible frequencies per count. Since \(\omega(m),\omega(n)\le L/\log 2<M\), projecting onto a set of values costs at most \(O(L)\) in absolute Fourier coefficient sum per count. The number of count variables is fixed. On the \(q,h\) factors write the resulting weight as \(\prod_{p\mid v}z_p\), where \(|z_p|=1\) and \(z_p=1\) outside the union of the tested prime intervals. On the \(d,\ell\) factors write it as \(\prod_{p\mid v}x_p\), with \(x_p=0\) for \(p\le Y\), \(x_p=\xi\) for \(Y<p\le Z_1\) and \(x_p=1\) elsewhere, with \(|\xi|=1\). Keep these phases on \(h,d\) in their coefficients. On \(q,\ell\) expand over squarefree divisors \(e\mid q\), \(f\mid\ell\), respectively, with coefficients \(\prod_{p\mid e}(z_p-1)\) and \(\prod_{p\mid f}(x_p-1)\). Both have local absolute weight at most two.

Keep \((h,N)=(d,N)=1\) and the two Möbius factors. Expand squarefreeness of \(q,\ell\) by \(r_q^2\mid q,r_\ell^2\mid\ell\), coprimality of the two factor pairs by \(b\mid(q,h),v\mid(d,\ell)\), and \((q,N)=1\) by \(c\mid(q,\operatorname{rad}N)\), with the respective Möbius weights. This gives exact squarefreeness of the products before truncation and justifies all count factorizations.

Truncate the seven indices \(r_q,r_\ell,b,v,c,e,f\) at \(R=H^\rho\) for a sufficiently small fixed \(\rho>0\). The first four tails require a square \(s^2\mid m\) or \(s^2\mid n\) with \(s>R\), an \(O(N/R)\) product set. The \(c\)-tail costs at most \(N\tau(N)/R\) products. For the last two put \(U=\max\{Z_1,\exp(L^{.99}),2\exp(L^{.75})\}\), \(K=L/\log U\), \(\lambda=\frac12\log K\), and \(\alpha=\lambda/\log U\). The logarithm of the mean bound for \(\prod_{p\mid u,\ p\le U}p^\alpha\) over \(u\le N\) is at most
\[
 \sum_{p\le U}\frac{p^\alpha-1}{p}
 \ll \lambda e^\lambda ,
\]
by the positive divisor expansion and \(\sum_{p\le U}\log p/p\ll\log U\). The exceptional proportions are bounded by \(\exp(-\tfrac12\rho K\lambda+O(\lambda e^\lambda))\). They save every fixed power of \(L\) since \(K\log K/\log L\to\infty\). Absolute multiplicities of the opened or truncated masks are fixed divisor powers, so the product error above applies. The periods are
\[
 E=[r_q^2,b,c,e]\le H^{5\rho},\qquad F=[r_\ell^2,v,f]\le H^{4\rho}.
\]

**Poisson and zero frequency.** Set \(q=Eq'\), \(\ell=F\ell'\). The unit conditions on \(h,d\) force \((h,F)=(d,E)=(h,d)=1\) in a solution. Impose the first two separately and use the last in the primitive reciprocal sums. Thus \((Eh,Fd)=(E,F)=g\mid N\). For \(E'=E/g,F'=F/g\), the single residue class for \(q'\) is \((N/g)\overline{E'h}\bmod F'd\). Let \(x=h/H,\ y=d/D,\ u=q/H,\ T_0=EF'D/H\). With normalized weights \(Q,G\) for the two smooth variables, the amplitude after Poisson is
\[
 {\cal A}_t(x,y)=\frac{1}{T_0y}\int Q(u)
      G\!\left(\frac{N-Nux}{DB_0y}\right)e\!\left(-\frac{tu}{T_0y}\right)\,du ,
 \qquad e(s)=\exp(2\pi i s).
\]
The accompanying phase is \(e(t(N/g)\overline{E'h}/(F'd))\). At \(t=0\) the prefactor is \(H/(D[E,F])\) times a function of polylogarithmic size and variation in \(h/H\). For fixed \(d\) the \(h\) coefficient is \(\mu(h)\prod_{p\mid h}z_p\) with \((h,NdF)=1,\ b\mid h\), and at most one log weight.

For clarity the required prefix estimate, uniform in the phase and a polynomial-size excluded modulus \(M_0=NdF\), follows from Davenport. Restrict the excluded primes first to \(p\le U\), at absolute cost \(O(HL/U)\) since \(\sum_{p\mid M_0,\ p>U}1/p\ll L/U\). If \(z'_p\) is \(z_p\) or zero as specified by the exclusion, the remaining multiplicative function is \(\mu*g_0\), with \(g_0(p^j)=1-z'_p\) for \(j\ge1,p\le U\) and zero for larger \(p\). The reciprocal norm is polylogarithmic. For indices \(s>H^{1/4}\) use the Euler product at exponent \(1-\alpha\). Its logarithm is \(O(\sum_{p\le U}p^{-1+\alpha})=O(\log L+\lambda e^\lambda)\). The extra factor \(H^{-\alpha/4}=\exp(-K\lambda/8)\) therefore gives arbitrary log savings on the reciprocal tail. On \(s\le H^{1/4}\) apply Davenport to the \(\mu\)-sum of length comparable with \(H/s\) in a difference of prefixes at the \(h\) scale. The condition \(b\mid h\) is an additive Fourier average of norm one. Partial summation handles the optional log and the smooth amplitude. This proves \(O_A(H/L^A)\) for every fixed \(A\) after increasing Davenport's saving. [Davenport, *On some infinite series involving arithmetical functions (II)*](https://doi.org/10.1093/qmath/os-8.1.313)

Summing \(d\) at cost \(O(D)\) gives \(O_A(N/L^A)/[E,F]\) per mask with the reciprocal factor left explicit. Across all indices, each active prime in any mask divides \([E,F]\), with only finitely many local patterns and absolute local weight bounded independently of the primes and phases. The sum of the absolute mask weights divided by \([E,F]\) is at most \(\prod_{p\le N}(1+C_3/p)\ll L^{C_4}\). This term permits the full count projection, including the \(n\) count.

**Nonzero frequencies.** Integrations by parts in \(u\) leave \(|t|\le T_0H^\rho\) with arbitrary fixed power saving in the discarded tails. This also holds when \(T_0H^\rho<1\), by summing the decay over integer \(t\ne0\). In a dyadic signed-frequency block \(|t|\asymp T\), the amplitude and its mixed first derivatives in \((x,y,t/T)\) are \(O(L^{C_5}T_0^{-1}H^{3\rho})\). Three-variable partial summation reduces to rectangular prefix sums in the trilinear theorem. There the three scales are \(E'H,F'D,T\); the three norms multiply to \(O(L^2\sqrt{HDT})\) by the sparse \(h,d\) positions. The amplitude and norm factor before the scale terms is \(H^{1+O(\rho)}L^{O(1)}\), using \(\sqrt{HDT}/T_0\le HH^{\rho/2}\). The phase factor is \(H^{O(\rho)}\) since \((N/g)T_0/((E'H)(F'D))=1\). With \(D_*=\max(H,D)\), the two remaining terms, including the leading \(H\), are bounded up to \(H^{O(\rho+\varepsilon)}L^{O(1)}\) by
\[
 H D^{7/10}D_*^{1/4},
 \qquad H D^{3/4}\big((D/H)D_*\big)^{1/8}.
\]
For \(D\le H\) these are at most \(H^{39/20}\) and \(H^{15/8}\). For \(D\ge H\) they are \(HD^{19/20}\) and \(H^{7/8}D\). The seven truncated indices and the two divisor expansion coefficients add at most \(H^{9\rho}\). Take \(\rho,\varepsilon\) small in terms of \(a\) so both exponents have fixed slack below \(2\) throughout \(D\le H^a\). Summing the boxes, frequencies and Fourier projections finishes the determinant estimate and (1).

## Connection to the running balance

The peer reply's two-prime grouping gives additional pointwise information. For squarefree \(n\), fix distinct primes \(p,r\mid n\). Group the signed divisors \(d=k_0,pk_0,rk_0,prk_0\), where \(k_0\mid n/(pr)\). The signs alternate and the logarithm is affine in the two choices. The four terms sum to zero when \(k_0>P\), and there are no admitted terms when \(prk_0\le P\). For each placement in a crossing group the exact interval is
\[
 P<d\le P\gcd(d,pr).
\]
The gcd is the selected part of \(pr\) in \(d\). This describes which terms contribute after grouping. A single unqualified restriction \(d\le Ppr\) may retain pieces of already cancelling complete groups. [Peer reply and strict endpoint identity](https://github.com/Sodelin/Research-Commons/blob/b8d0afa3e5fab3380f662ce172eacad56ea05316/communications/2026-11-23-codex-determinant-and-window-audit.md#reply-to-the-triple-complement-running-balance)

In the earlier large absolute-mass construction, \(d\gg N^{2/3}\) and \(d\) has many prime factors at most \(\exp(L^{.90})\). For any two such primes \(p,r\), \(d/(pr)>P\) for large \(N\), so every constructed tuple belongs to an exactly cancelling quartet in the full bracket. The other members can fall outside the construction's restricted divisor geometry. Those endpoints lie in the \(k(n)\ge3\) sector, where (1) bounds the aggregate of the full brackets. If \(k(n)\ge3\) and \(n>PZ_1^3\), a product of three of the short primes is strictly below \(n/P\), so this entire endpoint sector is triple-admitting. The \(n\le PZ_1^3=N^{a/2+o(1)}\) exceptions have absolute cost \(N^{a/2+o(1)}\) by the divisor bound. This identifies an asymptotic triple sector on the same exact masks and explains why allowing lower-order divisors can matter at the same \(n\). [Absolute-mass construction](https://github.com/Sodelin/Research-Commons/blob/46e4c9cffc/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-joint-bands-central-mass-2152z.md#actual-mass-in-the-uncharged-triple-complement-center) · [Finite running balance](https://github.com/Sodelin/Research-Commons/commit/bfd3f2d1281fe76fa8541279a7aef3e4949e051e)

The charge in (1) applies to the all-divisor center before any split into graph and triple-admitting endpoint sectors. It also applies directly to the separate \(k(n)\ge3\) triple sector as above. Any bound on brackets with additional restrictions on individual admitted divisors needs its own argument. The fixed-target lower bound on the full surviving signed center is now needed only for \(P^-(n)>Z_1\). In the ledger's notation it is
\[
 2E_{d,+}^{\,P^-(n)>Z_1}(N)
 \ \ge\ -M_0(N)-E_*(N)+\eta N
\]
for some fixed \(\eta>0\), with graph and triple charges restricted to the surviving support to count every bracket once. The next estimate is the adverse isolated-vertex contribution on this raised roughness scale, starting with the squarefree semiprime endpoints. The Goldbach lower budget remains open. [Fixed-target budget](https://github.com/Sodelin/Research-Commons/blob/ee0116a4311b3556c361afdacf16d622024c246a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#reflect-the-short-complement-graph-at-the-strict-cutoff)

## Evidence

The analytic bound is a hand proof on the stated support. Independent review is pending. Lean status is unformalized.

Separately, an exact-integer check used all 120 composite squarefree products of subsets of \(\{2,3,5,7,11,13,17\}\). The code represented each \(\mu(d)\log(n/d)\) by its vector of prime-log coefficients. At every cutoff equal to a divisor and immediately below it (a half-integer), 4,344 completion splits and 40,824 two-prime crossing checks passed. This finite check tests the algebra and the strict endpoint. The earlier fixed-target running-balance computation supplies the distinct numerical evidence on the original center.
