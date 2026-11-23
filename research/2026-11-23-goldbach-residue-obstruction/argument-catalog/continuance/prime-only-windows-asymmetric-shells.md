# Prime-only windows and asymmetric divisor shells

## A prime-only form of the missing window

Let \(L\) be either \(\zeta_M\) for a number field \(M\), or an Artin factor over \(\mathbb Q\) regular and nonzero at \(1\). Use \(r=1\) for \(\zeta_M\) and \(r=0\) for the Artin factor. Write \(c=\operatorname{FP}_{s=1}(L'/L)\) and \(-L'/L=\sum_n\Lambda_L(n)n^{-s}\). In the Dedekind case put \(d=[M:\mathbb Q]\) and \(Q=|D_M|\). In the Artin case let \(d\) be the representation dimension and let \(Q\) be any positive integer divisible by the ramified primes of the representation. In both cases \(|\Lambda_L(p^j)|\le d\log p\). Let \(B\) consist of all higher prime powers and the primes dividing \(Q\). Set
\[
c_*=c+\sum_{n\in B}\frac{\Lambda_L(n)}n,\qquad
P_L(y)=\sum_{\substack{p\le y\\p\nmid Q}}\Lambda_L(p)(y/p-1)
-r y\log y+(r+c_*)y .
\]
The sum defining \(c_*-c\) is absolutely convergent. The full normalized observable \(G_L(y)=\sum_{n\le y}\Lambda_L(n)(y/n-1)-r y\log y+(r+c)y\) satisfies
\[
G_L(y)-P_L(y)
=-\sum_{\substack{n\le y\\n\in B}}\Lambda_L(n)
-y\sum_{\substack{n>y\\n\in B}}\frac{\Lambda_L(n)}n
=O\bigl(d(\sqrt y+\log Q)\bigr).
\]
For the higher powers use \(\sum_{j\ge2}\sum_{p^j\le y}\log p\ll\sqrt y\) by Chebyshev's bound, and partial summation for the reciprocal tail. The exceptional first powers cost at most \(d\sum_{p\mid Q}\log p\) because each term carries a factor at most one. The implied constant is absolute.

Thus the same one-sided late-window criterion, including its exponent and window endpoints, can be stated using \(\Re P_L\). For a uniform \(O_\epsilon(y^{1/2+\epsilon})\) target, the displayed error gives the exact additional degree and discriminant dependence. In the \(S_3\) example the prime coefficient is \(\log p(2\mathbf1_{\mathrm{split}}(p)-\mathbf1_{\mathrm{inert}}(p))\) for \(p\ne23\), since the transposition trace is zero. For \(M/\mathbb Q\) Galois, the unramified coefficient for \(\zeta_M\) is \(d\log p\) at completely split primes and zero at the others. This reduces the unproved Dedekind window to a centered smoothed completely-split-prime estimate. The linear term \(c_*-c\) is required by the exact identity. [Pinned analytic criterion](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84) · [Prior Artin and Dedekind reduction](https://github.com/Sodelin/Research-Commons/blob/5a035053d0a8c6e20841e494eabc362af392d31f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/dedekind-window-asymmetric-goldbach.md#L5-L26).

For \(x^3-x-1\), write \(S(t)=2\theta_{111}(t)-\theta_3(t)\) for the weighted imbalance at unramified primes. The unconditional fixed-field effective Chebotarev theorem gives integrability of \(S(t)/t^2\); the two class densities cancel and any fixed exceptional term has exponent below one. Abel summation at \(s=1\) therefore gives \(c_*=-\int_1^\infty S(t)t^{-2}dt\) and
\[
G_\rho(y)=-y\int_y^\infty S(t)\frac{dt}{t^2}+O(\sqrt y+\log23).
\]
The missing signed estimate is precisely \(\int_y^\infty S(t)t^{-2}dt\ge-C_\epsilon y^{-1/2+\epsilon}\) throughout arbitrarily late windows \([Y,Y^{3/2}]\), for each \(\epsilon>0\). The Hilbert class field description makes the split indicator explicit. The quadratic resolvent of discriminant \(-23\) has three reduced forms \((1,1,6),(2,\pm1,3)\), and the cubic extension over it is unramified, so it is the Hilbert class field. A rational prime \(p\ne23\) splits completely precisely when it is represented by \(a^2+ab+6b^2\). [Lagarias–Odlyzko, Theorem 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf) · [Serre, Lectures on \(N_X(p)\)](https://www.college-de-france.fr/media/jean-pierre-serre/UPL9140953003901187132_14___Lectures_on_N_X.pdf).

A direct factorization into finitely many rational Dirichlet Euler factors reaches exactly the abelian Galois fields over \(\mathbb Q\). In the converse direction, let \(M\) be a normal closure of \(E\), \(G=\operatorname{Gal}(M/\mathbb Q)\), and \(m\) a common multiple of the proposed Dirichlet levels. If \(G\) is nonabelian, take \(1\ne g\in[G,G]\). Both \((1,1)\) and \((g,1)\) are compatible on \(M\cap\mathbb Q(\zeta_m)\) and hence occur as Frobenius classes in the compositum. The coefficient of \(p^{-s}\) in \(\log\zeta_E(s)\) counts fixed embeddings of \(E\), a faithful permutation action of \(G\). It is strictly smaller for \(g\) than for \(1\), whereas the corresponding coefficient of any finite Dirichlet product or quotient is constant on these primes \(p\equiv1\bmod m\). For abelian \(G\), \(E/\mathbb Q\) is Galois and Artin reciprocity supplies the factorization. This obstruction concerns factorization, leaving other proof routes open.

There is an unconditional low-height check by hand in this example. Serre identifies \(L_\rho(s)=L(s,f)\) for \(f(z)=\eta(z)\eta(23z)\), including the Euler factor at \(23\). The Mellin integral of \(f(it)\) gives \((2\pi)^{-s}\Gamma(s)L_\rho(s)\). It converges for every \(s\), by exponential decay at infinity and eta inversion at zero. In particular \(L_\rho(s)>0\) for real \(s>0\) by the positive product on the imaginary axis. In fact, let \(v=\log(\sqrt{23}\,t)\), \(a=2\pi/\sqrt{23}\), and \(w(v)=e^{v/2}f(i e^v/\sqrt{23})\). Eta inversion makes \(w\) even. The real part of the completed Mellin integral is
\[
2\int_0^\infty w(v)\cosh((\Re s-1/2)v)\cos((\Im s)v)\,dv .
\]
When \(0\le\Re s\le1,\ |\Im s|\le1\), the integrand without the factor \(2\) on \(0\le v\le1/2\) is at least \(0.09\cdot0.6\cdot0.875\). Indeed, \(1.3<a<1.4\) and \(q=e^{-a e^v}>0.09\) on this subinterval. For all \(v\ge0\) one has \(q<0.28\) and \(\prod_{n\ge1}(1-q^n)(1-q^{23n})\ge1-q/(1-q)-q^{23}/(1-q^{23})>0.6\). The cosine is nonnegative until \(v=\pi/2\) at least. The absolute negative contribution is at most \(\int_{\pi/2}^\infty e^v e^{-a e^v}dv=e^{-a e^{\pi/2}}/a<0.003\), whereas the positive contribution on \([0,1/2]\) exceeds \(0.02\). Thus the completion is nonzero on this rectangle, and \(L_\rho\) has no zeros in its intersection with the open strip. This addresses only low height. [Serre, §2.1.2, pp. 16–17](https://www.college-de-france.fr/media/professeurs-honoraires/UPL47720_cours_Taiwan_avril__10juin_2011_.pdf#page=16) · [Eta inversion](https://dlmf.nist.gov/23.18).

## A stronger asymmetric sieve with no large-prime hypothesis

Write \(L=\log N,\ H=\sqrt N,\ W=\exp(L^\gamma)\), and \(Y=\lfloor\exp(L^{\delta/2})\rfloor\), with the original fixed positive parameters. Retain the symmetric square-root block \(q,h\in(H/2,H]\), original middle-count mask, squarefree \(m=qh\), \((m,N)=1\), and \(n=d\ell=N-m\) which is \(Y\)-rough. Consider the exact sector with \(d\ge H\), \(q,h\) both \(W\)-rough, and \(\mu(m)=-1\). It allows both parities of \(n\) and permits composite \(d\). On each dyadic shell \(B<\ell\le2B\) with \(B\ge Y/2\), additionally restricting \(\ell\le N^{1/2-\kappa}\) for any fixed \(\kappa>0\), the signed weight is
\[
\ll_{\kappa,\gamma,\delta}
 \frac{N(1+\log L)\log(2B)}
 {(\log W)^2(\log Y)^2}.
\tag{1}
\]
No restriction on the sizes of the prime factors of \(q,h\) beyond \(W\)-roughness is imposed. The range can also be intersected with any \(q,h\)-swap-invariant part of the original support.

Indeed, reflection \(q\leftrightarrow h\) replaces the summand \(-\mu(h)\mu(d)\log h\log\ell\) by \(-\tfrac12\mu(h)\mu(d)\log(h/q)\log\ell\), bounded by \(O(\log\ell)\). For fixed \(q,\ell\), solvability forces \((q,\ell)=1\) and \((q\ell,N)=1\). Write \(h=h_0+\ell t\) and \(d=(N-qh_0)/\ell-qt\). The interval has length at most \(O(H/\ell)\) and \(H/\ell\ge N^\kappa\). Sift \(h\) up to \(W\) and \(d\) up to \(Y\). For odd primes outside \(q\ell N\) there are two distinct excluded roots below \(\min(W,Y)\) since the determinant is \(N\), and one root between the smaller and the larger threshold. The exceptional factors cost at most \(g(q)g(\ell)g(N)\), with \(g(v)=\prod_{p\mid v,\ p>2}(p-1)/(p-2)\). A root for a form of constant value modulo \(p\mid q\ell\) cannot be an identically zero form by the coprimality conditions. Omit the prime \(2\). The CRT error for each squarefree modulus is at most its number of excluded residue classes. The upper Brun sieve with local densities at most \(2/p\) therefore gives
\[
\ll (H/\ell)\,\frac{g(q)g(\ell)g(N)}{\log W\log Y},
\]
since its error, a fixed power of \(\max(W,Y)\), is \(N^{o(1)}\) and is absorbed by the displayed term. [Upper Brun sieve, Theorem 8.5.2 as quoted on p. 50](https://pub.math.leidenuniv.nl/~evertsejh/Fundamental%20Lemma.pdf).

For rough \(q,\ell\le N\), the factors \(g(q),g(\ell)\) are bounded uniformly, using \(\sum_{p\mid v}1/p\le(\log v)/(\min p\mid v)\) for \(v>1\). The number of \(W\)-rough \(q\) in the block is \(O(H/\log W)\). To upper bound the number of \(Y\)-rough \(\ell\in(B,2B]\), sieve to \(\min(Y,B^c)\) with a sufficiently small fixed \(c>0\). Its logarithm is comparable to \(\log Y\) for \(B\ge Y/2\) and its sieve remainder is smaller than \(B/\log Y\). The count is \(O(B/\log Y)\). Summing the reflected weights proves (1), since \(g(N)\ll1+\log L\). The endpoint \(\ell=1\) has zero weight, while \(1<\ell\le Y\) is excluded by roughness.

Summing (1) up to \(V=\exp(L^\sigma)\) gives \(O(N(1+\log L)L^{2\sigma-2\gamma-\delta})\), hence \(o(N)\) for \(\delta/2<\sigma<\gamma+\delta/2\). A single shell with \(\log B\asymp L^\sigma\) gives \(O(N(1+\log L)L^{\sigma-2\gamma-\delta})\), hence \(o(N)\) for \(\sigma<2\gamma+\delta\). For \((\gamma,\delta)=(.10,.01)\), the cumulative and single-shell thresholds are respectively \(.105\) and \(.21\). A union of shells costs the sum of their log scales, so the shell bound does not give the larger threshold for a full interval. This is a pointwise hand estimate. [Earlier asymmetric sieve](https://github.com/Sodelin/Research-Commons/blob/5a035053d0a8c6e20841e494eabc362af392d31f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/dedekind-window-asymmetric-goldbach.md#L28-L58).


The roughness cutoff \(W\) is independent of the lower endpoint of the middle-count mask. One can take \(W=\exp(L^\omega)\) for any fixed \(0<\omega<\beta\), with the original mask intersected with \(W\)-roughness. The formulas above then use \(2\omega\) in place of \(2\gamma\). For the absolute original weight in both \(m\)-parities, the same argument costs one additional factor \(L\) because no reflection saving is used. Thus when \(2\omega+\delta>1\) the odd-\(m\) estimate is \(o(N)\) on each individual dyadic shell up to \(\ell\le N^{1/2-\kappa}\), even if \(\log B\asymp L\). This does not sum over all polynomial-scale shells.
