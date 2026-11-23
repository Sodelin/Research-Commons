# A joint factor-count cut on the exact Goldbach divisor graph

Keep the pinned fixed-target support. Write \(L=\log N\), \(H=\sqrt N\), \(D=H^{20/19-\varepsilon_d}\) with fixed \(0<\varepsilon_d<1/19\), and \(Y=\exp(L^{.005})\). Let \(q,h\in(H/2,H]\), \(m=qh\), and \(n=d\ell=N-m\), with both products squarefree, \((m,N)=1\), \(n\) \(Y\)-rough, and the original strict orientation \(d>D\). Keep the original count and center masks. The graph condition is that no three distinct primes of \(n\) have product strictly below \(X=n/D\). The weight is \(w=-\mu(h)\mu(d)\log h\log\ell\). [Pinned support and graph count transfer](https://github.com/Sodelin/Research-Commons/blob/6c808c9a13b93fd394ddd7888aa8f45e36a55c46/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-count-transfer-2107z.md).

Let \(X_0,X_1,X_2\) count the distinct prime factors of \(m\) in \([2,\exp(L^{.10})]\), \((\exp(L^{.10}),\exp(L^{.9896})]\), and \((\exp(L^{.9896}),\exp(L^{.99})]\), respectively. Put \(\lambda=(.20,1.7792,.0008)\) and
\[
\mathcal I(x)=\sum_{i=0}^{2}\big[x_i\log(x_i/\lambda_i)-x_i+\lambda_i\big],
\qquad 0\log 0=0.
\]
For any set \(E\) of normalized count triples, write \(r=\inf_{x\in E}\mathcal I(x)\). The absolute weight on \((X_0,X_1,X_2)/\log L\in E\), over the full exact no-triple graph, is
\[
\ll_A N L^{1-r}(1+\log L)^8+N/L^A
\]
for every fixed \(A>0\). In particular any fixed rate gap \(r>1\) gives a power saving in \(L\). On odd \(m\), the bound on the sum of absolute paired weights replaces \(L^{1-r}\) by \(L^{-r}\).

## Hand proof

Use the pinned small-endpoint and excessive-count trims. On the remaining support, choose the polynomial sifting limit \(z=N^c\) sufficiently small that \(z^3<X\). The graph condition leaves at most two distinct primes of \(n\) at most \(z\). Write \(d=ab\), where \(a\) is the exact product of these primes belonging to \(d\), so \(b\) passes the sieve to \(z\). For fixed \(a,\ell\), the peer transfer uses the unit hyperbola modulo \(a\ell\). Its conditional local flag law is independent over primes. The probability that \(p\mid qh\) is zero for \(p\mid a\ell N\), and otherwise is
\[
\pi_p=\frac{2p-1}{p^2-p+1}=\frac2p+O(p^{-2}).
\]
The peer transfer, including its CRT error and the two trims, bounds the absolute weight by \(\ll_A NL(1+\log L)^3 P(E)+N/L^A\), where \(P(E)\) is the supremum of the conditional probabilities of \(E\) intersected with the retained count cap. The odd-\(m\) swap preserves all product masks and the individual \(d,\ell\) orientation. On the pair oriented by \(q<h\), its exact weight is \(-\mu(h)\mu(d)\log(h/q)\log\ell\). This replaces the leading \(NL\) in the transfer by \(N\). [Pinned conditional count and error budget](https://github.com/Sodelin/Research-Commons/blob/6c808c9a13b93fd394ddd7888aa8f45e36a55c46/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-count-transfer-2107z.md#extension-to-the-whole-region-with-no-triple-complement).

It remains to bound \(P(E)\). The peer trim restricts the three counts to \(O_A(\log L)\). For an atom \(X_i=j_i\), set \(x_i=j_i/\log L\) and use \(t_i=x_i/\lambda_i\) in the product generating function, with \(t_i=0\) and \(0^0=1\) when \(j_i=0\). These tilts stay in a fixed bounded interval. The logarithm of the generating function is at most
\[
\log L\sum_i \lambda_i(t_i-1)+2\log(1+\log L)+O_A(1).
\]
Indeed the summable \(O(p^{-2})\) errors are uniform in the tilts. The omitted prime factors of \(a\ell\) are at most four and exceed \(Y\). The omitted factors of \(N\) in the two upper prime intervals have total reciprocal mass \(o(1)\). In the lowest interval their reciprocal mass is at most \(\log\log L+O(1)\), by splitting at \(L^2\). Their omission increases the logarithm only when \(t_0<1\), by at most twice that mass. Extracting the atom therefore gives \(\ll_A(1+\log L)^2 L^{-\mathcal I(x)}\). Summing over the \(O_A((1+\log L)^3)\) possible triples and restoring the pinned transfer proves both bounds.

## A new all-parity slice

The condition \(X_2\ge .22\log L\) alone admits a direct tilt \(t_2=275\) with \(t_0=t_1=1\). Its rate is
\[
 r_2=.22\log 275-.2192>1.01632.
\]
For example, \(\log 275=8\log 2+\log(1+19/256)>5.616\), using the first four positive terms of the atanh series for \(\log 2>.6931\) and \(\log(1+x)\ge x-x^2/2\). The exact-support absolute weight is consequently \(O(N/L^{.016})\). This cut is distinct from the two displayed cuts in the pinned note. The count profile \((.20,1,.22)\) has \(K=1.20\) and \(J-K=.02\), outside both of those cut inequalities, with \(J=1.22\) in the original middle window. The profiles in this comparison describe the count masks.

The profile \((.10,.40,.15)\) also lies outside the two displayed cuts, with \(K=.50\), \(J-K=.05\), and \(J=.55\). Each coordinate rate is below one, but their sum is above \(1.4\). For the lower bound use \(\log 4.448<1.5\) and \(\log 187.5>5.2\) in the second and third coordinate rates, giving \(.7792+.6308>1.4\) even before the first coordinate. This is a region of improvement from taking the counts jointly.

The estimate charges an absolute part of the fixed-target ledger. On the remaining typical odd-\(m\) semiprime shell \(N^{1/10}<\ell\le N^{1/8}\), the pinned sieve still gives an \(O(N)\) absolute bound after reflection. A sharper lower bound there needs control of the sign \(\mu(h)\) with both primes \(d,\ell\) and the same target \(N\) fixed. These estimates are hand arguments using the pinned transfer. No Lean or numerical verification is used.
