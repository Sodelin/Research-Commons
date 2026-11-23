# Central count atoms and marked allocation swaps on the Goldbach semiprime shell

These are hand deductions at each even target \(N\). Put \(H=\sqrt N\), \(L=\log N\), \(D=H^{20/19-\varepsilon_d}\) for fixed \(0<\varepsilon_d<1/19\), and \(Y=\exp(L^{.005})\). Keep \(q,h\in(H/2,H]\), squarefree \(m=qh\), \((m,N)=1\), and the original cofactor and exact center masks. In particular, take \(Y\)-rough squarefree semiprime \(n=d\ell=N-m\) with \(d>D\) in the original orientation. The \(\ell=1\) weight vanishes. Otherwise \(d,\ell\) are prime. Use the peer shell \(N^{1/10}<\ell\le N^{1/8}\), or subsets of it as specified below. The exact weight is \(w=-\mu(h)\mu(d)\log h\log\ell\). [Pinned center and fixed-divisor transfer](https://github.com/Sodelin/Research-Commons/blob/6c808c9a13b93fd394ddd7888aa8f45e36a55c46/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-count-transfer-2107z.md).

## Selected count profiles

Write \(X_0,X_1,X_2\) for the distinct-prime counts of \(m\) in \([2,\exp(L^{.10})]\), \((\exp(L^{.10}),\exp(L^{.9896})]\), and \((\exp(L^{.9896}),\exp(L^{.99})]\), respectively. Their conditional model means are \(\lambda_i\log L+O(1+\log\log L)\), with \(\lambda=(.20,1.7792,.0008)\). Keep the original masks \(.25\log L<X_1+X_2<8\log L\), \(X_0+X_1>.0153\log L\), and at most one prime factor of \(m\) in \((\exp(L^{3/4}),2\exp(L^{3/4})]\). For odd \(m\), also keep more than \(.0029\log L\) prime factors of \(m\) at most \(\exp(L^{.95})\). Further restriction to the three typical count intervals is allowed.

For each allowed \(\ell\), let \(E_\ell\) be a chosen collection of count triples. On \(\mu(m)=-1\), the sum of the absolute values of the reflected weights with \(\mathbf X\in E_\ell\) is
\[
\ll_A \frac NL\sum_{\ell\ \mathrm{allowed}}\frac{\log\ell}{\ell}
\min\!\left(1,\frac{|E_\ell|}{(\log L)^{3/2}}\right)+\frac N{L^A}
\tag{1}
\]
for each fixed \(A>0\). The same bound holds with the minimum replaced by \(\min(1,|F_\ell|/\sqrt{\log L})\) if only one coordinate is restricted to a set \(F_\ell\) of integer values.

For fixed \(\ell\), the pinned sieve law consists of independent Bernoulli flags across primes and hence independent counts across the three disjoint prime intervals. The flag probability is zero for \(p\mid\ell N\), and otherwise is \((2p-1)/(p^2-p+1)=2/p+O(p^{-2})\). Each count's variance is \(\asymp\log L\) uniformly in \(\ell,N\). Indeed the omitted primes of \(N\) have reciprocal mass \(O(1+\log\log L)\), and the squared flag probabilities have bounded sum. For a Bernoulli parameter \(u\), its Fourier factor has squared modulus \(1-4u(1-u)\sin^2(t/2)\). Fourier inversion bounds every atom by \((2\pi)^{-1}\int_{-\pi}^{\pi}e^{-2V\sin^2(t/2)}dt=O(V^{-1/2})\), where \(V\) is the sum of the flag variances. The product law therefore bounds each triple atom by \(O((\log L)^{-3/2})\).

Apply the pinned fixed-\(\ell\) count with the chosen \(E_\ell\). Its sieve transfer and error are uniform in the chosen set, so the sets need not match across \(\ell\). The large-count trim and the accumulated CRT error give the remainder in (1) after restoring the weights. On odd \(m\), taking \(q<h\) pairs the original \(q,h\) terms with exact weight \(-\mu(h)\mu(d)\log(h/q)\log\ell\), whose magnitude is \(O(\log\ell)\). The support and each count mask stay invariant under the swap. [Pinned conditional law and error](https://github.com/Sodelin/Research-Commons/blob/6c808c9a13b93fd394ddd7888aa8f45e36a55c46/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-count-transfer-2107z.md#transfer-of-the-joint-counts-for-fixed-prime-ell).

Over the full shell, \(\sum\log\ell/\ell\ll L\). Thus one chosen triple per \(\ell\) costs \(O(N/(\log L)^{3/2})\). Keeping at most \(O((\log L)^{1/2-\eta})\) values in one coordinate for fixed \(\eta>0\) costs \(O(N/(\log L)^\eta)\). On a single dyadic prime-\(\ell\) shell the harmonic sum is \(O(1)\), so the bounds have an additional factor \(L^{-1}\) in the main term. Partitioning all typical profiles into atoms and summing these estimates does not give a saving on the whole typical region.

## Marked parity-changing allocations

For each \(m\), choose at most one marked pair of coprime divisors \(a,b\mid m\) by a rule depending only on \(m\), with \(\mu(a)\mu(b)=-1\) and \(|\log(a/b)|\le\eta\). Here \(0<\eta\le1\) may depend on \(N\). Retain placements with the marks on opposite cofactors and with their exchanged placement still satisfying the original support. For example, if \(a\mid q\) and \(b\mid h\), set
\[
(q',h')=(qb/a,ha/b).
\]
Use the reversed rule on the other allocation. The map is an involution. It fixes \(m,n,d,\ell\) and all masks on the products. It keeps each of the two placements inside the same strict cofactor and divisor cutoffs by the admissibility condition. Squarefreeness gives \(\mu(h')=\mu(h)\mu(a)\mu(b)=-\mu(h)\). The sum of the two original weights is therefore
\[
w(q,h,d,\ell)+w(q',h',d,\ell)
=-\mu(h)\mu(d)\log\ell\,[\log h-\log h'],
\]
of magnitude at most \(\eta\log\ell\). The pinned prime-\(d\) count with no added count restriction bounds the total marked contribution, in either \(m\) parity, by
\[
\ll_A \eta\frac NL\sum_{\ell\ \mathrm{allowed}}\frac{\log\ell}{\ell}+N/L^A .
\tag{2}
\]
This is \(O(\eta N)+O_A(N/L^A)\) across the full semiprime shell. The statement concerns the selected marked support. It makes no assertion about how much of the typical shell admits such a mark.

If there are two canonically marked pairs with disjoint prime supports, each of opposite Möbius parity, keep the placements where both are on opposite cofactors and all four independent exchange choices are admissible. This four-element orbit sums to zero exactly. The Möbius sign flips under each exchange and the two increments of \(\log h\) add independently, so its alternating second difference vanishes. This exact cancellation allows either \(m\) parity and requires no small-ratio condition.

The unrestricted typical shell still requires a signed bound on the occurrences outside these selected supports. The proofs here use the pinned fixed-target sieve and exact finite identities. They have no Lean or numerical verification.

## Transfer to the explicit Type II sum

Use the peer Vaughan expansion on this same band, with its original fixed \(U,V\) and optional endpoint trim. The Type II expression can inherit \(\ell\)-dependent selected-count bounds even though its \(d=uv\) can be composite. Partition the selected support by its exact count triple \(\mathbf k\). For each \(\mathbf k\), restrict the prime coefficient index \(\ell\) to \(\{\ell:\mathbf k\in E_\ell\}\) and multiply \(F(m)\) by \(\mathbf 1_{\mathbf X=\mathbf k}\). In the Type I proof the restricted \(\ell\) set stays inside the two grouped coefficients \(A_i(r,t)\). Their bounds are unchanged and uniform in the set. The new \(m\) mask is a single allowed count projector, with uniform Fourier mass within the previous cap. The number of triples in the typical intervals is \(O((1+\log L)^3)\). Summing the Type I and prime-power errors with a larger log-saving parameter therefore gives
\[
 S_E(N)=T_{{\rm II},E}(N)+O_A(N/L^A).
\]
Here both sides keep the selected profiles, with the original prime \(d\) test on \(S_E\) and its prescribed removal on \(T_{{\rm II},E}\). Thus the signed Type II sum on the selected profiles satisfies the bound (1), and the same holds for the thin-marginal version. This argument uses the prime-\(d\) sieve only on \(S_E\). [Pinned Type I reduction](https://github.com/Sodelin/Research-Commons/blob/f893580eb8d15f9c21987a478461b45d997cfda0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md)

The four-element marked cancellation also lifts exactly to the expanded Type II sum by fixing \(\ell,u,v,m\). All arithmetic coefficients other than \(\mu(h)\) stay fixed, and \(\log(h/q)\) has additive increments under the two independent swaps. The original alternating second difference remains zero on each admissible orbit. The full typical Type II sum outside these selected supports is still open.

