# Least-prime pairing for admitted triple complements

This is a pointwise hand bound on part of the exact larger-divisor center. Unlike the short-complement graph estimate, it allows admitted divisors with three or more prime factors. [Exact center and strict cutoff](https://github.com/Sodelin/Research-Commons/blob/bd417b56fe190a8a34918fb5b9405acb4c6d735d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md).

Keep the original fixed even target \(N\), let \(L=\log N,\ H=\sqrt N\), and write \(P=H^a\) with \(1<a<20/19\) fixed. As in the center, \(q,h\) are in the square-root block with a swap-invariant mask, \(m=qh\) is squarefree with \((m,N)=1\), and \(n=N-m\) is squarefree and \(Y\)-rough with \(\log Y\asymp L^\theta\), \(0<\theta<1\) fixed. Use the strict cutoff \(d>P\) on \(d\ell=n\), hence \(X=n/P\) and \(\ell<X\). Choose fixed \(0<\sigma<1\), \(0<\kappa<2(1-\theta)\), and use
\[
 V_0=\exp(L^\sigma),\qquad z=\exp(c_0 L/\log L)
\]
for a small fixed \(c_0>0\). Retain endpoints whose least prime \(p\le V_0\) and with at most \(\kappa\log L\) prime factors at most \(z\). These extra tests concern \(n\), so preserve the exact \(q,h\) swap. Put
\[
 r_\theta(\kappa)=\kappa\bigl(1+\log(2(1-\theta)/\kappa)\bigr).
\]
On odd Möbius parity of \(m\), the sum of absolute grouped orbit weights over this entire sector is
\[
 \ll N L^{\sigma-1+r_\theta(\kappa)+o(1)}+N^{.9+o(1)}+O_A(N/L^A).
\]
Thus it is \(o(N)\) whenever \(\sigma+r_\theta(\kappa)<1\). For example, \(\theta=.005,\ \sigma=.85,\ \kappa=.02\) gives a strictly negative exponent. The estimate applies in particular to the even-\(n\) center and imposes no maximum size on the individual admitted complements besides \(\ell<X\).

## Exact pairing at the least prime

For every such \(n\), split the divisor sum into pairs \(v,pv\):
\[
 \sum_{\substack{\ell\mid n\\\ell<X}}-\mu(\ell)\log\ell
 =\log p\sum_{\substack{v\mid n/p\\v<X/p}}\mu(v)
  -\sum_{\substack{v\mid n/p\\X/p\le v<X}}\mu(v)\log v .
\]
On the first range both members of the pair are admitted and combine to the small weight \(\log p\). At \(v=X/p\), the partner equals the strict cutoff and is excluded, so it belongs to the second range. The original signed \(d\)-sum is this expression times \(\mu(h)\mu(n)\log h\). Grouping \(q,h\) by the swap changes the block log factor to \(\log(h/q)\) on the odd-\(m\) sector, of absolute size at most \(\log2\). Thus charge the interior once at \(\ell=pv<X\) with weight \(\log p\), and the boundary at \(\ell=v\) with weight \(\log\ell\). Neither charge requires a sign estimate on \(v\).

Discard \(n<N/L^B\) at arbitrary log savings by the absolute endpoint bound, with \(B\) sufficiently large. The boundary then lies in the fixed band \(N/(P L^B V_0)\le\ell<N/P\), of logarithmic width \(O(L^\sigma+\log L)\). Every allowed \(\ell\) is \(<H\). [Endpoint trim](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-endpoint-trim.md).

## Sieve and reciprocal charges

Write \(d=A b\) where \(A\) is the exact product of the primes \(\le z\) in \(d\). Then \(A\le z^{\kappa\log L}=N^{c_0\kappa}\), and \(b\) is \(z\)-rough. Fix \(A,\ell\) and count the congruence \(qh=N\bmod A\ell\) with the \(b\)-roughness test, using the prior polynomial-level upper sieve of level \(N^{1/100}\). It applies with the present \(z\): the ratio of the log level to \(\log z\) tends to infinity. At fixed \(A,\ell\) the main bound is \(O(N/(A\ell\log z))\). The modulus is a unit modulus for \(N\) on the exact support and is \(Y\)-rough. Omitting any primes dividing \(A\ell\) costs a bounded Euler factor. The error, using the residue-box bound, has size \(O(N^{.03+o(1)}[(A\ell)^{1/2}+H/(A\ell)^{1/2}])\). Summing over \(A\le N^{c_0\kappa}\) and \(\ell\le H\), including logs or marked choices, costs \(N^{.78+1.5c_0\kappa+o(1)}\). Fix \(c_0\) small enough to make this \(O(N^{.9+o(1)})\). [Polynomial sieve with exceptions](https://github.com/Sodelin/Research-Commons/blob/be190409fedb5f8c5de58bc2958d618dd1eb2821/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/polynomial-rough-large-divisor.md).

Across \(A\) and the small-prime part of \(\ell\), there are at most \(\kappa\log L\) selected primes from \((Y,z]\), with two possible assignments. Their reciprocal sum is bounded by
\[
 \sum_{j\le\kappa\log L}\frac{(2\sum_{Y<p\le z}1/p)^j}{j!}
 \ll L^{r_\theta(\kappa)+o(1)}.
\]
This follows by Mertens and factorial growth up to the cutoff. The unmarked primes \(>z\) of \(\ell\) cost at most \(\prod_{z<p\le H}(1+1/p)\ll\log L\).

For the interior, the marked prime \(p\le V_0<z\) pays for \(\log p\) at reciprocal cost \(O(\log V_0)\) by Chebyshev. Apply the preceding bound to the other selected primes. For the boundary, the band is at polynomial scale \(N^{1-a/2-o(1)}\). By making \(c_0\kappa<(1-a/2)/2\), the small-prime part supplies less than half the log of \(\ell\). Therefore \(\log\ell\le2\sum_{r\mid\ell,r>z}\log r\). Mark such a prime \(r\). At every fixed remaining product, the interval for \(r\) has logarithmic width \(O(L^\sigma+\log L)\). Summing \(\log r/r\) by Chebyshev costs \(O(1+L^\sigma+\log L)\). The remaining large-prime factors still cost \(O(\log L)\). These two charges, multiplied by \(N/\log z\ll N\log L/L\), give the claimed estimate.

This removes a genuine triple-admitting slice as well as the no-triple cases that satisfy the new count condition. On the even-\(m\) sector the swap retains a factor \(\log m\), so this argument alone does not give the corresponding saving there.


## Fixed-count case and both-parity tails

If the endpoint has at most a fixed number \(j\ge1\) of primes at most \(z=N^{c_0}\), choose \(c_0>0\) sufficiently small in terms of \(j\). The same argument permits **every** bound \(p\le V_0=N^{o(1)}\) in the odd-\(m\) sector. Put \(T=\log(2V_0)\). The unmarked primes above \(z\) now cost \(O_{c_0}(1)\). Once the least prime \(p\) is marked, all other small primes exceed \(p\) and there are at most \(j-1\) of them. Their reciprocal cost is
\[
 O_j\bigl((1+\log(L/\log p))^{j-1}\bigr)
\]
by the squarefree factorial bound with both assignments. In the boundary charge remember \(p\) in \(A\); it does not divide \(\ell=v\). The log width is then \(B\log L+\log p\). For the term involving \(\log p\), dyadically decompose the range of \(\log p\) below \(T\). The weighted prime sum in the \(i\)-th interval is \(O(T2^{-i})\) by Chebyshev, and the remaining cost there is \(O_j((1+\log(L/T)+i)^{j-1})\). The total is \(O_j(T(1+\log(L/T))^{j-1})\). The \(B\log L+1\) part contributes at most \(O_j((1+\log L)^{j+1})\); the marked prime then has reciprocal weight only. The same \(\log p\) estimate applies to the interior charge. The net upper bound is
\[
 \ll_j \frac NL\left[T(1+\log(L/T))^{j-1}+(1+\log L)^{j+1}\right]+N^{.9+o(1)}+O_A(N/L^A),
\]
which is \(o(N)\) whenever \(T=o(L)\) for fixed \(j\). Remembering the marked least prime costs at most \(j\) choices per pair \(A,\ell\) in the lattice error.

For the growing-count version, the exact middle-count tilt can be combined with the sieve and permits either \(m\)-parity on sufficient tails. In the sieve for fixed \(A,\ell\), use the upper sieve outside the original middle interval and the nonnegative exact-count and roughness polynomials inside it, as in the previous polynomial-rough note. The present \(z\) still eventually exceeds the entire middle interval. Conditional on local survival, the distinct \(qh=0\bmod p\) flags in that interval have means \(2/p+O(p^{-2})\) off \(A\ell N\); the removed primes contribute \(o(1)\) to the mean since they exceed \(\exp(L^\gamma)\). The same tilted atom bound therefore multiplies the main term by \(L^{-I(t)}/\sqrt{\log L}\), where \(t\) is the middle-count threshold and \(I(t)=t\log(t/[2(\beta-\gamma)])-t+2(\beta-\gamma)\). This costs only subpower additional sieve moduli, as before. Restoring the \(O(L)\) block weight on either parity now gives \(o(N)\) on a tail with \(I(t)>\sigma+r_\theta(\kappa)\), even with admitted triple complements. [Exact middle-count tilt with polynomial sieve](https://github.com/Sodelin/Research-Commons/blob/be190409fedb5f8c5de58bc2958d618dd1eb2821/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/polynomial-rough-large-divisor.md#middle-count-tails-recover-a-bound-in-both-block-parities).


## Sharper growing-count threshold using the least-prime order

In the growing-count case, retain the least prime \(p\) in both charges. In the first it is a marked factor of \(\ell=pv\), and in the second it is a marked factor of \(A\). Every other small selected prime across \(A,\ell\) exceeds \(p\), so the factorial parameter can be replaced by \(2\sum_{p<r\le z}1/r\). The boundary log width is \(B\log L+\log p\ll\log p\), since \(p>Y\).

Partition the range of \(\log p\) dyadically, and at scale \(L^\xi\) use \(\sum\log p/p\ll L^\xi\). The factorial parameter is at most \(2(1-\xi)\log L+O(1)\) by Mertens. Thus, for \(0<\kappa<1-\sigma\), the odd-\(m\) exponent is at most
\[
 \max_{\theta\le \xi\le\sigma}\{\xi-1+\kappa(1+\log(2(1-\xi)/\kappa))\}
 =\sigma-1+\kappa(1+\log(2(1-\sigma)/\kappa)).
\]
The derivative of the expression in braces is \(1-\kappa/(1-\xi)>0\), giving the last equality. Harmless \(o(1)\) from dyadic endpoints or log powers is included in the bound. The lattice error is unchanged since at most \(O(\log L)\) choices can be marked in each \(A,\ell\). This improves the strict saving range. For example, \(\sigma=.9,\ \kappa=.03\) gives a main exponent below \(-.013\), and \(\sigma=.75,\ \kappa=.08\) gives one below \(-.023\). For either block parity after the middle-count tilt, require \(I(t)>\sigma+\kappa(1+\log(2(1-\sigma)/\kappa))\). These claims still allow admitted triple complements.
