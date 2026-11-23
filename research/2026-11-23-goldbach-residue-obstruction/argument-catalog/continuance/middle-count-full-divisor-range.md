# The original middle-count mask gives a full-range saving on a rough block

This is a pointwise hand deduction on the original exact long-divisor support. It uses the original endpoint threshold \(Y\). The added restriction concerns \(q,h\).

Let \(L=\log N,\ H=\sqrt N,\ Z=\exp(L^\beta),\ \delta=1-\beta\), and \(Y=\lfloor\exp(L^{\delta/2})\rfloor\). On the original square-root block, retain the conditions \(q,h\in(H/2,H]\), the strict cofactor cutoff, squarefree \(m=qh\), \((m,N)=1\), and \(d>D\), \(d\ell=N-m>0\), with \(d\ell\) \(Y\)-rough. Write \(k(m)\) for the number of distinct prime divisors in \((\exp(L^\gamma),Z]\). Retain the original mask \(\alpha\log L\le k(m)\le K=\lfloor8\log L\rfloor\), with \(\alpha=1/4\) in the project. Additionally suppose \(q,h\) are both \(W\)-rough, where \(W=\exp(L^\omega)\) with \(\max(\gamma,\delta/2)<\omega<\beta\). Define
\[
 b_0=2(\beta-\omega),\qquad
 I=\alpha\log(\alpha/b_0)-\alpha+b_0,
\]
and assume \(b_0<\alpha\). For this sector, uniformly at each even \(N\), the total absolute weight of the original summands is
\[
 \ll N(1+\log L)L^{3-2\omega-\delta-I}+N^{3/4+o(1)}.
 \tag{1}
\]
On the sub-sector \(\mu(qh)=-1\), the signed contribution is
\[
 \ll N(1+\log L)L^{2-2\omega-\delta-I}+N^{3/4+o(1)}.
 \tag{2}
\]
Both estimates are for all \(d>D\), with no balance requirement on \(d,\ell\) and no parity restriction on \(d\ell\).

For example, with \((\beta,\gamma,\delta)=(.99,.10,.01)\), \(\omega=.95\) gives \(I>.1148\) and (2) is \(O(N(1+\log L)L^{-.0248})\). With \(\omega=.9896\), \(I>1.18\) and (1) is \(O(N(1+\log L)L^{-.16})\). Any prescribed logarithmic saving in (1) follows by taking a fixed \(\omega\) sufficiently close to \(\beta\), at the cost of restricting the block more strongly. The constants and onset need not be uniform as \(\omega\uparrow\beta\).

## Proof

**Count by the smaller factor.** For each placement choose \(s=\min(d,\ell)\le H\); for fixed \(q,h,s\) there are at most two orientations of the original pair. The chosen factor is \(Y\)-rough and \((s,N)=1\). The other factor \((N-qh)/s\) is also \(Y\)-rough. For \(s>1\), it is enough to bound the number of pairs in a dyadic shell \(B<s\le2B,\ s\le H\); then \(B\ge Y/2\). The case \(s=1\) may include the orientation \(d>D,\ell=1\), which has zero weight. The orientation \(d=1\) is excluded for large \(N\).

Put \(t=\alpha/b_0>1\). On the exact support, all intermediate prime factors of \(m\) are in \((W,Z]\), and \(k(m)=k(q)+k(h)\). Bound the indicator of \(k(m)\ge\alpha\log L\) by \(t^{k(q)+k(h)-\alpha\log L}\). Expand the power over divisors \(a\mid q,b\mid h\) made of distinct primes in \((W,Z]\), with weight \((t-1)^{\omega(a)+\omega(b)}\), where \(\omega(v)\) here counts distinct prime factors. Because \(k(m)\le K\), only \(\omega(a)+\omega(b)\le K\) is necessary. All coefficients are nonnegative, so we may enlarge each expanded count after this truncation. The number of pairs \(a,b\), including their weights, is \(N^{o(1)}\) because \(a,b\le Z^K\) and \(t\) is fixed.

**Joint count for each forced divisor pair.** Write \(q=au,\ h=bv\). If \((ab,s)>1\) no solutions survive. For \((ab,s)=1\) the base congruence is \(abuv\equiv N\bmod s\), with a unit right side on scaling. The \(W\)-roughness tests on \(q,h\) and the \(Y\)-roughness test on \((N-qh)/s\) have unchanged local densities at every active prime, because all primes dividing \(ab\) exceed \(W>Y\). For odd \(p\nmid sN\) where all three tests are active, the two forbidden sets \(qh=0\) and \(qh=N\bmod p\) are disjoint with total size \(3p-2\). If \(p\mid N\), they coincide and the associated factor increases by at most \((p-1)/(p-2)\). At \(p\mid s\), the tests on \(q,h\) are automatic and \(p>Y\). This leaves total survival product \(O((1+\log L)/((\log W)^2\log Y))\).

Use upper Bonferroni at \(O(\log L)\) primes. Its density tail is \(O_A(L^{-A})\) since the sum of local bad probabilities is \(O(\log L)\). For each selected modulus \(e\) there are at most \(e^2=N^{o(1)}\) residue boxes for \(u,v\) modulo \(e\); \((e,s)=1\), so each reduces to a modular hyperbola modulo \(s\). Complete periods, mixed complete/short periods and the Kloosterman rectangle estimate give total error \(O(s^{1/2+o(1)}(1+H/s))\) per box. The main factor before local sifting is \(H^2\varphi(s)/(4ab s^2)\) because the real interval lengths are \(H/(2a)\), \(H/(2b)\) before the modulus-\(e\) split. All sieve boxes, forced divisor weights and later log weights cost only \(N^{o(1)}\) in the error. Summing over \(s\le H\) costs \(N^{3/4+o(1)}\). [Rectangular count, Shparlinski fixed-rectangle equation (10)](https://arxiv.org/pdf/1103.2879) · [Estermann](https://doi.org/10.1112/S0025579300002187).

The forced-divisor reciprocal sum with weights is at most
\[
\prod_{W<p\le Z}\bigl(1+(t-1)/p\bigr)^2
\ll L^{b_0(t-1)} .
\]
Multiplying by \(t^{-\alpha\log L}\) gives \(O(L^{-I})\). In each shell \(\sum_{s\ {\rm rough}}\varphi(s)/s^2\ll1/\log Y\) by the one-dimensional upper sieve, using the cutoff \(\min(Y,B^c)\) for a sufficiently small fixed \(c>0\). Thus the shell count is \(\ll N(1+\log L)L^{-2\omega-\delta-I}\) plus the summable error above. [Upper sieve, p. 50](https://pub.math.leidenuniv.nl/~evertsejh/Fundamental%20Lemma.pdf).

**Restore the weights.** The original weight has absolute value at most \(L^2\); \(O(L)\) dyadic shells then give (1). When \(m\) is squarefree and \(\mu(m)=-1\), the exact \(q,h\) symmetry averages the signed weight to \(-\frac12\mu(h)\mu(d)\log(h/q)\log\ell\), of size \(O(L)\). The additional roughness and smaller-factor partition preserve that symmetry. This gives (2). Choosing the smaller factor was only an upper-counting device, so there was no signed reflection in \(d,\ell\).

The improvement comes from the original middle-count lower cutoff combined with restricted \(q,h\) roughness. The argument does not bound the part in which either \(q\) or \(h\) has a prime factor \(\le W\). It uses no GRH input and makes no assertion about strong Goldbach as a whole.
