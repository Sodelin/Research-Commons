# Middle-count tails without roughness on the block factors

A pointwise hand bound for the original exact long-divisor support. This note retains the original roughness of \(n=d\ell\) and removes any extra roughness condition on \(q,h\).

Use \(L=\log N,\ H=\sqrt N,\ \delta=1-\beta,\ Y=\lfloor\exp(L^{\delta/2})\rfloor\). Let \(\mathcal P\) be the primes in \((\exp(L^\gamma),\exp(L^\beta)]\), where \(\gamma>\delta/2\) as in the project. Put \(b=2(\beta-\gamma)\) and \(I(a)=a\log(a/b)-a+b\) for fixed \(a>0\). Retain the original square-root block \(q,h\in(H/2,H]\), strict cofactor cutoff, squarefree \(m=qh\), \((m,N)=1\), the original middle mask \(k(m)\in[\frac14\log L,8\log L]\), and \(d>D,\ d\ell=N-m>0\) with \(d\ell\) \(Y\)-rough. Here \(k(m)\) counts distinct factors in \(\mathcal P\). Intersect this support with one tail: \(k(m)\ge a\log L\) if \(a>b\), or \(k(m)\le a\log L\) if \(a<b\).

On the entire long-divisor range, the absolute original weight is
\[
\ll \frac{N L^{3-\delta-I(a)}}{\sqrt{\log L}}+N^{3/4+o(1)}.
\tag{1}
\]
On \(\mu(m)=-1\), the signed weight is bounded by the same expression with \(3\) replaced by \(2\). On a single dyadic shell of \(\min(d,\ell)\), replace the indicated exponent by one less in either estimate.

For \(\beta=.99,\gamma=.10\), the full-range upper tail is \(o(N)\) starting at the solution to \(I(a)=2.99\) for absolute weight, approximately \(a=5.93314\), and at the solution to \(I(a)=1.99\) for signed odd-\(m\) weight, approximately \(a=5.04423\). Use the exact defining equations at equality. On a single shell, the signed odd-\(m\) lower tail \(k(m)\le .26\log L\) is \(o(N)\) since \(I(.26)>.99\). The decimals here are numerical evaluations of the exponents, independent of the proof.

## Pointwise joint count

Choose \(s=\min(d,\ell)\le H\), allowing at most two orientations. The case \(s=1\) has zero original weight for large \(N\): \(d=1\) violates the cutoff and \(\ell=1\) has \(\log\ell=0\). Fix \(Y\)-rough \(s>1\) coprime to \(N\). The base congruence \(qh=N\bmod s\) has density \(\varphi(s)/s^2\) in the square. In the boxes modulo squarefree auxiliary moduli coprime to \(s\), the CRT leaves the local pair \((q,h)\bmod p\) uniform at every auxiliary prime. For the auxiliary primes \(p\le Y\) the bad event is \(qh=N\bmod p\), because \(p\nmid s\). It has density \((p-1)/p^2\) for \(p\nmid N\) and \((2p-1)/p^2\) for \(p\mid N\). Consequently the product of survival factors is \(O(1/\log Y)\), uniformly in \(N\). At \(p\mid N\) that factor only decreases.

For \(\mathcal P\), use one divisibility label for each coordinate at each \(p\nmid s\). Their sum equals \(k(m)\) on the squarefree original support. Primes \(p\mid s\) make both labels zero. In the CRT density model these labels are mutually independent Bernoulli variables of probability \(1/p\), including the two labels at a single prime. They are independent of the bad events at \(p\le Y\), since \(\mathcal P\) lies above \(Y\). Their sum \(X\) has mean \(\lambda=b\log L+O(1)\) uniformly in \(s\), since removing primes dividing \(s\) changes \(\sum 1/p\) by \(O(L\exp(-L^\gamma))\).

To transfer counts of \(X=j\) to the finite box, for an even \(J\asymp C_A\log L\) use
\[
P_{j,J}(k)=\sum_{i=0}^J(-1)^i\binom{j+i}{j}\binom{k}{j+i}.
\]
For integer \(k\ge j\) this is \(\binom{k}{j}\sum_{i=0}^J(-1)^i\binom{k-j}{i}\), so it is nonnegative and at least \(\mathbf1_{k=j}\). Its excess over that indicator is at most \(\binom{j+J+1}{j}\binom{k}{j+J+1}\), by adjacent Bonferroni truncations. Thus in the independent model the expectation of the excess is at most \(\lambda^{j+J+1}/(j!(J+1)!)\), which is \(O_A(L^{-A})\) by choosing \(C_A\) large, since \(\lambda^j/j!\le e^\lambda\). Use the corresponding even Bonferroni upper polynomial for the absence of all bad primes \(p\le Y\), again with density error \(O_A(L^{-A})\). The two polynomials are nonnegative, so their product is a pointwise upper bound for the joint event. Its expected value factors in the independent model.

Expanding the product over prime labels and bad events involves only \(O_A(\log L)\) primes per term, since \(j\le8\log L\). All moduli, the number of residue pairs in their boxes, the number of terms and their total absolute coefficients are \(N^{o(1)}\), using \(\log Z=(\log N)^\beta\) with \(\beta<1\). Each residue pair reduces \(qh=N\bmod s\) to a rectangular modular hyperbola with unit right-hand side. Splitting complete periods and using the rectangular Kloosterman bound gives error \(O(s^{1/2+o(1)}(1+H/s))\) per box. For the mixed complete and partial periods the error is controlled by the unit-count error \(O(\tau(s))\); complete pairs are exact. Summing over \(s\le H\), all \(j\) in the mask and all weights costs \(N^{3/4+o(1)}\). The CRT main term equals the base area times the expected product established above. [Rectangular count, Shparlinski, fixed-rectangle equation (10)](https://arxiv.org/pdf/1103.2879) · [Estermann](https://doi.org/10.1112/S0025579300002187).

## Tail and weights

Tilt the independent model by \(t^X\) with \(t=a/b\). The normalizing factor is \(F(t)=\prod(1+(t-1)/p)\), over the labels, and \(\log F(t)=b(t-1)\log L+O_t(1)\). Under the tilt the Bernoulli parameters are \(t/(p+t-1)\), so their total variance \(V\) is \(\asymp_t\log L\). Every atom under the tilt has probability \(O_t(V^{-1/2})\): the modulus of the characteristic function is at most \(\exp(-2V\sin^2(u/2))\), and Fourier inversion gives that bound. In the original model \(\Pr(X=j)=F(t)t^{-j}\Pr_t(X=j)\). Summing the geometric series on the indicated side of \(a\log L\) gives the uniform tail bound \(O(L^{-I(a)}/\sqrt{\log L})\). This handles the exact critical exponents in (1).

For each dyadic shell \(B<s\le2B\), with \(B\ge Y/2\), the rough reciprocal sum \(\sum_s\varphi(s)/s^2\ll1/\log Y\) follows from the upper sieve at \(\min(Y,B^c)\) for small fixed \(c>0\). Together with the roughness factor for the other divisor and the count tail, this gives a shell placement bound of order \(N L^{-\delta-I(a)}/\sqrt{\log L}\) plus the summable hyperbola error. The original weight \(-\mu(h)\mu(d)\log h\log\ell\) has size at most \(L^2\), and there are \(O(L)\) shells. In the odd-\(m\) sector, the original \(q,h\) reflection preserves the support and replaces \(\log h\) by \(\tfrac12\log(h/q)\) in the signed weight, saving one factor \(L\). These steps give (1) and its signed form. [Upper sieve, p. 50](https://pub.math.leidenuniv.nl/~evertsejh/Fundamental%20Lemma.pdf).


Two refinements follow from the same proof.

- Let \(a_0>b\) solve \(I(a_0)=3-\delta\) for the absolute estimate, or \(I(a_0)=2-\delta\) for the odd-\(m\) signed estimate. Replace the lower threshold by \(k(m)\ge a_0\log L-c\log\log L\), where \(0\le c<1/(2\log(a_0/b))\) is fixed. The tilt stays in a compact interval above one, so all tilted estimates remain uniform. By \(I'(a_0)=\log(a_0/b)\), the resulting bound is \(O(N(\log L)^{c\log(a_0/b)-1/2})+N^{3/4+o(1)}=o(N)\).
- If \(\ell\le \exp(L^\sigma)\) with \(\delta/2<\sigma<1\), the smaller factor is \(\ell\) for counting purposes whenever \(d\ge\ell\); in all cases one may instead fix \(\ell\) directly because \(\ell<H\) for large \(N\). The proof of the shell bound uses no condition that the fixed divisor is the smaller one. Summing its \(O(L^\sigma)\) shells and charging \(\log\ell\le L^\sigma\) gives absolute exponent \(1+2\sigma-\delta-I(a)\), or signed odd-\(m\) exponent \(2\sigma-\delta-I(a)\), both with the factor \(1/\sqrt{\log L}\). For the lower tail \(a=.26\) the signed bound is \(o(N)\) for \(\sigma\le(\delta+I(.26))/2\), about \(0.51492\) with the original parameters. This controls a cumulative asymmetric slice without roughness on \(q,h\).


The count argument also detects an uneven split between \(q\) and \(h\). Use a separate nonnegative upper polynomial and exponential tilt for the labels on each coordinate. The two sets of labels are independent in the CRT model. For either orientation of \(k(q)\ge a_1\log L,\ k(h)\le a_2\log L\) with \(a_1>\mu_0>a_2>0\), \(\mu_0=\beta-\gamma\), the full absolute estimate becomes
\[
 \ll \frac{N L^{3-\delta-J(a_1)-J(a_2)}}{\log L}+N^{3/4+o(1)},
 \qquad J(a)=a\log(a/\mu_0)-a+\mu_0 .
\]
Uniform error control is unchanged because all polynomial degrees remain \(O_A(\log L)\). For the original parameters, \(a_1=4,\ a_2=.5\) gives \(J(a_1)+J(a_2)>2.99\), so this part is \(o(N)\) even for both parities. It includes tuples whose total count is below the full absolute upper-tail threshold.

A finite check verified the two inequalities for \(P_{j,J}(k)\) in 14,025 cases with \(k\le50,\ j\le24\), and even \(0\le J\le20\). The uniform result uses the hand proof above.
