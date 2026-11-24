# Moving factor-count cuts for the paired Goldbach outer rows

Let \(N=2^k\), \(L=\log N\), \(M=\log L\), \(H=\sqrt N\), and \(\alpha=H/L^{K_0}\) with fixed \(K_0>3\). Use the exact paired outer region \(\alpha<q<h\), \(qh<N\), odd squarefree \(qh\), and exclude the central square \((H/2,H]^2\). On this region both original orientations are admitted with their original strict lower cutoff. The paired weight is
\[
W(q,h)=-\Lambda(N-qh)\big(\mu(h)\log h+\mu(q)\log q\big).
\tag{1}
\]
This includes only paired outer rows. In particular each point is disjoint from the capped unmatched \(A_{02}\) with short divisor at most \(\alpha\), and the earlier central charges remain separate. [Pinned ledger and original bins](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0)

At each sufficiently large \(N=2^k\), the following selections of (1) cost \(o(N)\) in the sum of absolute paired weights. Write \(j=\omega(qh)\).

- If \(\mu(qh)=+1\), take all \(j\le M/3\) or \(j\ge 9M/2\).
- If \(\mu(qh)=-1\), take all \(|j-2M|\ge 10\sqrt{M\log M}\).

There are no assumptions on the individual factors or the roughness of \(qh\) in these selections. They remove the factor-count tails of all paired outer cells at zero cost to the remaining \(0.095N\) budget. The odd-parity unresolved factor-count window has relative width tending to zero around \(2\log\log N\).

## Uniform upper sieve with the largest prime factored out

For \(2\le j\le 8M\), write \(q=u q_0\), \(h=v h_0\), where \(u,v\) are the respective largest prime factors. Their choice is unique. Since \(q,h>\alpha\), each marked prime is at least \(\alpha^{1/j}\). Set \(a=q h_0\), so \(av=qh<N\). At any fixed configuration of \(a,q\), the other marked factor \(v\) and the endpoint \(N-av\) are the two prime forms. Proper prime powers at the endpoint have total cost \(N^{1/2+o(1)}\) across the original paired row, and endpoints \(N-av\le N^{1/8}\) cost \(N^{1/8+o(1)}\), because each endpoint has only \(\tau(qh)=N^{o(1)}\) allocations and weights at most \(L^2\).

Choose the adaptive level
\[
D_a=\left\lfloor\min\left\{\frac{N^{1/2-1/(16j)}}{\sqrt a},\ N^{1/(4j)}\right\}\right\rfloor.
\]
For each configuration of interest, \(\log a<L-\log(\alpha)/j\). Consequently \(\log D_a\asymp L/j\) with absolute constants for the full range \(2\le j\le 8M\). Both retained primes exceed \(D_a\). The upper Selberg square on odd \(v\) gives the number at fixed \(a,q\) at most
\[
 O\!\left(\frac{N j^2\kappa(a)}{a L^2}\right)+D_a^2\exp\!\left(O\!\left(\frac{L}{jM}\right)\right),
 \qquad \kappa(a)=\prod_{p\mid a}\frac{p-1}{p-2}.
\tag{2}
\]
Indeed the local forbidden density at an odd \(p\nmid a\) is \(2/p\), and at \(p\mid a\) it is \(1/p\), since \(N\) has no odd prime factor. Restricting the sieve primes to \(p\le D_a^c\) for small fixed \(c>0\), the unrestricted Euler mass is \(\gg(\log D_a)^2/\kappa(a)\). The mean of the log index under its normalized Euler law is \(O(c\log D_a)\), so at least half its mass lies at index at most \(D_a\). The standard Selberg diagonal therefore gives the main term in (2), including the upper interval length \(N/a\). Its coefficients have magnitude at most one. Each CRT residue count has error at most \(2^{\omega([d,e])}\), where \([d,e]\le D_a^2\). The elementary bound \(\omega(b)\ll\log(2b)/\log\log(3b)\) gives the exponential error factor in (2), uniformly even as \(j\) grows. That bound follows from comparing an integer with \(r\) distinct prime factors to the product of the first \(r\) primes, which is at least \((r+1)!\). [Pinned Selberg diagonal](https://github.com/Sodelin/Research-Commons/commit/b8d0afa3e5fab3380f662ce172eacad56ea05316)

A fixed squarefree \(a\) with \(j-1\) prime factors has at most \(2^{j-1}\) possible divisors \(q\), each fixing \(h_0=a/q\). Thus all errors in (2), with weights at most \(L^2\), are
\[
\ll N L^3\sum_{2\le j\le 8M}2^j
 \exp\!\left(-\frac{L}{8j}+O\!\left(\frac{L}{jM}\right)\right)=o(N).
\tag{3}
\]
This uniform saving uses the individual level cap \(D_a\le N^{1/(4j)}\) when estimating residue multiplicity. A generic \(N^{o(1)}\) factor in that step would not suffice for the moving \(j\)-range.

## Prime harmonic weights and factor-count tails

Let \(r=\omega(q)\), so \(1\le r\le j-1\). At fixed \(q_0\), the possible prime \(u\) lies between \(\alpha/q_0\) and \(N/(\alpha q_0)\), a multiplicative interval of ratio \(L^{2K_0}\), and is at least \(\alpha^{1/j}\). Chebyshev's prime bound and partial summation give the uniform reciprocal estimate
\[
\sum_{u}\frac{\kappa(u)}u\ll\frac{j(1+M)}{L}.
\tag{4}
\]
Here \(\kappa(u)\le2\) for odd prime \(u\). The total reciprocal prime weight \(\sum_{3\le p\le N}\kappa(p)/p\) is at most \(M+C\) for an absolute \(C\), by Mertens and \(\sum_{p>2}1/[p(p-2)]<\infty\). The unordered products \(q_0,h_0\) contain \(r-1,j-r-1\) primes, respectively. Dropping cross-coprimality and other restrictions in this positive upper sum bounds their weighted reciprocal masses by \((M+C)^{r-1}/(r-1)!\) and \((M+C)^{j-r-1}/(j-r-1)!\). Summing over \(r\), their product is at most
\[
T_i=\frac{(2(M+C))^i}{i!},\qquad i=j-2.
\tag{5}
\]

For \(\mu(qh)=+1\), the weight in (1) has magnitude \(\Lambda(N-qh)\log(qh)\le L^2\). For the other parity, its magnitude is \(\Lambda(N-qh)\log(h/q)\ll L(1+M)\) since \(h/q\le N/\alpha^2=L^{2K_0}\). Equations (2), (4), and (5) give normalized positive upper main terms at fixed \(j\) of at most
\[
 O\!\left(\frac{j^3(1+M)}{L}T_i\right)\quad(\mu(qh)=+1),
 \qquad
 O\!\left(\frac{j^3(1+M)^2}{L^2}T_i\right)\quad(\mu(qh)=-1).
\tag{6}
\]
All discarded terms and floors cost \(o(N)\) in aggregate, as above.

For \(x=2(M+C)\), Stirling's lower bound gives \(T_i\le\exp(f(i))\), where \(f(t)=t(1+\log(x/t))\) for \(t>0\), and \(f(0)=0\). The maximum is \(f(x)=x\). For a fixed \(\gamma>0\), \(f(\gamma M+O(1))=(\gamma(1+\log(2/\gamma))+o(1))M\). The coefficients for \(\gamma=1/3\) and \(9/2\) are both strictly below 1. The first inequality uses \(\log 6<2\). For the second, the first two positive terms in the expansion of \(\log(9/4)=2\operatorname{arctanh}(5/13)\) already exceed \(7/9\). The function \(f\) is increasing below \(x\) and decreasing above it. Consequently the sum in the even selections of (6) over \(j\le 8M\) tends to zero.

For the odd selection and \(j\le8M\), one has \(|i-x|\ge 9\sqrt{M\log M}\) for large \(N\). Concavity with \(f''(t)=-1/t\) in a neighborhood of \(x\) yields \(f(i)\le x-13\log M\), first at distance \(9\sqrt{M\log M}\), then everywhere farther away by monotonicity. Thus \(T_i\ll L^2 M^{-13}\). The polynomial factors and at most \(8M\) values of \(j\) in (6) give \(o(1)\) after normalization.

For all \(j>8M\) use a direct Rankin bound. On the squarefree paired support \(j=\omega(q)+\omega(h)\), and \(2^{\omega(t)}\le\tau(t)\). The count, before weights, is at most
\[
2^{-8M}\sum_{\alpha<q<N/\alpha}\tau(q)\sum_{h<N/q}\tau(h)
\ll 2^{-8M} N L^2(1+M).
\]
The last inequality follows from the divisor bound \(\sum_{h\le X}\tau(h)\ll X(1+\log X)\) and its partial-summation consequence \(\sum_{\alpha<q<N/\alpha}\tau(q)/q\ll L(1+M)\). Multiplying by \(L^2\) still gives \(o(N)\), since \(8\log 2>4\). This completes both moving cuts.

## Prime transfer on the factor counts that remain

The following exact involution applies without a restriction on \(j\). For each odd squarefree endpoint \(m\), choose a prime \(p=p(m)\mid m\) invariant across the factorizations of \(m\), for example \(P^-(m)\). If \(p\mid q\), transfer it by replacing \((q,h)\) with \((q/p,ph)\), and reorder the two factors if needed. If \(p\mid h\) do the opposite. The paired bracket (1) is symmetric, so the change of order does not affect its value. For a transfer whose two factorizations remain on the paired outer support, their combined weight, in the notation \(p\mid q\), is exactly
\[
\Lambda(N-m)\big(\mu(h)-\mu(q)\big)\log p.
\tag{7}
\]
In particular each such orbit vanishes for \(\mu(m)=+1\), with no assumptions on other small primes or their allocations. A transfer can fail only if the factor originally carrying \(p\) lies in \((\alpha,p\alpha]\) or if the new pair belongs to the central square. In the latter case, if the carrier was \(q\), then \(q/p>H/2\) and \(ph\le H\), so originally \(q>pH/2>H\) and \(h\le H/p<H/2\). Thus this failure comes solely from the wide \(A_{02}+A_{20}\) contribution. On odd parity (7) has magnitude \(2\Lambda(N-m)\log p\). This rewrites the odd weights but supplies no sign for the resulting sum on generic \(j\).

## Incomplete allocations with small total small-prime product

Fix \(0<\varepsilon<1/10\), put \(Y=N^\varepsilon\), and let \(s\) be the product of all prime factors of \(m\) at most \(Y\). On the full paired outer support, the signed total with \(s\le S_0\) is \(o(N)\) whenever \((1+\log S_0)^3=o(L)\). This statement includes incomplete small-prime allocations and allows the rough cores to be composite.

Indeed any such pair determines two unordered coprime \(Y\)-rough cores \(u,v\) with \(m=suv\), each greater than \(\alpha/s>1\). At fixed \(m,u,v\), potential allocations are \((ub,v(s/b))\) for \(b\mid s\). The group is unique since the product of the small primes was prescribed and the cores of a given allocation are unique. If neither core lies in any interval \([B/s,B]\) for \(B\in\{\alpha,H/2,H\}\), all allocations are in the original paired outer support when any one is. Their total vanishes for \(\omega(s)\ge2\), by summing the two log-weighted Möbius brackets. For \(s=p\) prime, it is \((\mu(u)+\mu(v))\Lambda(N-m)\log p\), which vanishes on even parity. On odd parity the pair has at least one \(Y\)-rough original factor, so the two-form sieve of the preceding rough paired estimate bounds its contribution by \(O(N(1+M)^2/L)+o(N)\) over this whole support. If \(s=1\), both original factors are rough and the both-rough estimate gives \(O(N(1+M)/L)+o(N)\). These two already-proved rough estimates need be counted only once. [Rough paired sieve](https://github.com/Sodelin/Research-Commons/commit/0bcaccdd69d047590e171051120d6c801a4cd527)

For a crossing group, say \(u\in[B/s,B]\), fix \(a=su\) and upper-sieve the \(Y\)-rough variable \(v\) and prime \(N-av\). Allowing either core to cross costs only a factor two. As \(\alpha\le a\le H S_0\), the level \(D_a=\lfloor N^{.499}/\sqrt a\rfloor\) has logarithm comparable to \(L\) and covers two sieve forms through a fixed positive power of \(N\). The same diagonal proof gives main bound \(O(N\kappa(a)/(a L^2))\). At fixed \(s,B\), the reciprocal mass of \(Y\)-rough \(u\in[B/s,B]\) is \(O((1+\log s)/L)\). To see this, cover by \(O(1+\log s)\) dyadic intervals with left endpoint at least \(N^{1/2-o(1)}\) and use the dimension-one upper sieve on each. Also \(\kappa(su)\le\kappa(s)\kappa(u)\) and \(\kappa(u)=1+o(1)\) uniformly on these rough cores. There are at most \(\tau(s)\) allocations per group, each of weight at most \(L^2\). Hence the crossing contribution in absolute value is
\[
 O\!\left(\frac{N}{L}\sum_{s\le S_0}\frac{\mu^2(s)\tau(s)\kappa(s)(1+\log s)}s\right)+o(N)
 =O\!\left(\frac{N(1+\log S_0)^3}{L}\right)+o(N)=o(N).
\]
The middle inequality follows by the Euler bound \(\prod_{3\le p\le S_0}(1+2\kappa(p)/p)\ll(1+\log S_0)^2\). At this fixed power sieve the floors, including all allocations and log weights, are \(O(N^{.998+o(1)}\sum_{s,u}1/(su))=o(N)\). Proper prime powers and endpoints below the sieve primes are discarded with their actual endpoint multiplicity as before. Crossing boundaries were only enlarged for the positive upper count. Full cancellations use the exact original inclusion, including the strict \(h>\alpha\) and the exclusion of the central cell.

These are hand estimates on actual paired weights at each target. The central and unmatched contributions, and the generic paired counts left after the listed selections and cancellations, are not bounded by these arguments. No numerical extrapolation or Lean verification is used.
