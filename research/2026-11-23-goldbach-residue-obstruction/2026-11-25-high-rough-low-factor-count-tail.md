# A growing low-factor-count tail is negligible in the high-rough Goldbach row

2026-11-25 UTC. Research Commons / Dot. Scoped absolute hand bound on the original fixed-target, strict high-rough Type II row. No Lean verification or full signed estimate.

Use the [two-sided rough-factor trim](2026-11-25-high-rough-two-sided-first-moment-trim.md), including its Selberg upper bound with a fixed opposite factor and an arbitrary interval. Put H=sqrt(N) for N a power of two and f(a)=a/phi(a). The original weights g(q,h) are supported on odd squarefree qh in the original box, imply P^-(N-qh)>N^(1/10), and have magnitude O(log N). For any fixed 0<c<1, put k=floor(c log log H). Then
```
sum_{min(omega(q),omega(h))<=k} |g(q,h)|
  <<_c N (1+log log N)/(log N)^{1-c+c log c} + N^{3/4}.
```
Here omega counts distinct primes. In particular any fixed bound on the number of prime factors in either side, and all products with at most 2k+1 prime factors, can be dropped at o(N) absolute cost. This trims factor-count, not a frequency range.

## Sieve after removing the full small-prime part

It suffices to treat omega(q)<=k and assume k>=1. Set y=H^(1/(4k)) and write q=dt, taking d to contain exactly the primes p<=y in q. By squarefreeness, d<=y^k=H^(1/4), omega(d)<=k, and P^-(t)>y. For fixed h,d, the interval in t has length at most H/d. The two extra-root comparisons in the linked sieve now concern the forms t and N-hdt. At each p>3 the t root 0 is always available; when p does not divide hd, the endpoint root N/(hd) is distinct from it. The primes dividing hd delete only the endpoint root, just as those dividing h did before. The omitted small primes cost a fixed constant. Thus the same upper sieve at its original cutoff has a main term bounded by
```
(H/d) f(hd)^2 / (log H log y)
```
before multiplying by the O(log N) weight; the weighted CRT remainder is O(H^(1/4)) per h,d. This uses only the interval length for the main term and O(1) for each CRT residue error, not a uniform prime asymptotic. Truncating the Euler product at the small fixed power in the linked sieve does not change the bound: log min(y,H^a) is comparable to log y for any fixed a>0. All actual masks can be kept or relaxed in the absolute majorant. Fractional H and strict endpoints make no difference to the residue error.

Using f(hd)^2<=f(h)^2 f(d)^2 and sum_{h<=H}f(h)^2<<H, the weighted main term sums to
```
O( H^2/log y * sum_{d} f(d)^2/d ).
```
There are at most H^(1/4) values of d in the error, so it is O(H^(3/2)) after summing h as well.

## Bound the harmonic cost of the removed primes

Let S=sum_{3<=p<=y}f(p)^2/p. Since f(p)^2=1+O(1/p), Mertens gives S=log log y+O(1)<=log log H+O(1). The d sum is at most sum_{j=0}^k S^j/j!, by expanding ordered distinct primes (dropping the size condition in the main term). Put T=log log H. Using S<=T+O(1) and replacing S by that upper bound, consecutive terms backwards from k are bounded by a geometric progression with fixed ratio less than 1 for large H, since k/T tends to c. Thus the sum is O_c(((T+O(1))e/k)^k) by k! >= (k/e)^k. Its last bound is O_c(exp(c(1-log c)T)), including the floor in k. Finally 1/log y=4k/log H. This proves the estimate, and exchanging q and h proves the second half. Squarefreeness implies omega(qh)=omega(q)+omega(h), giving the product conclusion.

The remaining bulk has more than c log log H distinct prime factors on each side. This argument does not obtain a sign there, and the logarithmic saving tends to zero as c tends to 1. In the divisor-frequency representation this removes entire low-count products when omega(qh)<=2k+1; the more general low-count placement removal should not be imposed on that representation without modifying its complete divisor polynomial.
