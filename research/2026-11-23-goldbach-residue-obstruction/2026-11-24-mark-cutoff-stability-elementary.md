# Goldbach mark-cutoff stability from elementary rectangle counts

2026-11-24, Research Commons / Dot. Scoped hand bound on an unweighted majorant, and conditional application to the signed ledger indicated below. No new Lean verification. This removes the need for the proposed Kloosterman-completion error in the [earlier cutoff candidate](../2026-11-24-vp-vnp-boolean-boundary/FIVE-LANE-INTERFACES-AND-OBSTRUCTIONS.md).

Let N be a power of two, L=log N, and 0<=W=o(L). Sum over primes N^(1/10)<ell<=N^(1/8) and odd primes w with |log(ell w)-(13/40)L|<=W; require ell≠w (squarefree marks). For each such mark count pairs 1<=q,h<=C sqrt(N) with r=(N-qh)/(ell w) a positive integer free of odd prime divisors below N^(27/160). Give every counted allocation a nonnegative weight at most C' log ell. The total is
```
O_C,C'( N(1+W)/L + N^(33/40+4 kappa+o(1)) )
```
for any sufficiently small fixed kappa>0 (for example 1/100), with a constant allowed to depend on kappa. In particular it is o(N).

**Rectangle count.** Fix M=ell w and let z=N^kappa. If d is composed of odd primes at most z, the condition d|r implies qh≡N mod Md. Continue to count that congruence even outside the region qh<N, which is legitimate when upper-bounding a nonnegative Selberg square by extending it to the whole box instead of applying it with signed coefficients to a truncated congruence count. For K=Md odd, N is a unit. Exactly phi(K) residue pairs solve qh≡N modulo K; each component count in the interval [1,C sqrt N] is length/K+O(1). Summing the product gives
```
A(K) = (C sqrt N)^2 phi(K)/K² + O_C(sqrt N+K).
```
Since d is coprime to M, the proportion relative to the M-main term is the multiplicative g(d)=phi(d)/d². All d in the expansion have d<=z². Here K<=N^(13/40+2 kappa+o(1))=o(sqrt N).

**Sieve.** Apply the usual upper-bound Selberg square with coefficients supported on odd squarefree d<=z, lambda_1=1, to the small-prime factors of r. The optimized main quadratic form is 1/G(z), where G(z)=sum_{d<=z, d odd and squarefree} prod_{p|d} g(p)/(1-g(p)). For odd p, p g(p)/(1-g(p))=1-1/(p²-p+1). The product is bounded below absolutely, so G(z)≫log z by the positive density of odd squarefree integers and partial summation. In the standard minimizing formula the magnitude of lambda_d is at most prod_{p|d}(1-g(p))^(-1)<=d (the partial sieve sum in the numerator is at most G(z)); thus the absolute sum of coefficients is O(z²). Expanding the square and using the rectangle error costs O_C(sqrt N z^4) per mark. Consequently the count per mark is O_C(N/(M L)+sqrt N z^4), with kappa fixed.

**Sum over marks.** For each ell, the w range is a multiplicative interval of logarithmic length 2W, with w=N^(1/5+o(1)) or larger. Divide into bounded-ratio intervals; the elementary Chebyshev prime-count bound gives sum 1/w=O((1+W)/L). Also sum_{ell<=N^(1/8)} (log ell)/ell=O(L). This yields the claimed main bound. The number of marks is at most N^(13/40+o(1)) by summing the trivial floor bound on w over ell; multiplying by O(L) and the per-mark error gives the displayed exponent 33/40+4 kappa+o(1).

**Application boundary.** If the original ledger's only change is adding or deleting these squarefree marks, and its absolute opened weight is O(log ell) per allocation up to bounded multiplicity, the result applies by majorization even with additional arithmetic and parity filters. The negative-part functional is 1-Lipschitz, so changing grouped signed sums changes their total negative mass by at most the absolute added/deleted weight. The exponent proof does not independently recover those ledger weights or bound the signed sum away from the cutoff. If original masks allow repeated marks, nonunit target classes, or unbounded multiplicity, those need a separate check. This bound does not solve Goldbach or the remaining signed fixed-target inequality.
