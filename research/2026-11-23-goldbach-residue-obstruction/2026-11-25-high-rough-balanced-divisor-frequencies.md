# A polylogarithmic divisor-frequency reduction for the strict high-rough Goldbach row

2026-11-25 UTC. Research Commons / Dot. Scoped hand reduction at the original powers of two, using the previous rough-endpoint upper sieve. No Lean verification, signed estimate, or positivity result.

Keep the exact [double-exchange row](2026-11-25-high-rough-double-factor-exchange.md), with product coefficient C_N(m), odd squarefree m of Möbius sign -1, H=sqrt(N), and sharp box H/2<q,h<=H. Thus C_N(m) keeps all original product and endpoint allocation masks, is O(log N), and vanishes unless N-m has least prime greater than N^(1/10). Write G(N) for the signed ordered row, twice its restricted q<h counterpart; any external scalar in the original decomposition can be restored separately.

Put z=log(h/q), m=qh. The box forces N/4<m<=N and, except for the choice of strict endpoints, is exactly
```
 |z| <= a_m := min(log(N/m), log(4m/N)).
```
Indeed q= sqrt(m) exp(-z/2), h=sqrt(m) exp(z/2). In particular a_m<=log 2. For each product in this range define the odd function g_m(z)=z 1_(|z|<a_m); any boundary convention below gives the same error estimate.

## Smooth the sharp cutoff without changing the arithmetic weights

Let eta=1/log N, and convolve g_m with the even nonnegative unit-integral tent eta^(-1) max(0,1-|z|/eta). The resulting g_(m,eta) equals z whenever |z|<a_m-eta and equals zero when |z|>a_m+eta. Its difference from the sharp function is uniformly O(1) and occurs only at distance at most eta from the possible boundaries. This also holds when a_m<=eta. For every affected pair, one of q,h is within O(eta H) of H/2 or H, and the other lies in [H/3,2H] for sufficiently large N. To see this, use the displayed expressions for q,h and note that at |z|=a_m the relevant box edge is attained exactly.

The argument of the [sharp-edge bound](2026-11-25-high-rough-double-factor-exchange.md) estimates this union of strips with the outside band [H/3,2H] as well: for each fixed opposite variable, only the length of the interval for the sieved variable enters the CRT main term; the O(H^(1/4)) remainder is unchanged. Sum f(h)^2 with f(h)=h/phi(h) up to 2H. Thus smoothing changes the weighted row by O(eta N + H^(5/4)), including any thickened-box pairs not in the old box. The coefficient C_N(m) is used unchanged and the estimate is not applied to a signed proxy for it.

## Sum all factor allocations in each retained frequency exactly

Choose period L=4 log N for the kernel in z; all actual |z|<=log m<=log N, so there is no wrap, and the outside near-zero neighborhoods of the compact kernel make the periodic convolution agree. Write c_(m,j) for the periodic Fourier coefficient of g_(m,eta) at omega_j=2 pi j/L. Uniformly in m,
```
c_(m,0)=0,
|c_(m,j)| << (1/|j|) min(1,(L/(eta |j|))^2)  (j != 0).
```
The sharp kernel has uniformly bounded variation, giving the first factor by piecewise integration by parts. The tent is a convolution of two identical centered uniform densities on [-eta/2,eta/2], so its Fourier multiplier is the squared sinc and gives the second factor. Hence truncating at J=ceil((log N)^4) has uniform error O((L/(eta J))^2)=O(log^(-4) N). It may be applied to all ordered factor placements, not only the balanced ones: the total absolute divisor weight is O(log N sum_(m<=N) tau(m))=O(N log^2 N), using sum_(m<=N) tau(m)<=N sum_(d<=N) 1/d. Thus truncation costs O(N/log^2 N).

The remaining per-product sum is explicit. For squarefree m,
```
sum_(qh=m) mu(h) exp(i omega log(h/q))
   = product_(p|m) [exp(-i omega log p)-exp(i omega log p)]
   = product_(p|m) [-2i sin(omega log p)].
```
Each prime is assigned to either q or h; the latter choice introduces the minus sign. Combining the estimates gives the exact signed approximation
```
G(N) =
  sum_(N/4<m<=N, m odd squarefree, mu(m)=-1) C_N(m)
      sum_(0<|j|<=J) c_(m,j) product_(p|m) [-2i sin(omega_j log p)]
  + O(N/log N).
```
The spectrum has no zero mode. Opposite frequencies recombine to real weights. This replaces a sum over near-equal divisors by a polylogarithmic frequency grid whose per-product divisor factors are completely explicit. The coefficient still depends jointly on m and N through the original endpoint; the representation neither asserts independence across frequencies nor gives a sum bound by itself. The next test is whether a weighted mean of the sine products against the actual endpoint coefficient gains anything beyond the edge sieve. This is an alternate representation, not a claim to have covered exchange orbits or proved Goldbach.
