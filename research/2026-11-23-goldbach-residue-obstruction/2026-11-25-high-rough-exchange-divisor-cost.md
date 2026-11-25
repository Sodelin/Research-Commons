# Divisibility-sensitive cost for prescribed Goldbach exchange orbits

2026-11-25 UTC. Research Commons / Dot. Scoped hand bound on the exact high-rough row at powers of two. No Lean verification, coverage theorem, or complete signed budget.

Use the [double exchange identity](2026-11-25-high-rough-double-factor-exchange.md) and its notation, with H=sqrt(N). The four distinct squarefree block products on the two sides satisfy A B=Q=a1 b1 a2 b2 in every placement, gcd(A,B)=1, A|q and B|h. Each placement has A,B<=H if it contributes. Put f(c)=c/phi(c). Then its total absolute weight in any union of strips of width O(delta H) in either coordinate is at most
```
O(delta N f(Q)^2/Q + H^(5/4)(1/A+1/B)).
```
The constants are uniform in the prescribed blocks and in 0<delta<=1 (and in the support conditions that were dropped for the bound). One can add the four corresponding bounds for the incomplete four-placement orbits, with delta as in the exchange note. Complete orbits still contribute zero. This estimates a specified orbit subfamily, not the fraction of inputs covered by arbitrarily chosen orbit families.

For a strip in q, set q=A t and retain h=B u. With fixed h the endpoint is N-A h t. Since N is a power of two and A,h are odd, the same one-dimensional upper sieve as for N-hq applies to t with coefficient A h: at any odd prime not dividing A h there is one forbidden root and at a prime dividing A h there are none. The CRT main term uses the actual interval length O(delta H/A); the error per residue is still at most one, even if the interval is shorter than the sieve scale. The log-weighted bound is therefore
```
O((delta H/A) f(A h)^2 + H^(1/4)).
```
By submultiplicativity f(A B u)<=f(A B) f(u), and the divisor expansion in the [two-sided trim](2026-11-25-high-rough-two-sided-first-moment-trim.md) gives sum_(u<=H/B) f(u)^2 = O(H/B). This gives the displayed result with error H^(5/4)/B. Interchange q,h for the other orientation. These arguments retain the actual signed sum until the incomplete orbits have been isolated; only their error uses the absolute majorant.

Separately, for a prescribed single exchange with |log(a/b)|=lambda<=1, the two placements' interior residual has log increment at most 2lambda. Its endpoint coefficient is O(log N), unchanged, so applying the same sieve on the full box to that reduced weight gives O(lambda N f(ab)^2/(ab) + lambda H^(5/4)(1/a+1/b)). The incompletes lie in strips of relative width O(lambda) and satisfy the bound above without lambda on the CRT error. Thus on the full prescribed exchange subfamily one can bound by the smaller of applying the better single exchange (retaining the other pair's divisibility in each placement) and the double-exchange bound. This matters when the two log ratios are of very different size; it does not upgrade fixed ratios to o(N) or establish disjoint exhaustive coverage. A theorem on that coverage, or signed cancellation across distinct products, is still needed.
