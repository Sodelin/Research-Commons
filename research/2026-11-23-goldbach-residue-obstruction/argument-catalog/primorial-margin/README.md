# The square-zero margin, uniformly in the target

Hand proof, not Lean checked. This improves the deterministic margin in the corrected Huang–Li comparison. It does not estimate the unknown diagonal prime–Möbius discrepancy or prove Goldbach. No priority claim.

Write L=log N for even N, w_p=1/[p(p−1)] for odd primes, B(N)=Σ_{p∤N,p>2} w_p, and A(N)=∏_{p∤N,p>2}(1−w_p). These are the local factors in [Huang–Li, §3.3–3.4](https://arxiv.org/html/2005.03811v2). All results below are pointwise in N, not target averages.

## 1. Sharp scale before the singular series

Let p_j be the first odd prime for which the product of odd primes through p_j exceeds N. The prime number theorem for θ gives p_j∼L. With costs c_p=log p the prime divisors of N have total cost ≤L. The ratios w_p/c_p strictly decrease with p. The fractional knapsack bound (shift cost from any larger prime to any unfilled smaller prime, or use the supporting line with slope w_{p_j}/c_{p_j}) bounds the removed weight Σ_{p|N,p>2} w_p by the weight of all odd primes through p_j. Thus B(N)≥Σ_{p>p_j} w_p∼1/(L log L), by partial summation of the PNT. Along N=∏_{p≤y} p the full weight through y is removed and L=θ(y)∼y, so B(N)∼1/(L log L). Since 1−exp(−B)≤1−A≤B, the same sharp asymptotic lower scale holds for 1−A. In particular it strengthens the single-prime lower bound of order L⁻² in Huang–Li §3.4.

## 2. Keep the singular series in the budget

Let S(N)=2C₂∏_{p|N,p>2}(p−1)/(p−2) in the paper's normalization. The uniform lower bound for S(N)(1−A(N)) is actually of order 1/L.

- If B(N)≥1/L, use 1−A(N)≫B(N) (B is bounded) and S(N)≥2C₂.
- Otherwise choose y=√L. For p≤y, 1/p≤y w_p. Hence Σ_{2<p≤y,p∤N}1/p≤yB(N)<1/√L. The product of the missing factors (p−1)/(p−2) through y is bounded because log((p−1)/(p−2))≪1/p. The product over *all* odd primes through y is ≍log y by Mertens' product (the ratio to ∏p/(p−1) is a convergent product). Thus S(N)≫log L. Multiply by the bound from §1.

On the primorial sequence S(N)∼e^γ log y by Mertens' product in the same normalization, and 1−A(N)∼1/(y log y); so the product is ∼e^γ/L. This shows sharpness in order, not the optimal uniform constant. Neither branch assumes sign cancellation for the prime–Möbius sequence.

## 3. Attach the margin to the exact analytic input

Huang–Li §3.3 bounds the squarefree weighted mass Σ_{n<N} Λ(n)μ²(N−n) by N A(N)+O_A(N/L^A) uniformly for any fixed A by the short square-divisor argument and ordinary prime distribution; also μ≤μ². Retain [Moya's correction](https://zenodo.org/records/21939906) n<N−αq. In the earlier [diagonal max-prefix comparison](../second-pass/README.md), choose the short-side log saving exponent, then K, sufficiently large: α=√N/L^K. The same short-side truncation and ordinary Bombieri–Vinogradov argument works with error O(N/L³) by increasing those fixed powers; the lower-end Euler-model truncation and proper prime-power errors are power-saving with logs. In detail, take the paper's square-divisor parameter B₀=L^(A+4) with A≥4, sum the large-B₀ tail as in (14)–(15), and then require αB₀² to lie inside the ordinary Bombieri–Vinogradov range with the required log savings as in (16). The long-side log weight costs O(L) by summation by parts and its varying endpoint remains in the max-prefix norm. Since S(N)≪L, the squarefree-mass error can be made o(N/L) as well.

Thus a sufficient extra pointwise input on **all** sufficiently large even N is Σ_{q≤√N L^K, squarefree, (q,N)=1}D_q(N)=o(N/L²), with D_q defined in the earlier comparison, using the actual reflected twist and maximal prefixes. The guaranteed model margin above then dominates the errors. This is weaker in log scale than spending a uniform N/L² margin, but stronger than the fixed-family o(N/L) premise, because the fixed-family model margin can be larger. In particular, the [mod-25/mod-49 argument](../exclusion-debate/README.md) remains sharper for 192 mod 210. [Cantarini's weighted averages](https://arxiv.org/abs/2607.09110) are not substituted for the pointwise premise. We do not establish that premise, an effective threshold, finite verification to a threshold, or a twin-prime statement.
