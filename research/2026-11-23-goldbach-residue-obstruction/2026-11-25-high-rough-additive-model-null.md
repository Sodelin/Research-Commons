# Low-complexity additive product models contribute negligibly to the signed Goldbach row

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction using Davenport's Möbius estimate. No estimate for the whole endpoint sequence, no Lean check, and no Goldbach conclusion.

Use the exact ordered strict high-rough row in the [double exchange note](2026-11-25-high-rough-double-factor-exchange.md), with I=(H/2,H], H=sqrt(N). Denote its symmetric product weight by C_N(m), leaving the restriction to odd squarefree m with μ(m)=−1 outside it. Define the linear operation on product profiles P by
```
S_H(P) = ∑_{q,h in I; qh odd squarefree; μ(qh)=-1}
                 μ(h) log(h/q) P(qh).
```
The actual row is S_H(C_N). Do not insist that a model P itself be supported on rough endpoints; those tests are part of C_N and must stay in the residual C_N−P. Any fixed outer multiplier in the original decomposition can be restored separately.

**Claim.** For a finite representation P(m)=∑_j b_j(m)e(α_j m), with real frequencies and complex functions b_j on the product interval [H²/4,H²],
```
 |S_H(P)| ≪_A H² / (log H)^A · ∑_j (||b_j||∞ + Var(b_j)).
```
Here Var is ordinary total variation (discrete variation is sufficient), e(t)=exp(2πit), and the constant is independent of the frequencies, of the target, and of the number of terms. In particular arbitrary bounded (or polylogarithmically bounded) product models periodic modulo any polylogarithmic modulus, optionally multiplied by bounded-variation profiles of polylogarithmic norm, have an arbitrary logarithmic saving in this exact signed row. This is additive frequency in m=qh, not the existing [log-divisor frequency](2026-11-25-high-rough-balanced-divisor-frequencies.md).

## Remove the parity projector without losing its effect

On odd squarefree qh, μ(qh)=μ(q)μ(h), so inserting the −1 projector changes μ(h) to (μ(h)−μ(q))/2. In the complete ordered common box with a product-only coefficient, the μ(q) term is the negative of the μ(h) term by transposition and oddness of log(h/q). Thus
```
S_H(P) = ∑_{q in I, q odd squarefree}
         ∑_{h in I, (h,2q)=1} μ(h) log(h/q) P(qh).
```
Squarefreeness of h is now internal to μ(h). Dropping the parity projector by fiat in the first formula, or treating μ(h) as independent of the selected parity at fixed q, does not give this result; the transposition is essential. If an added mask breaks this symmetry, the theorem does not automatically apply.

## Davenport with a fixed-q coprimality test

[Davenport's uniform logarithmic saving](https://academic.oup.com/qjmath/article-abstract/os-8/1/313/1564796) gives |∑_{n≤x} μ(n)e(αn)|≪_A x/(log x)^A for all real α and x≥2. Use the elementary pointwise convolution
```
μ(h) 1_{(h,2q)=1} = ∑_{d|h; every prime dividing d divides 2q} μ(h/d).
```
For h divisible by a prime dividing 2q the local factor is 1−1=0; away from these primes it reduces to μ. For any H/2≤t≤H take the exponential prefix through t. For d≤√H apply Davenport at t/d, whose log is comparable to log H for sufficiently large H, and sum 1/d at most f(2q)=2q/φ(2q). For the rest use the absolute count H/d and Rankin:
```
∑_{d>√H; p|d implies p|2q} d^(-1)
  ≤ H^(-1/4) ∏_{p|2q} (1−p^(-1/2))^(-1) ≪ H^(-1/8).
```
The last product is O_ε(H^ε) uniformly for 2q≤2H: split off finitely many small primes and bound each remaining factor by p^ε. Taking ε=1/8 proves the displayed bound. Consequently each restricted exponential prefix is O_A(H f(2q)/(log H)^A), uniformly in its frequency. This also bounds subinterval prefixes by subtraction.

At fixed q use frequency α_j q. Abel summation against log(h/q)b_j(qh) costs at most O(||b_j||∞+Var(b_j)), since log(h/q) is uniformly bounded on the common box and has bounded variation. Sum q using ∑_{q≤H} f(2q)≪H, which follows from the convergent divisor mean of q/φ(q) or the earlier row-envelope moment bound. This proves the claim. A period R profile with supnorm M has additive Fourier coefficient sum at most √R M by finite Parseval, giving the stated periodic consequence.

## Remaining arithmetic

For any such model with polylogarithmic total variation budget, S_H(C_N)=S_H(C_N−P)+O_A(N/log^A N). A productive approximation would have to show the residual small in the **signed row**, or give an absolute approximation in the actual box-placement mass; no such approximation is proved here. In particular the joint endpoint divisor geometry cannot be discarded merely because a progression model for it cancels. The result separates a progression-model contribution from the genuine fixed-target remainder, and it does not supply the required covariance bound.