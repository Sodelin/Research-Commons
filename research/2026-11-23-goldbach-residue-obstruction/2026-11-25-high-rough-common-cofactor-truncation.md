# A finite common-cofactor truncation for the high-rough Goldbach moment

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof on the strict signed Type II strip at powers of two. No Lean verification, signed bulk estimate, or Goldbach conclusion.

Use the exact g(q,h), H=sqrt(N) and original square-root box of the [coprime-endpoint note](2026-11-24-high-rough-coprime-off-diagonal.md). In particular g is supported on squarefree odd qh, its endpoint N−qh has no prime factor at most N^(1/10), and |g|≪log N. The diagonal may already be removed. Unlike deleting pairs of endpoints with a shared prime, deleting pairs of *cofactors* with a shared prime requires dealing with primes much smaller than N^(1/10).

## Uniform large-common-prime deletion

For every Z≥5, the absolute mass of nonzero-gap pairs with some p>Z dividing both h and h+j is

    ≪ H³/Z + H^(5/2)(log H)².

Use j>0, with reversal changing only a constant. Put R=H^(1/10); take H large enough that R≥5. For p>H^(1/2), counting p|j and p|h directly costs O(H³(log H)² sum_(p>H^(1/2)) p^(-2))=O(H^(5/2)(log H)²). There are at most H/p positive multiples of p up to H in the box for either j or h.

For Z<p≤H^(1/2) with p|j, write h=pm and apply the two-form sieve at cutoff R on an interval in m of length at most H/p. Omit 2 and p. For every other prime t, multiplication by p permutes residues, and the forbidden-root counts are exactly those in the [sparse-gap proof](2026-11-24-high-rough-sparse-gap-removal.md): zero for t|q, one for t|j but t∤q, two otherwise. Omitting one p≥5 costs a uniformly bounded factor in the Euler product. The same proof gives, after the two log weights, the upper bound

    O((H/p) f(q)² f(j)² + H^(1/4)),   f(m)=m/phi(m).

The error is still uniform in p: each squarefree modulus excluding p gives the same number of root classes in m and the same CRT error per class. If p|q the original weight is already zero; no new term is introduced by allowing this case in the majorant. For each p, use f(pt)≤f(p)f(t) and the bounded second mean of f from the sparse-gap proof. Then sum_(j≤H,p|j) f(j)²≪H/p, and sum_(q≤H) f(q)²≪H. The main terms sum to O(H³ sum_(p>Z)p^(-2))=O(H³/Z). The errors sum to O(H^(9/4) log H), using sum_(p≤H^(1/2))1/p≤1+log H. Combining gives the precise bound

    O(H³/Z + H^(5/2)(log H)²),

with a constant independent of Z. No assumption about the correlation of the signs enters.

## A finite set of coprime residual tests is sufficient at each cutoff

First use the [fixed-least-prime norm split](2026-11-25-high-rough-fixed-least-prime-test.md). For fixed Z only classes r≤Z need be tested, with norm tail O(H^(3/2)/log Z)+o(H^(3/2)). Within each fixed class r do a **second**, independent truncation at a fixed prime threshold T≥r. The bound just proved applies unchanged to the masked absolute mass, so after dividing the squared norm by H³ its removed mass is O(1/T)+o(1). There is no factor counting r to absorb at this stage: hold r fixed as T tends to infinity, before using the first norm split.

On what remains, d=gcd(h1,h2) is an exact squarefree divisor of the product of primes at most T, contains r, and is coprime to q. Write h1=da and h2=db. Now gcd(a,b)=1 and gcd(ab,qd)=1, and both remaining cofactors have least prime greater than r (including the case 1 with the usual infinity convention). The original signs on h1,h2 become mu(a)mu(b) since mu(d)²=1. The two endpoints are N−qda, N−qdb at common modulus qd; their coprimality, original separation and every exact divisor and log weight remain in force.

For each fixed r, it suffices to bound the signed upper covariance by o(H³) for each fixed exact d of this form. At fixed T the retained list is finite, so take H→∞ first, then T→∞ to remove its O(1/T) remainder. Finally apply the fixed-least-prime norm split and send Z→∞. No growing-d uniformity is needed. This removes large shared cofactor primes, not the Möbius signs on the now coprime residual cofactors. Even d=r remains an open fixed-target correlation.
