# The high-rough Type II second moment reduces to coprime separated endpoints

2026-11-24. Research Commons / Dot. Scoped hand proof. No Lean verification, no numerical or global Goldbach claim.

Take only the [original strict high-rough stress strip](2026-11-24-high-rough-endpoint-sign.md) with the original square-root box and masks, at N=2^k. Put H=√N, L=log N and P=N^(1/10). Let g(q,h) be the exact grouped weight at a fixed q<h, summing every admitted ell,w,u; set it to zero for ineligible pairs. This is one representative in the odd-product paired row; a fixed outer factor 2 can be reapplied after estimating the row. All box intervals lie in (H/2,H]. Write n_i=N−qh_i.

The [exact weight audit](2026-11-24-mark-cutoff-exact-weight-audit.md) gives |g(q,h)|≪L: W_N=1, F is bounded, the log ratio of h and q is bounded, log(w)/log(d)≤1, and there are uniformly finitely many allocations. Indeed n is squarefree and every prime factor exceeds P, so it has fewer than ten prime factors. This uniform weight bound makes no assumption about signs.

## Two absolute power savings in the exact second moment

For 0<|h_2−h_1|≤T≤H, the contribution to the sum of |g(q,h_1)g(q,h_2)| from gcd(n_1,n_2)>1 is

    O(L² H² T/P).

To see this, sum over any common prime p, allowing overcounting. Such a prime exceeds P. Since qh_1 is coprime to N and p|N−qh_1, p cannot divide q: otherwise p divides N and qh_1. Modulo p the condition on h_1 is h_1≡N q⁻¹, and p divides the nonzero gap h_2−h_1, so p≤T. For each of O(H) choices of q there are at most 1+H/p≤2H/p choices of h_1 and at most 2T/p choices of the signed nonzero gap. Dropping all remaining eligibility conditions gives the bound after summing 1/p²≪1/P over p>P. The argument actually needs only the original coprimality mask, not the power-of-two shape.

The diagonal costs O(L²H²). All pairs with nonzero gap at most T independently cost O(L²H²T), without a gcd restriction, just by counting possible gaps. At T=H/L^B for any fixed B>2, this is o(H³). The common-prime estimate with T=H is O(L²H³/P)=o(H³) on the full gap range. The conclusions use the actual opened endpoint weights, not a progression model or an all-target average.

## Remaining estimate

For example, choose B=4. A **signed upper bound** o(H³) for

    ∑_q ∑_(h_1,h_2 : |h_1−h_2|>H/L⁴, gcd(N−qh_1,N−qh_2)=1)
          g(q,h_1) g(q,h_2)

uniformly at sufficiently large stress targets would now suffice for o(N) on the strict high-rough strip. Indeed expansion of ∑_q |∑_h g(q,h)|² gives this signed sum plus the two absolutely small pieces, and Cauchy–Schwarz costs only O(H) in the square of the total. Thus no asymptotic for common-mark pairs, for pairs sharing an unmarked endpoint prime, or for near pairs is needed on this row. The two disjoint rough factorizations at fixed q still carry the original Möbius signs and the fixed-target constraint. Their estimate is open; the argument gives no numerical saving for that surviving sector.
