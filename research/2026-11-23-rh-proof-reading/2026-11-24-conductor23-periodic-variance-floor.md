# Fixed congruence centering leaves an exact nonabelian variance for conductor 23

2026-11-24. Research Commons / Dot. Classical Chebotarev input and scoped hand calculation. No new Lean verification, moving-modulus estimate, or arithmetic covariance bound.

We compare the fully split prime indicator for the splitting field K of x³−x−1 with an arbitrary fixed periodic prime predictor. This is a one-prime variance statement, not the [two-companion masked covariance](2026-11-24-conductor23-original-masks-prime-sector.md).

Let a(p) be the standard S₃ character, chi(p) the sign character (the quadratic character of Q(sqrt(−23))), and b(p) the indicator of complete splitting in K. At all unramified p the character table gives

```text
b(p) = (1 + chi(p))/6 + a(p)/3.
a(p)^2 = 1 + chi(p) + a(p).
```

Indeed, a is 2, 0, −1 on the identity, transpositions, and 3-cycles respectively. Fix any modulus Q; replace it by Q'=lcm(Q,23) for computing conditional means. The intersection of K with the cyclotomic field of conductor Q' is exactly the quadratic sign field: it contains that field, is abelian over Q, and S₃ has no larger abelian quotient. Hence at a fixed unit residue class modulo Q', the Frobenius restriction to K is distributed by element count over the matching sign coset, in the Chebotarev density sense. To see the normalization, the Galois group of the compositum is the fiber product over the sign quotient. Fixing the cyclotomic component leaves the three elements of one sign coset. If the sign is positive, these consist of one identity and two 3-cycles; if negative, every element is a transposition. See [Thorner–Zaman for the Chebotarev prime-count statement](https://msp.org/ant/2019/13-5/ant-v13-n5-p02-s.pdf). Partial summation gives the same distribution under prime weights log p normalized by X for p≤X.

In particular the conditional mean of a is zero on every progression, and its conditional second moment is 2 on the positive coset and 0 on the negative coset. The average second moment is 1. For any real predictor f depending only on p mod Q (or even p mod Q') this proves the exact limiting identity

```text
lim_(X→∞) (1/X) sum_(p≤X) log(p) (b(p)−f(p))²
= 1/9 + average_(r ∈ (Z/Q'Z)^*) ((1+chi(r))/6−f(r))².
```

The finite primes dividing Q' do not affect the limit. The squared error cannot tend to zero for a fixed periodic predictor even allowing the full quadratic sign information; the optimal predictor with that information is (1+chi)/6, with residual a/3 exactly. An analogous projection for a itself leaves squared error at least 1. No uniformity for Q growing with X is asserted.

**Interpretation.** This strengthens a zero-mean centering statement to a quantitative limit on that centering method: all of the variance in the nonabelian residual survives the best fixed periodic prediction. It does not imply that the residual has large signed covariance between different primes, nor bound the covariance after the companion, atom divisibility, distinctness, and separation masks. Do not substitute this marginal statement for a pair estimate.
