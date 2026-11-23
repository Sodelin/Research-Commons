# Near-equal factors: an absolutely removable semiprime slice

This extends the [centered cell bookkeeping](square-divisor-cells.md) to a slice where the actual side need not vanish. Elementary hand argument, not Lean verification, not a Goldbach proof.

Let d ≤ Q ≤ N be the modulus and k = floor((N−n)/d) ≥ 1 the cofactor cell. Keep the original cutoffs and all other restrictions. Fix 0 < η < 1/2. Retain those k = pr with distinct primes p < r and r−p ≤ k^(1/2−η). If Y = floor(N/d), all such k ≤ Y can be counted by allowing arbitrary integer factors: p ≤ sqrt(Y), and for each p there are at most floor(Y^(1/2−η)) positive differences r−p. Thus there are at most Y^(1−η) retained cells. Overcounting by factor pairs is harmless.

Each retained cell has at most one actual n in the required congruence and at most d centered model integers. As in the previous cell bounds, with weights at most (log N)² before the model's 1/φ(d) and outer coefficients bounded by 1, the combined absolute cost is at most

$
(log N)^2sum_{dle Q}(N/d)^{1-eta}(1+d/arphi(d)).
$$

Using d/φ(d) ≤ τ(d), write d = ab in the divisor sum. The inner sum of b^(η−1) for b ≤ Q/a is at most (Q/a)^η/η by integration; the outer sum is then bounded by Q^η(1+log Q)/η. The combined cell cost is O_η(N^(1−η)Q^η(log N)^3). In particular Q ≤ sqrt(N)(log N)^K gives O_η(N^(1−η/2)(log N)^(3+Kη)) for fixed K. This is a power saving on the specified slice, not a signed estimate for the remaining semiprimes.

The actual side here can be nonzero: take N = 112, d = 3, p = 5, r = 7, k = 35, n = 7, and η = 1/8. Then N−n = 105 is squarefree and Λ(7) > 0; the strict moving cutoff n < N−αd admits this example when α < 35. The point of the estimate is that this class is sparse, not that those actual terms vanish. It does not control all balanced factors, for example r−p comparable to p, or the regime with one small and one large factor.

Integer check for η = 1/8: enumerate all factor pairs 2 ≤ p < r with pr ≤ 40,000 and (r−p)^8 ≤ (pr)^3. The resulting cumulative number of pairs is at most floor(sqrt(Y)) floor(Y^(3/8)) for each integer 1 ≤ Y ≤ 40,000. At Y = 40,000 there are 5,950 pairs, counting composite factors too. This test is finite; the displayed proof gives the uniform estimate.
