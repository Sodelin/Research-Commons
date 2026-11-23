# Large square divisors in centered cofactor cells

**Scope.** Elementary hand bound for the cofactor-cell split in [the continuation note](README.md), in the setting of the [corrected Huang–Li moving cutoff](https://zenodo.org/records/21939906). This is not a prime-pair supply estimate, a novelty claim, or a Lean verification.

Fix an even target N and write k = floor((N−n)/q) ≥ 1. Fix an integer Z ≥ 2, and retain cells whose k is divisible by d² for at least one integer d ≥ Z. The divisor d need not be prime. Keep any original cutoff restrictions, and let 1 ≤ q ≤ Q ≤ N. Assume, as in the continuation note, each summand before the model's factor 1/φ(q) has absolute weight at most (log N)² and outside row coefficients have magnitude at most 1.

1. The actual progression n ≡ N (mod q) has at most one point per cell. At that point N−n = qk; thus μ(N−n) = 0 in every retained cell. There is no actual contribution.
2. The centered model is not necessarily zero. A model integer in that cell satisfies qk ≤ N−n < q(k+1), not necessarily d² | N−n. There are at most q model integers per cell, so each retained cell costs at most q(log N)²/φ(q).
3. For Y = floor(N/q), the number of retained cells is at most sum over d ≥ Z of floor(Y/d²), at most Y/(Z−1), by the integral bound on the decreasing tail. This bound needs neither prime distribution nor cancellation and stays true after any further cutoff.
4. The total absolute model error is at most N(log N)²/(Z−1) times sum over q ≤ Q of 1/φ(q). For an elementary bound, q/φ(q) ≤ 2^ω(q) ≤ τ(q), and sum over q ≤ Q of τ(q)/q ≤ (1+log Q)² by writing q=ab. Hence the displayed slice costs O(N(log N)^4/(Z−1)), uniformly in N and independently of the signs of the row coefficients.

**What it buys.** A polylogarithmic threshold Z = ceil((log N)^B), with fixed B chosen large, gives any prescribed logarithmic saving on the slice. There is a separate check needed for the model even when the actual progression is identically zero. The bound does not cover all small-square cofactors: Z fixed gives no saving at the scale needed. It also says nothing about squarefree composite cofactors, which are not an error term merely because they are composite.

**Check.** Direct exact-integer enumeration verified the cell-count inequality count·(Z−1) ≤ floor(N/q) for 60,500 triples: 12 ≤ N ≤ 400, 1 ≤ q ≤ ceil(sqrt(N)), 2 ≤ Z ≤ 12. That check is finite; the uniform estimate is the elementary proof above.
