# Binary Goldbach: argument catalog and first improvements

**Status:** Research notebook. Elementary lemmas below are hand-checked; the replay is finite; no original Goldbach solution, Lean check, priority claim, or VibeMath submission.

## 1. Weighted sieve: enough candidates minus composite partners

**Basic argument.** Chen's theorem guarantees a prime plus a residual with one or two prime factors. For this candidate set, if C is its size and L is its sum of Liouville signs (−1 for primes, +1 for two-factor composites), the count of genuine first primes is (C−L)/2. [Li–Liu's asymmetric sieve](https://arxiv.org/html/2606.05224v2) restricts the smaller factor. See the [earlier source audit](../near-miss-audit/SIEVE-BOUNDARY.md) for its fixed cutoffs.

**Small improvement: an exact audit class.** Set the factor exponent to b=(log 5)/log N. Since q<N, the smaller factor r in N=p+rq satisfies r<5, so r=1,2,3. For N≡192 mod 210 we have N≡0 mod 6, N≡2 mod 5, and N≡3 mod 7. If r is 2 or 3, then r divides the prime p, so p=r and q=N/r−1. For r=2 this q is a multiple of 5 and exceeds 5; for r=3 it is a multiple of 7 and exceeds 7. Both contradict primality. Every such representation on this progression would therefore certify Goldbach. More generally, to eliminate a fixed finite set of possible small factors, require N divisible by each r and choose distinct auxiliary primes s_r outside the set with N≡r mod s_r. The Chinese remainder theorem gives infinitely many N satisfying all the requirements, and the same argument works beyond a fixed threshold. This is a reduction, not a guarantee that any candidate exists. The replay checks 952 members of the example class.

**Next test.** Can a parity-sensitive lower bound guarantee a candidate for the moving exponent on this one progression? [Huang–Li](https://arxiv.org/abs/2005.03811) give a conditional route involving an extra Möbius-twisted distribution input; do not assume that input, or its uniformity in N, follows from Dirichlet GRH.

## 2. Exceptions: sparsity does not force clustering

**Basic argument.** If an exception necessarily forced many more nearby, an upper bound on the total number might rule out even one. A basic obstruction is that the proposed clustering law must use information specific to real primes.

**Small improvement: a planted isolated hole.** For N divisible by 4, take the odd integers in [1,N−1], split into independent blocks {x,N−x}, and select x alone with probability d, N−x alone with probability d, neither otherwise. Take d=1/log N. The midpoint is even. The set never represents N, but for all sufficiently large N divisible by 4, some realization represents every other even t in [N/2,3N/2] and has small discrepancies as below.

For a fixed t≠N in the interval, there are at least N/8−1 unordered distinct candidates {x,t−x} of odd integers in the carrier. As edges on the reflection blocks these candidates have no loops and maximum degree two (parallel edges are allowed); each endpoint within a block has at most one t-partner. Greedy matching takes at least a third, and on that matching the events that both elements are selected are independent with probability d². Thus missing this t has probability at most exp(−d²(N/24−1)). The union bound over at most N targets tends to zero.

For an interval and a remainder class containing m eligible odds, the count is a sum of independent block contributions in [0,2], with variance at most 2dm. Bernstein's inequality and a union bound over fewer than N^4 interval/class queries for moduli up to N give simultaneous discrepancy O(sqrt(dm log N)+log N). This can hold together with the coverage property since both failure probabilities tend to zero. Likewise at each Fourier frequency the real and imaginary centered block sums have total variance O(dN) and bounded increments; test a uniform N^3 mesh and use the O(N²) derivative bound to pass to all frequencies. The same square-root-scale estimate holds uniformly in frequency with m replaced by N. This is not a model of all actual prime properties or a logical claim about what follows from GRH. For prior related random-sumset tools see [Lazarev–Miller–O'Bryant](https://arxiv.org/abs/1109.4700) and [Zhao](https://arxiv.org/abs/0911.2292).

**Second diagnostic: preserve exact small-wheel histograms too.** A separate fixture groups consecutive reflection pairs within opposite reduced classes mod 30, chooses a block with probability 2/10, and chooses an orientation uniformly when active. The paired model takes both endpoints of the same reflection pair; the avoiding model takes one endpoint from each of the two reflection pairs, in opposite residue classes. Both have marginal density 1/10 and exact matching whole-range histograms mod every divisor of 30. Independence across blocks and Bernstein give the same interval/class discrepancy estimate as above with that density. This is a second construction, not a claim that the isolated-hole fixture has the exact histogram property. The replay checks 460,800 prefix inequalities for moduli 1–80 and separately exhibits just one missing central even sum in the independent reflection model.

## 3. Circle method: use phase or localize the target

**Basic argument.** The minor-arc coefficient for one target is signed. The global fourth moment of the smoothed prime sum controls the sum of squared errors over all targets, not the sign or size of any particular error. [Huixi Li and Zhixin Liu](https://arxiv.org/html/2610.26756v1) cite Goldston's older full-Dirichlet-GRH bound, O(sqrt(N) log³ N) exceptions; their preprint obtains O(sqrt(N) log^100 N) under weaker zero-location assumptions and extends the analysis to prime differences. Granting the newer proof's hypotheses does not turn either upper bound into zero.

**Small improvement: a check on the scalar optimization.** In Lemma 10.1 of that preprint take eight equal lengths a_i=1/8, u_i=x_i=1/16, and r=D=1/2, e=3/2. For a subset with a-sum A, the first subset inequality is 1/2+A≤A+max(A,1/2), and the second has a right-hand branch equal to 3/2. All eight individual fourth-moment constraints hold at equality; H=2. This remains a feasible equality pattern even if a stronger amplitude input imposes D≥1/2. In particular a strict gain cannot follow from only those scalar inequalities at that tightened boundary. This is not a witness for actual prime sums and not a failure in Li–Liu's proof; the paper treats its equality patterns separately.

**Next test.** Ask what one exceptionally negative Fourier coefficient would force about the phase across arc blocks, not just about the total fourth moment. A sufficiently strong one-sided, target-specific bound would be useful even without a full prime-pair asymptotic. None is proved here.

## Replay

Run `python3 -B replay.py | diff -u REPLAY.txt -`. The finite checks support the constructions but do not replace the general arguments.
