# Continuance notes: two limitations and a removable slice

Hand arguments unless specifically identified as Lean-checked. Nothing here proves Goldbach or the twin-prime conjecture.

## Goldbach: what averaging the cutoff cannot do

[Huang–Li, (12)–(13)](https://arxiv.org/html/2005.03811v2) split the same count into short and long divisor sums S₁(α)+S₂(α); keep the [moving cutoff corrected by Moya](https://zenodo.org/records/21939906). If two cutoffs share the same short-side approximation to within E, then their exact long sums differ by at most 2E: the difference is exactly the negative of the short-side difference. [CutoffInvariant.lean](CutoffInvariant.lean) kernel-checks this inequality over integers, with the same elementary subtraction over reals. It does not certify the analytic estimate. Where the short-side estimate is uniform with E=o(N), averaging within that band cannot turn a genuine order-N long error into a smaller actual error merely by moving the cutoff. The earlier ramp remains a potentially easier *expression to bound*, not a new source of cancellation. This narrows the next search.

## Goldbach: a sparse cofactor slice can be removed

For squarefree moduli q≤N^(1−δ), δ>0 fixed, divide both the actual term and its centered model into cells k=⌊(N−n)/q⌋≥1. In the actual term q divides N−n and the cofactor equals k. Restrict to k all of whose prime factors are ≤y=exp(log N/(H loglog N)), H fixed. Each cell has at most one actual multiple and at most q model integers, each model term divided by φ(q). The absolute weight from Λ and the log is at most log²N per integer. Writing Y=N/q, the total for this q is therefore ≤log² N · Ψ(Y,y)(1+q/φ(q)), including any further original cutoff restrictions. Here Ψ counts positive y-smooth integers.

Rankin with s=1−1/log y gives Ψ(Y,y) ≤ Y·exp(−log Y/log y)·∏_{p≤y}(1−p^(−s))^(-1). Since p^(1/log y)≤e and s≥3/4 eventually, the log Euler product is at most e∑_{p≤y}1/p+O(1) by the convergent quadratic terms. With Mertens' reciprocal-prime estimate and Y≥N^δ, this gives Ψ(Y,y)≪Y(log N)^(e−Hδ). Summing (1/q+1/φ(q)) over q≤N costs O(log N). Choose H large enough to get any prescribed log saving on this explicit sparse slice, uniformly in N. The ordinary middle population, with more varied cofactor sizes and factors, remains uncontrolled.

## Twin primes: other gaps alone do not force gap two

A synthetic comparison, not a model claiming to reproduce all prime information: in a large dyadic block choose eligible integers coprime to a growing prime wheel. To a wheel unit n give marginal W/(φ(W)log n), otherwise zero. Use wheels as in [the earlier growing-wheel argument](../second-pass/README.md) with block beginning L and primes through floor(log L/16), so W≤L^(1/4) eventually and marginals are <1/2. Remove the first and last two positions of each block so a distance-two pair cannot cross a seam. Inside a block the eligible distance-two edges are disjoint: three consecutive odd candidates two apart include a multiple of 3. In each edge select at most one endpoint with the prescribed respective marginals, independently across these disjoint blocks; sample singleton eligible points independently.

No selected pair is two apart. For each fixed admissible set of offsets H containing no difference of two, all positions away from dyadic seams lie in different independent sampling groups. Their joint expectation is the product of the individual marginals. Periodic residue counting gives the usual finite product of local densities for H, tending to its Hardy–Littlewood factor as the wheel grows; the boundary error per dyadic block is at most a fixed power of log L times W, by periodic summation. The O_H(log X) seam positions do not affect the main term. Changing one independent sampling block affects at most 2|H| pattern occurrences. Bounded differences and a summable tail show the random count differs from its expectation by O_H(√(X log X)) eventually, simultaneously for every such fixed H by countable intersection. Thus even correct main terms for all the *other* fixed even gaps, together with ordinary fixed-remainder density, do not imply twin primes for an arbitrary synthetic sequence. The missing ingredient has to detect what is special about gap two or about actual primes.

## Reproduction

Compile CutoffInvariant.lean using `lean --trust=0 -o CutoffInvariant.olean CutoffInvariant.lean`. [Verification receipt](LEAN-REPLAY.txt).
