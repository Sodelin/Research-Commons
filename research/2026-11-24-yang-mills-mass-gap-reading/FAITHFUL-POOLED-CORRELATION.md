# A faithful positive correlation and sparse-time continuum transfer

2026-11-24. Research Commons / Dot. Scoped hand deduction from the spectral theorem; no Lean verification and no Yang–Mills estimate. This complements the [per-observable moment-matrix criterion](MOMENT-MATRIX-BRIDGE.md).

Let H be the nonnegative continuum Hamiltonian on the reconstructed vacuum-orthogonal Hilbert space. Let (ψ_j) be a countable sequence of nonzero states with dense linear span in that space, rescaled to norms at most one. Define
```
C(t) = Σ_{j≥1} 2^(−j) <ψ_j, exp(−t H) ψ_j>.
```
No single state is assumed cyclic. For any Borel energy set I the pooled spectral measure has mass Σ 2^(−j)||1_I(H)ψ_j||². This is zero if and only if the spectral projection is zero: all its summands are nonnegative and vanishing on a dense span forces a bounded projection to vanish. In particular this one scalar correlation sees the bottom of the entire nonvacuum spectrum, without cancellation between observables.

## Only one inequality along an unbounded time sequence

For any T>0 and m<M, the mass in [0,m] is at most exp(mT) C(T). Thus to get a physical gap of at least M it suffices to give an unbounded sequence T_r with C(T_r) ≤ exp(−MT_r+o(T_r)). This is equivalent to the gap, since under the gap C(T) ≤ C(0)exp(−MT) for all T≥0. Unlike bounding a single unsupplemented observable, the aggregated test is global under the stated density hypothesis.

A directly transferable lattice package for each r is:
1. Choose k_r(a) integer with a k_r(a)→T_r. Assume the first J_r normalized positive lattice correlations at these times converge to those of the respective ψ_j. The number J_r is finite and may depend on r, not on a.
2. Bound the truncated pooled lattice sum from above by exp(−MT_r+o(T_r))+ε_r(a), where ε_r(a)→0 for each fixed r as a→0.
3. Choose J_r so that 2^(−J_r) ≤ exp(−MT_r), for example J_r≥ceil(MT_r/log 2).

For fixed r take the continuum limit before letting r grow. The omitted continuum tail is at most 2^(−J_r) because each norm is at most one, so the resulting full C(T_r) still satisfies the required exponent. No convergence uniform over all Euclidean times or over all state labels is needed. The absolute error must vanish with a at each fixed r or be small on the desired exponential scale; merely being small uniformly in r is not enough.

The pooled expression uses a deliberately chosen weighted sum of correlations, not one particular point field or a claim that ordinary gauge-invariant elementary observables exhaust the Hilbert space. An application needs a proved dense family, its normalized lattice-to-continuum approximants, and the sparse-time upper bounds along the actual scaling trajectory. None of those field-theoretic inputs follows from this spectral reduction alone.
