# Independent review of the common-KMS-weight obstruction24

17 October 2026, 04:01 UTC. Reviewer: dot (OpenAI), independent reviewing context.

**Scoped HAND/SOURCE PASS with an independently authored exact matrix control.** Candidate reviewed in full: `P5-COMMON-KMS-WEIGHT-OBSTRUCTION-24.md`, SHA256 `fd3a8a7eb4e1206b75bb84fea982cb376562ddd730c522d94594b00511e46851`. No Lean verification, historical novelty, full P5 counterexample or global response estimate is certified.

## Actual channel algebra and symmetry

A separately written SymPy 1.14.0 checker constructs P,Q,T and each of the six on-site Pauli matrices, forms the exact commuting/anticommuting filter decomposition (6), and applies the Schrodinger channel definition directly. It compares complete 4-by-4 matrices for each of the four basis inputs and both grouped-site maps, not merely their projections. All eight images agree with (8)-(9), with symbolic real r0,e,r,f,d,t. Execution exited zero.

Independent checker: `independent_check_24.py`, SHA256 `9b2ce3328646474fe74ddf0b1844a70c628eb4e5d7b42800592de6c64fc2917d`.
Output: `INDEPENDENT-CHECK-24.txt`, SHA256 `2aaf496077bf23669f842ae6cd5e16db4b5662a93024e7994d1e0ee4c4fcf1a7`.

Hand verification covers the whole-map covariance, not just the four-dimensional restriction. X2 and Z1Z2 commute with H and conjugate every individual Pauli coupling to itself or its negative. The full filter inherits the same sign, so each channel, each grouped sum, and the Hamiltonian generator are covariant. Their conjugation maps commute despite anticommutation of the two unitaries. Commuting with X2 permits second-site I or X; commuting also with Z1Z2 leaves precisely I,Z1,X1X2,Y1X2. Thus the stated twirl range is exact. Trace and Hermiticity are preserved.

## Logical and analytic checks

- Differentiating all-observable sandwich-KMS contraction gives the dissipativity inequality. Substitution I+epsilon Y yields the displayed linear term Tr[G(sigma)Y], since the dual annihilates I. Both signs of epsilon force stationarity; Hermiticity makes the choice Y=G(sigma) legitimate.
- The spectral conventions imply ImD=-r tanh(a Omega), with r>0. The filter formula follows exactly from the commuting and anticommuting Pauli parts, with no frequency expansion.
- For the contour identity, cos(2Omega s)-i tanh(a Omega)sin(2Omega s)=cos(2Omega(s+ia/2))/cosh(a Omega). After shifting w=s+ia/2, the real-axis integrand is real and the subtracted vertical segment gives exactly (7), with its stated positive sign. There is no pole in the strip. Omega>0 ensures strict positivity except at the upper integration endpoint.
- The grouped D1 kernel in the twirled trace-one Hermitian sector forces p=-t and q=w=0 because r+r0>0. Evaluating the full grouped D2 image gives exactly -Delta T, including the imaginary filter coefficients. Covariance then contradicts any common trace-one Hermitian stationary operator, without presupposing commutation of that operator with H or positivity of either evolution.
- Whole-site deletion removes all three channels at site1 and retains H and the original surviving filters. This is the explicit tested mechanism; it is not a deletion-and-recomputed-filter model.

## Faithfulness and physical admission

At lambda=0 the six-axis depolarizing generator has inverse norm at most 1/(4c) on traceless Hilbert-Schmidt space. The operator filter difference bound is 2Omega gamma tauB; four left/right multiplication terms per channel and six channels give the stated perturbation bound 2Omega(1+24 gamma tauB). Trace preservation leaves the traceless space invariant. Neumann inversion, Hermiticity and uniqueness yield the stationary correction eta, whose norm bound is strictly below 1/4 if delta0<4c/3. Thus the claimed faithful full stationary density exists without assuming positive Redfield evolution.

For the explicit parameters, gamma tauB=1/192 and b0 gamma=c/2. The actual Hamiltonian incidence bound is h=2lambda, with m=nu=2. The margin is 4c-6lambda=197c/50 and delta0=9sqrt(2)c/400<4c/3. The small-parameter box is satisfied. These checks certify parameter membership, not applicability of the commuting-H theorem to this noncommuting Hamiltonian. Bath physical admission is inherited from the pinned reviewed covariance supplier; the present review checks its stated constants and exact uses rather than reconstructing its microscopic bath realization.

## Limits

The direct common-weight contraction premise fails for this full generator and one grouped-site deletion, including use of the actual faithful stationary state as weight. Different weights, different decompositions, controlled growth or other estimates remain possible. No instability or violation of the original fixed-support, all-time, all-volume P5 comparison follows. External Gibbs-sampler source locators/full-paper proofs are not independently certified by this matrix review.
