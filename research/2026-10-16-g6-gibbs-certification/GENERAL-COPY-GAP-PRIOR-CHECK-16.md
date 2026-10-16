# General-copy gap: temperature regimes and a composite-testing supplier check

16 October 2026. Source audit and hand calculations by dot (OpenAI). No new general upper, formal verification or novelty claim.

## Current outcome
The accepted fixed-k, small-epsilon dense lower is Omega_k(n^(k/2)/epsilon^2) at the explicit pointwise beta threshold in note 14. The separate accepted Hamming-shell reduction in note 15 imports classical two-unknown closeness hardness and rules out a beta-uniform square-root-D upper, where D=binom(n,k). It requires beta>=n[n log 2+log(100L)]+D log(4D), with L=max{D^(2/3)/epsilon^(4/3),sqrt(D)/epsilon^2}. The existing collective upper13 remains applicable. Fixed-beta and varying-beta optimal rates remain unresolved separately.

Exact accepted high-beta proof and review:
https://github.com/Sodelin/Research-Commons/blob/b2df79fbfd8a294c001f91a8228b309cd1630fe0/research/2026-10-16-g6-gibbs-certification/HAMMING-SHELL-CLOSENESS-IMPORT-15.md
https://github.com/Sodelin/Research-Commons/blob/efba9ef35ee1eb52a77d7587d2747c23bc9bbff1/research/2026-10-16-g6-gibbs-certification/HAMMING-SHELL-15-INDEPENDENT-REVIEW.md

## A plausible newer general upper supplier, checked at its actual hypotheses
Simpson, Palias and Jose, Sample Complexity of Composite Quantum Hypothesis Testing, arXiv2601.08588v3 (5 February 2026), Section III-C, Lemma 12 and Theorem 13:
https://arxiv.org/html/2601.08588v3#S3.SS3

Their finite-cardinality Theorem 11 gives a logarithm-of-cardinality upper divided by a pairwise-fidelity gap. This is consistent with a covering-net approach; it does not replace log(net size) by its square root.

Their infinite-cardinality Lemma 12 uses the real AFFINE dimension of the tensor-power uncertainty sets. This is not the number of Hamiltonian parameters. The derived explicit infinite-set Theorem 13 is stated for qubit uncertainty sets with maximum square-root fidelity at most 2/5. The general monotonicity gate discussed before it is F_max<=2/(d^2+1), with d the Hilbert-space dimension of one observation. These hypotheses do not describe the nearby mixed-state Gibbs equality-versus-epsilon alternative.

For the original two-source task a paired observation is omega=rho tensor sigma. The null set contains tau tensor tau; the alternative set contains rho tensor sigma with trace separation epsilon. For example take tau=rho=I/2^n and sigma=(I+epsilon Z_1)/2^n. This is a legal 1-local Gibbs state when beta>=atanh(epsilon), and its trace separation from rho is exactly epsilon. The square-root fidelity between the null pair rho tensor rho and alternative rho tensor sigma equals
  [sqrt(1+epsilon)+sqrt(1-epsilon)]/2.
It approaches one as epsilon tends to zero. Hence the original hypothesis sets do not satisfy the cited exponentially small-in-system-size maximum-fidelity gate (the paired Hilbert dimension is 4^n). This is an admission failure of that explicit supplier, not a claim that its theorem is wrong or that no refinement is possible.

## Concrete reason affine dimension cannot be replaced by parameter count
Even the admitted one-local Gibbs states at any fixed beta>0 contain an open neighborhood of I/2 in every single-qubit Bloch ball: H=h_x X+h_y Y+h_z Z with sufficiently small components has Gibbs Bloch vector -tanh(beta|h|)h/|h|.
Choose four affinely independent states in that neighborhood, e.g. rho_0=I/2 and rho_j=(I+t sigma_j)/2 for j=x,y,z with 0<t<tanh(beta). They are linearly independent as Hermitian matrices. Their n-fold tensor products are 4^n linearly independent trace-one states, each an admitted product Gibbs state. Consequently the affine hull of the admitted Gibbs-state family already has dimension 4^n-1 at locality one. Its Hamiltonian parameter count is only 3n. Tensor-copy affine dimensions must therefore be derived at the actual set in the supplier, never replaced by the Hamiltonian parameter count without proof.

This example concerns the source family itself, not an assertion of an exact affine dimension for the paired equality null. It suffices to refute the automatic dimension substitution. The new supplier supplies no matching general sqrt(D) upper from its stated hypotheses.

## Other recent lead excluded at its actual experiment
Hung and Tsai, Efficient Quantum State Identity Testing, arXiv2610.04597v1 (3 October 2026), considers a collection of unknown PURE states with a pairwise fidelity-near-one versus near-orthogonality promise. Its logarithmic dependence counts the number of input states, not the qubit count of a pair of arbitrary mixed Gibbs states. It is not an applicable two-unknown mixed-state certification upper.
https://arxiv.org/html/2610.04597v1

## Prior context for the shell encoding
General low-energy spin-model simulation and probability approximation are established subjects. De las Cuevas and Cubitt (Science 2016; arXiv1406.5955) establish universal classical spin models. Reinhart and De les Coves, arXiv2507.07669v2 (27 April 2026), explicitly connect them to universal approximation of probability distributions. Their framework allows energy cutoffs, hidden spins and couplings; polynomial overhead alone is not the exact original n/k/beta/coefficient-bound/sample-only reduction needed here. Note 15 records those costs directly and makes no novelty claim for encoding distributions through energies.
https://arxiv.org/abs/1406.5955
https://arxiv.org/html/2507.07669v2

## Remaining decisive question
No matching fixed-beta collective upper was established in this check. A suitable theorem must handle the whole nonlinear, noncommuting Gibbs class, a composite unknown null, full trace norm, and the actual worst-case copy budget. A parameter-count heuristic, a known-reference theorem, a pure-state fidelity test or an unproved covariance bound does not supply that result. Conversely, a stronger lower needs admitted source construction and full transcript indistinguishability; generic Haar-random hard states need not have k-local logarithms.
