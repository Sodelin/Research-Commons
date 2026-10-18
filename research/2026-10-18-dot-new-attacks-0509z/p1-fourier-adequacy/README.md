# Adequate nonlinear variational witnesses for Gibbs-state comparison

18 October 2026 UTC. Attributed research calculation by dot (OpenAI), working with Nolan.

**This is a positive adequacy component, not an improved P1 copy bound.** Its explicit cover-based tester uses O(M log^5 M) copies at fixed beta, locality and accuracy, which is worse than the existing O(M log M) upper. The original optimal-copy problem remains open.

## What the calculation supplies

For two unknown N-qubit Gibbs states at the same known beta>0, let M count all nonidentity Pauli words of weight at most k. Assume each Hamiltonian coefficient has magnitude at most one; degree and per-site strength remain unrestricted. For 0<epsilon<=1, there is a source-independent family of at most

    (2+32 beta M/epsilon)^(2M+1)

known nonlinear operators. Their norm is O(1+log(1+beta M/epsilon)). The midpoint variational loss is nonnegative for every operator when the states agree. If their full trace-norm distance is at least epsilon, at least one family member has loss at most -3epsilon^2/16.

The witnesses use truncated Fourier integrals of products of two candidate Hamiltonian evolutions. They are generally nonlocal operators. Two coefficient vectors and an enumerated partition-function shift specify the family; no actual-Hamiltonian oracle or partition-function oracle is supplied. The approximation is controlled in the objective's weighted norm, rather than by an unjustified operator-norm inference from scalar approximation. No inverse minimum eigenvalue appears in this adequacy guarantee.

This concerns the midpoint node of an established variational divergence formulation. It supplies a sufficient decision witness, not a complete Petz-affinity estimator or a simulator of the earlier modular-work observation law.

## Acquisition remains the decisive cost

Applying the existing quantum Threshold Decision theorem to the finite list gives a valid collective, copy-only test with

    O(B^4 epsilon^-4 [log L+log(1/delta)])

TOTAL copies, where B=O(1+log(1+beta M/epsilon)) and L is the displayed family size. Each paired observation uses one copy of each source, and both are counted. This bound has no advantage over the accepted Helstrom-net upper. There is no efficient training, candidate selection, gate synthesis or runtime claim.

The proof also records a per-witness quadratic second-moment bound under exact equality. That identity does not supply the uniform adaptive-selection and alternative-side estimates needed for a faster tester. Parameter count alone cannot justify a square-root-parameter copy bound: accepted P1 lower bounds already rule out that blanket conclusion in their stated domain.

## Verification and computability qualification

The producing note is preserved unchanged, including its historical candidate header. The accompanying review records the later scoped hand/source acceptance by a separate assistant reviewing context. It is not external peer review or Lean verification. The finite author checks contain exact rational Sylvester/completion identities and explicitly noncertifying two-qubit numerical diagnostics; they supplement the parameterized hand proof.

For an effective finite implementation, beta and requested tolerances must be known computable numbers with the precision needed to specify the candidate matrices. The existential statement for arbitrary real beta uses the ideal known-matrix collective-measurement model. This qualification applies to the producing note's finite-computability wording; it does not change its all-real-beta mathematical adequacy claim.

## Attribution and relation to prior work

- Lu--Fang, [arXiv:2501.07292v2](https://arxiv.org/html/2501.07292v2), Lemma2/Eq.(3) and Lemma4/Eq.(37), supplies the midpoint variational/Sylvester framework.
- [NIST DLMF Eq.4.36.2](https://dlmf.nist.gov/4.36.E2) supplies the classical hyperbolic-function product underlying the Fourier identity.
- Badescu--O'Donnell, [CorollaryA.4](https://www.cs.cmu.edu/~odonnell/papers/quantum-data-analysis.pdf), supplies collective Threshold Decision.
- Hastings, [Quantum Belief Propagation](https://arxiv.org/pdf/0706.4094), provides older related thermal-filter methodology. Its stronger geometric locality hypotheses are not imported here.
- The earlier [full-class upper](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md) and [accepted lower32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) remain the relevant full-class constraints.

No historical novelty is established. The useful distinction is that a uniformly adequate family can avoid inverse-state conditioning while its acquisition/search cost still fails to improve the optimal-copy gap.
