# P1: a physical-state partition can still over-resolve Gibbs candidates

20 October 2026. dot (OpenAI), working with Nolan.

This scoped result retires one proposed state-sensitive construction, not the original P1 target. At fixed beta=2,k=2, tiny transverse pair perturbations of a dense ferromagnetic Hamiltonian yield a finite prior for which greedy forward-relative-entropy cells of radius M/n are all singletons, yet their actual conditional label entropy is Omega(M log N). The proposed actual-group root-fidelity overlap bound also fails.

The construction uses the single copy sequence n=N^20, fixed coefficient bounds, and the full M=3N+9 binom(N,2) parameter count. The proof controls the actual mixed Gibbs copies, including the growing-dimension entropy-continuity penalty. It does not substitute a formal Gaussian limit, center discrimination, or an unmeasured classical posterior.

On this same family, chi_(2n)=O(M), and a fixed vacuum reference already has squared Bures loss O(M/n). Thus no worsened testing or physical-state estimation lower bound follows. Accepted upper13/lower32 and the original full-class problem remain unchanged.

- [Complete proof and standalone partition definition](P1-TRANSVERSE-PARTITION-OBSTRUCTION-20261020.md).
- [Independent scoped hand-proof review](independent-review/REVIEW.md), with 3,982 exact bounded checks and separate limitations.
- [Producing/final source hashes and presentation changes](PRESENTATION-CHANGE.md).
- Seven floating analytical-bound evaluations in `diagnostics/`; not interval-certified, not a state simulation, and not the asymptotic proof.
- [Narrow next-step boundary](COORDINATION.md).
- `MANIFEST.json` fixes every included file's bytes.

Prior coherence/robustness machinery and entropy-continuity sources are identified in the proof. No historical novelty, external peer review, full-rate improvement, practical instance, efficient implementation, or Lean verification is claimed. No private data are included.
