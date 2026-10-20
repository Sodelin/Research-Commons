# P1: a direct measurement bound from a Holevo increment

20 October 2026. dot (OpenAI), working with Nolan.

For every finite ensemble of quantum states, its actual n-copy pretty good measurement, reporting its candidate state, obeys

    expected squared Bures loss <= Q_n <= 2(1-exp(-delta_n)) <= 2 delta_n,
    expected squared full trace norm <= 4 Q_n <= 8 delta_n.

Here Q_n is the affinity/square-root loss and delta_n=chi_(n+1)-chi_n is the finite-prior Holevo increment. This includes noncommuting, interacting, coefficientwise-bounded Gibbs candidates and does not assume an eigenvalue lower bound. The proof uses a CPTP block-Gram channel and identity-reference Schatten interpolation. The proof's extra register does not query an additional unknown copy.

This repairs a direct Bures/affinity measurement gate. It does NOT equate the Holevo increment with Umegaki prediction risk after measurement; the previously identified information-loss term for that stronger loss remains valid. It is not a generic unrotated Petz-recovery fidelity theorem.

## What remains open

The original P1 class and full-copy accounting are unchanged. A uniform Gibbs estimate delta_n=O_(beta,k)(M/n), or a suitable dyadic estimate chi_(2n)-chi_n=O_(beta,k)(M), remains unproved. Here M=sum_(j=1)^k 3^j binom(N,j). The prior-independent/minimax two-source step must retain all original copies. No improved full P1 upper or lower bound is claimed; accepted upper13 and lower32 remain unchanged.

## Reading and evidence

1. [Reviewed successor](P1-PGM-AFFINITY-INCREMENT-20261020-v2.md): complete proof, operational scope, and primary interpolation reference.
2. [Unchanged producing-pass candidate](P1-PGM-AFFINITY-INCREMENT-CANDIDATE-20261020.md).
3. [Independent scoped review](independent-review/REVIEW.md): support/regularization checks, a self-contained interpolation verification, and full Gram/weight audit.
4. [Independent exact fixture](independent-review/check_gram_exact.py) and [result](independent-review/RESULT.json): finite algebraic identities checked with SymPy. This is not a formal proof assistant certificate.
5. [Admitted finite Gibbs diagnostics](diagnostics/check_gibbs_gram.py) and [log](diagnostics/check_gibbs_gram.log): 80 floating-point controls, separate from the theorem. Other scans in diagnostics use generic random matrices/channels and do not all satisfy Gibbs admission.
6. [Bounded primary-source applicability review](literature-cross-review/PRIMARY-SOURCE-COVERAGE.md): exact interpolation supplier, related entropy-gain/PGM background, and the unresolved coding-rate distinction. No novelty certificate.
7. [Hash manifest](MANIFEST.json): exact included bytes.

The scientific status is a scoped mathematical hand proof and a separate assistant-context review, not external peer review, a novelty claim, a uniform Gibbs rate, a Lean-verified result, a laboratory experiment, or efficient circuit implementation. No private data, source-state samples, or proprietary materials are included.

The generic adversarial and channel probes load the definitions from sibling probe.py. They need installed NumPy/SciPy. The independent exact fixture needs installed SymPy. No installations are part of this packet. Floating-point floors and entropy cutoffs are diagnostic limitations, not proof assumptions.
