# A limitation of the logarithmic-difference measurement at fixed temperature

17 October 2026. Author: dot (OpenAI), working with Nolan. Coordinating mathematical review: dot (OpenAI), in a separate reviewing pass.

**This pair is easy to distinguish by measuring its data qubit. This packet does not improve the unrestricted P1 copy lower bound or solve P1.** It rules out a proposed shortcut that measures only the spectral projectors of the exact Gibbs logarithmic difference, or scalar-function postprocessings of that measurement.

## Reviewed result

For every fixed inverse temperature beta > 0 and every sufficiently large N, an explicit noncommuting, three-local pair has full trace distance at least 1/4, while its logarithmic-difference measurement has outcome total variation O_beta(1/N). Every Hamiltonian Pauli coefficient has magnitude at most one. All reservoir, mediator and data qubits count toward N. The construction uses growing degree and per-site interaction sum, as permitted by the original coefficientwise-bounded class.

The measurement restriction matters: resolving additional information inside a degenerate score eigenspace is outside it. A data-qubit measurement does precisely that and has a constant signal. The restricted sequential lower bound fixes the same score-projector measurement under the null and alternative; it supplies no oracle for the unknown pair's logarithmic difference.

## Status and evidence

- [The complete derivation](P1-LOCAL-SCORE-MEASUREMENT-CANDIDATE-28.md) preserves its original producing-pass candidate status and exact bytes.
- [The coordinating review](P1-LOCAL-SCORE-MEASUREMENT-REVIEW-28.md) accepts the stated mathematical scope by hand review, including coefficient collisions, both reservoir phases, the limiting gap and the measurement restriction.
- [The checker](check_local_score_28.py) and [its actual output](check_local_score_28.log) supplement the proof with 24 ordinary floating-point full-matrix versus sector-formula comparisons. The maximum discrepancy was 3.3306690738754696e-16. Larger examples use sector formulas. A printed zero leakage probability at R=1000 is numerical underflow, not an exact zero.
- These are not interval certificates, Lean proofs, external peer review, laboratory validation, or an exhaustive historical-novelty audit.

Run the supplementary check with Python, NumPy and SciPy already available:

    python check_local_score_28.py

## Prior work and remaining obligation

The symmetric relative-entropy identity and virtual-transition mechanism are established background. The primary comparison is [Bluhm et al., Certifying and learning local quantum Hamiltonians, arXiv:2603.29809v1](https://arxiv.org/html/2603.29809v1), particularly Lemma 4, Lemma 15 and Theorem 17. Their energy and moment estimates retain their parameter-dependent resource assumptions; this packet does not refute them or establish historical novelty.

The original P1 problem still permits arbitrary collective measurements on copies of two unknown states. Its full optimal copy complexity remains open in this project. Components 26 and 27 remain unchanged. The missing positive step is a uniformly controlled, copy-only selection of an adequate measurement across the full admitted class; score locality alone does not provide it.

SHA-256 hashes and byte lengths are recorded in [MANIFEST.json](MANIFEST.json).
