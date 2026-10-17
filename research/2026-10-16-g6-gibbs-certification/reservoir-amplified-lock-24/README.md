# Reservoir-amplified clone locks: a sharper P1 lower-bound component

17 October 2026. Attributed research by dot (OpenAI), working with Nolan.

For every fixed k >= 3, beta > 0 and 0 < epsilon <= 1/4, the reviewed construction gives the all-sufficiently-large-N lower bound

    Omega(N^(2k/3) / (log N)^(2/3))

for testing equality versus full trace-norm separation at least epsilon between two unknown N-qubit Gibbs states at the same beta. Hamiltonians are at most k-local with every nonidentity Pauli coefficient bounded by one. The copy budget is worst-case total copies, and arbitrary collective measurements are allowed. Interaction degree and total strength per site are unrestricted.

The previous accepted shell construction gave Omega(N^(2k/3)/(log N)^(2k/3)). This improvement reduces the logarithmic encoding overhead by sharing the reservoir with the clone locks. All auxiliary spins and overlapping coefficient contributions are counted. The upper bound remains O(N^k log N) at fixed parameters, so optimal-copy P1 remains open.

## Evidence and reading order

- [Unchanged producing-pass candidate](P1-RESERVOIR-AMPLIFIED-LOCK-CANDIDATE-24.md): the full construction and hand proof. Its historical pending-review header is retained.
- [Coordinating hand review](P1-RESERVOIR-AMPLIFIED-LOCK-REVIEW-24.md): accepted scoped result and checked assumptions.
- [Amplification clarification](AMPLIFICATION-CLARIFICATION-24.md): constant-factor explanation of the final sample reduction.
- [Hash manifest](MANIFEST.json): exact source bytes.

This is a reviewed mathematical hand proof. It is not external peer review, a Lean-verified result, a computational experiment, or a claim of historical novelty. It gives no improved k=2 bound, uniform optimal epsilon dependence, bounded-degree result, efficient state preparation, or laboratory validation.

The testing hardness is imported from Chan, Diakonikolas, Gregory Valiant and Paul Valiant, [Optimal Algorithms for Testing Closeness of Discrete Distributions, Theorem 1.1](https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf). The prior [shell21 proof](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-ALL-K-SHELL-CANDIDATE-21-v2.md) and [review](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-ALL-K-SHELL-21-COORDINATING-REVIEW.md) remain preserved. No P5, G3 or G4 master obligation is changed.
