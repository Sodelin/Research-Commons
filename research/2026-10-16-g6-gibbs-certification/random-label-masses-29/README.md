# Testing Gibbs states: common random label masses

17 October 2026. Research by dot (OpenAI), working with Nolan.

**Accepted at scoped hand-proof level after separate assistant-context statistical and physical-encoding reviews.** Both receipts are included. These are assistant reviews, not external mathematical peer review. The original producing-pass candidate is preserved byte for byte, including its historical “awaiting review” header; this wrapper and the dated receipts record the later acceptance.

## Reviewed result

For every fixed integer `k >= 5`, inverse temperature `beta > 0`, and fixed full-trace-distance accuracy `0 < epsilon <= 1/1024`, the reviewed argument gives the worst-case total-copy lower bound

```text
Omega_{k,beta,epsilon}(
  N^((2k+1)/3) / (log N)^((2k+1)/(3(k-1)))
)
```

for every sufficiently large number `N` of physical qubits. The task is to distinguish exact equality of two unknown Gibbs states from full trace norm at least `epsilon`, with success at least `2/3`. Arbitrary adaptive source selection and collective quantum measurements are allowed. The Hamiltonians have Pauli weight at most `k` and each nonidentity Pauli coefficient has magnitude at most one. Interaction degree and total strength at a site are unrestricted. A diagonal subclass establishes a lower bound for the larger noncommuting class.

The improvement concerns a component of the original optimal-copy problem. At `k=5`, the power becomes `11/3`, above component 27's `7/2`. At `k>=6`, it exceeds component 24's power `2k/3` by `1/3`. There is no claimed improvement for `k=3` or `k=4`. The general upper remains `O(N^k log N)` at fixed parameters; the gap is open. The bound does not give optimal dependence on temperature or accuracy.

## Why the statistical construction is different

The two states share unknown label probabilities. Rare heavy labels carry identical conditional data laws. More numerous light labels carry the differences. The heavy labels mask count patterns that would otherwise reveal the differing rows. Both source states retain exactly the same normalization for every latent draw.

The proof keeps the full two-source count mixture and all data coordinates sharing each label count. It controls the complete product-row likelihood, rather than treating its coordinates as independently timed observations. Conditioning the alternative prior on the event of sufficient separation has an explicit probability cost. A Poisson experiment supplies a fixed worst-case total-copy experiment with a uniform shortage bound.

The physical encoding includes the label-energy term `-log(weight)`, counts every label clone, data spin and reservoir spin, and checks collisions among Pauli coefficients. The latent label mass is an unknown coefficient choice, not an extra observable register. The construction relies on unrestricted degree and total local strength; no practical state-preparation or hardware claim is made.

## Evidence and limits

- The candidate contains the parameterized hand argument, physical encoding, finite guards and padding to every sufficiently large `N`.
- The author's exact SymPy checker passed 144 rational coordinate/product-row cases, four explicit full-row likelihood sums and eight shared-mass denominator cases. It also checks the polynomial and Poisson identities used in the proof. These checks supplement the hand argument; finite enumeration does not prove the asymptotic result.
- The statistical review independently checks the full likelihood argument, conditioning and copy-budget reduction. Its separately written checker passed 405 exact rational cases and a joint shared-mass denominator check. The physical review checks every coefficient, leakage guard, spin count and padding step. Both are separate assistant-context hand reviews, not external peer review.
- There is no Lean verification, established historical novelty, experimental validation or full P1 solution.

## Attribution

The heavy/light coordinate prior comes from Canonne, Diakonikolas, Kane and Stewart, [*Testing Bayesian Networks*, Section 5.2 and Theorem 40](https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf), and was used in components 26 and 27. Multiple probability-mass scales and Poisson lower-bound experiments are classical distribution-testing tools; see Chan, Diakonikolas, Gregory Valiant and Paul Valiant, [*Optimal Algorithms for Testing Closeness of Discrete Distributions*, Section 4](https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf). Neither reference is claimed to supply the exact combined row prior and physical encoding here. Historical novelty of that combination remains unestablished.

The physical clone/reservoir construction reuses the reviewed [component 24](https://github.com/Sodelin/Research-Commons/blob/0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d/research/2026-10-16-g6-gibbs-certification/reservoir-amplified-lock-24/README.md) and [component 27](https://github.com/Sodelin/Research-Commons/blob/0daba51d070c50bc10153a9272eab0e436484841/research/2026-10-16-g6-gibbs-certification/averaged-shared-counts-27/README.md). The earlier uniform-label construction is preserved in [component 26](https://github.com/Sodelin/Research-Commons/blob/a823c8445e1dd2ce4cb4008a547958fa50bac810/research/2026-10-16-g6-gibbs-certification/conditional-product-label-26/README.md).

## Files

- `P1-RANDOM-LABEL-MASS-CANDIDATE-29.md`: unchanged producing-pass proof candidate.
- `check_random_label_mass_29.py`: author's exact finite checker.
- `check_random_label_mass_29.log`: successful checker output.
- `P1-RANDOM-LABEL-MASS-INDEPENDENT-STATISTICAL-REVIEW-29.md`: separate assistant-context statistical review.
- `independent_statistical_check_29.py` and `.log`: separately authored statistical checker and successful output.
- `P1-RANDOM-LABEL-MASS-PHYSICAL-REVIEW-29.md`: separate assistant-context physical-encoding review. Its attribution line is normalized for this public packet; mathematical text is unchanged.
- `MANIFEST.json`: exact file hashes, source preservation and verification scope.

Run the author checker with `python check_random_label_mass_29.py` (SymPy required), and the separate statistical checker with `python independent_statistical_check_29.py` (Python standard library only), from this directory. These reproduce the finite checks, not the entire hand proof.
