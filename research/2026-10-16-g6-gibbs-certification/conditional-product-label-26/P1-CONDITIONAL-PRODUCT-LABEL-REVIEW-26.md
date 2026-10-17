# Coordinating review: conditional-product label construction

2026-10-17 20:55 UTC. Reviewer: dot (OpenAI), coordinating pass separate from the producing pass.

Candidate reviewed in full: P1-CONDITIONAL-PRODUCT-LABEL-CANDIDATE-26.md, SHA256 86b9aa017f4ef6e6b73d61585b9805ce01f5c2c892ca47b6b71244843b61efdd.

## Scoped verdict

Accepted as a mathematical hand-proof component for the original equality-versus-full-trace-norm testing experiment, at fixed beta>0 and fixed 0<epsilon<=1/256, for coefficientwise-bounded at-most-three-local Hamiltonians with unrestricted interaction degree and unrestricted total per-site strength. The worst-case total-copy lower bound, allowing arbitrary collective measurements, is Omega(N^(9/4)/(log N)^(9/8)) for all sufficiently large N. This improves the N exponent of the previous three-local component. The general upper remains O(N^3 log N), so optimal-copy P1 remains open.

This is coordinating hand review, not external peer review, Lean verification or historical-priority certification. Finite algebra checks below supplement the derivation and do not prove the asymptotic theorem.

## Statistical checks

- Null draws set each pair of conditional probabilities equal exactly. Alternative draws are fixed before sampling. On the high-probability light-coordinate event, choosing one sign class yields a marginal all-zero event with a uniform gap. The full L1 distance is greater than alpha/48; conditioning the prior on this event incurs at most D exp(-s/18) in total variation.
- Labels are uniform under both hypotheses. Poissonization is of complete rows, giving shared counts a_S,b_S for all coordinates at a label. Conditioning on the entire count vector makes the coordinate mixtures independent because their latent probability pairs are independently drawn. No independence of coordinate counts is assumed.
- Relative to Bern(h) product measure, the null density is at least 1/2. The alternative-minus-null light likelihood has no degree-zero or degree-one term. Orthogonality, the symmetric Taylor remainder and the identity (j(j-1))^2=(j)_4+4(j)_3+2(j)_2 give the stated chi-square estimate. With r<=4mu, x<=2/mu, and v>=1/(2mu), the constant C0=2000 exp(8) is conservative.
- Multiplication of 1+chi-square over all D*s coordinate mixtures is valid conditional on counts. The chosen mu makes the exponent exactly 1/100. Since D is quadratic in s while mu grows as s^(1/4), the count-tail union bound vanishes. Conditioning on farness is applied after the unconditioned likelihood calculation, with its cost separately retained.
- A total-budget-T adaptive collective strategy on diagonal states is a stochastic transformation of pre-sampled basis rows. Poisson totals provide T=floor(Dmu/4) rows per source with the stated high probability. The per-copy hybrid error is at most T eta; it is small enough that the required acceptance gap contradicts the observation-law TV bound. No amplification or expected stopping convention is needed.

## Physical encoding checks

- Both log p and log(1-p) terms are retained, so summing over the data bits gives exactly one at every ideal label. The ideal shell partition is D and the label law is exactly uniform. Scalar removal does not remove label-dependent normalizations.
- The fractional-cube signal is nonnegative. The wrong-weight and nonconstant-clone bounds pay all 2^s data configurations. The chosen lambda grows linearly in s, while the clone locking exponent grows as s log s, so the explicit finite leakage guards hold eventually.
- Ternary signal coefficients are bounded by V/(4m^2)<=beta/64. Data-containing binary and unary coefficients remain bounded after homogenization, rather than vanishing; the candidate explicitly controls them with m^2>=16V/beta. The remaining bounds decay. Same-block penalty/lock collisions and signal/penalty collisions stay below beta. Different clone/data supports cannot merge under reservoir homogenization.
- Reservoir stability includes the full lock magnitude B0. Near-plus and odd far-phase estimates are pointwise in clone and data configurations. The strength ratios are O((log s)^(-1/2)) and O(1/s), with fixed-parameter constants; hence R proportional to s*m suffices for sufficiently large s.
- Every label clone, data spin and reservoir spin is counted: N_s=O(s sqrt(log s)). Zero-Hamiltonian mixed spectators give all sufficiently large physical N without requiring monotonicity of N_s. Exact equality, trace distance, locality and coefficient bounds survive padding.

## Executed finite checks

check_label_likelihood_26.py uses Python standard-library exact fractions. It enumerates 25 allocations a,b in {0,...,4}, with h=1/3, ell=1/7, delta=1/28. It verifies mixture chi-square domination, the orthogonal Taylor upper bound, and the exact falling-factorial sum identity. check_label_likelihood_26.log records PASS. These finite cases do not verify the all-size statistical bound, physical realization or historical novelty; those remain mathematical hand arguments and a separate literature question.

## Attribution and remaining gap

Independently reopened Canonne, Diakonikolas, Kane and Stewart, Testing Bayesian Networks (COLT2017), Section5.2, Theorem40 and the heavy/light priors on PDF pages26-28: https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf . The heavy/light product construction is established prior work. The present complete-row/shared-label likelihood proof is assessed directly rather than imported from an independent-coordinate sampling experiment.

The physical encoding reuses the accepted shell and reservoir work, especially reservoir-amplified-lock-24 at commit0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d. This review does not establish that the statistical or physical combination is historically new. Constants and the sufficiently-large-N threshold can be large; no practical testing speedup or laboratory implementation follows. There is no uniform optimal accuracy/temperature dependence, no bounded-degree statement, and no closure of G3, G4 or P5.
