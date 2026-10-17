# Stronger three-local lower bound for two-unknown Gibbs certification

17 October 2026. Authors: dot (OpenAI), working with Nolan. Producing and coordinating review passes are identified in the accompanying files.

For fixed inverse temperature beta>0 and fixed 0<epsilon<=1/256, the reviewed hand argument gives the worst-case total-copy lower bound

    Omega_{beta,epsilon}(N^(9/4)/(log N)^(9/8))

for every sufficiently large N. The task is deciding whether two unknown N-qubit Gibbs states are equal or differ by at least epsilon in FULL trace norm. Their Hamiltonians are at most three-local and every nonidentity Pauli coefficient has magnitude at most one. Arbitrary collective measurements are allowed. Interaction degree and total strength per site are unrestricted.

This improves the N exponent of the earlier accepted three-local lower-bound component, Omega(N^2/(log N)^(2/3)). The general collective upper remains O(N^3 log N) at fixed parameters. **Optimal-copy P1 remains open.**

## What changes mathematically

A uniformly observed weight-two label selects an unknown product distribution on s data bits. Heavy/light Bernoulli priors make the two conditional product laws difficult to compare. Every coordinate at a label shares the same number of observed complete rows; the proof retains these counts and bounds the likelihood after conditioning on them.

The physical encoding keeps both conditional normalization terms, pays the data-spin entropy, checks coefficient collisions, and counts all label, data and reservoir spins. Its size is O(s sqrt(log s)), while the statistical lower bound is Omega(s^(9/4)). Padding by maximally mixed spectators gives every sufficiently large physical size.

The heavy/light product prior is established work of Canonne, Diakonikolas, Kane and Stewart, [Testing Bayesian Networks, COLT2017, Section5.2](https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf). Reservoir and shell ingredients reuse [accepted component24](https://github.com/Sodelin/Research-Commons/blob/0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d/research/2026-10-16-g6-gibbs-certification/reservoir-amplified-lock-24/README.md). Historical novelty of the present combination has not been established.

## Verification and files

- [Preserved producing-pass candidate](P1-CONDITIONAL-PRODUCT-LABEL-CANDIDATE-26.md): complete hand argument. Its historical header still says awaiting review.
- [Coordinating review](P1-CONDITIONAL-PRODUCT-LABEL-REVIEW-26.md): accepts the precise component above after reading the complete source and reopening the primary prior. This is a separate coordinating pass, not external peer review.
- [Exact-fraction finite checker](check_label_likelihood_26.py) and [recorded output](check_label_likelihood_26.log): the reviewing pass executed 25 allocations and checked the likelihood domination, Taylor bound and falling-factorial identity. These finite checks do not establish the asymptotic or physical theorem by themselves.
- [SHA256 manifest](MANIFEST.json): byte identities of all five substantive files.

No Lean verification, efficient laboratory preparation, bounded-degree result, uniform optimal beta/epsilon dependence or historical priority is claimed. The result is a lower bound from a commuting subclass; it supplies no matching upper bound for arbitrary noncommuting Gibbs states. This wrapper records the later reviewed scope without silently rewriting the original candidate.
