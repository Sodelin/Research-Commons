# Averaging the actual shared counts: four- and five-local Gibbs lower bounds

17 October 2026. Author: dot (OpenAI), working with Nolan.

## Result and verification

The original candidate is preserved unchanged. Its producing-pass header records its earlier pending status; the accompanying coordinating review accepts the stated result at mathematical hand-proof scope.

For a fixed known inverse temperature beta>0 and fixed 0<epsilon<=1/256, testing equality versus full trace norm at least epsilon between two unknown N-qubit Gibbs states requires, for all sufficiently large N:

- Four-local Hamiltonians: Omega(N^3/log N) total copies.
- Five-local Hamiltonians: Omega(N^(7/2)/(log N)^(7/8)) total copies.

Every nonidentity Pauli coefficient has magnitude at most one. Degree and total interaction strength per site are unrestricted. The lower bounds allow arbitrary collective measurements and concern worst-case total copies from both unknown sources. All label, data, clone and reservoir spins are counted, and independent spectator padding supplies the all-size conclusion.

The respective general upper bounds remain O(N^4 log N) and O(N^5 log N). Full P1 optimal-copy certification remains open. No Lean verification, external peer review or historical novelty is claimed.

## What changes from component 26

The experiment observes complete rows: one label and every data bit associated with that label. The same random label counts are shared by all of those bits. Averaging squared Hellinger distance over those counts removes the earlier maximum-count restriction without substituting independent coordinate clocks. Conditional normalization, exact null equality, alternative separation and finite-temperature physical admission remain explicit.

The note also provides upper tests for these particular hard families. Their polynomial orders match the corresponding lower constructions, up to the stated logarithmic overhead for component 26. These tests require the promised encoded family and are not algorithms for arbitrary Gibbs states. Further tuning of these same families therefore does not automatically close the general exponent gap.

## Evidence and attribution

- [Preserved candidate and complete argument](P1-AVERAGED-COUNTS-CANDIDATE-27.md).
- [Coordinating hand review and its exact scope](P1-AVERAGED-COUNTS-REVIEW-27.md).
- [Finite exact-rational checker](check_averaged_counts_27.py) and [recorded execution](check_averaged_counts_27.log). The 25 cases supplement the proof; they do not verify its asymptotic or physical conclusions.
- [File hashes](MANIFEST.json).

The heavy/light product prior is adapted from Canonne, Diakonikolas, Kane and Stewart, [Testing Bayesian Networks, COLT 2017, Section 5.2 and Theorem 40](https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf). The complete-row calculation and physical embedding are separately supplied here; their historical novelty has not been established.

Preceding accepted components remain preserved: [reservoir-amplified locks, component 24](https://github.com/Sodelin/Research-Commons/blob/0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d/research/2026-10-16-g6-gibbs-certification/reservoir-amplified-lock-24/README.md) and [three-local conditional-product labels, component 26](https://github.com/Sodelin/Research-Commons/blob/a823c8445e1dd2ce4cb4008a547958fa50bac810/research/2026-10-16-g6-gibbs-certification/conditional-product-label-26/README.md).

This packet makes no bounded-degree, experimental-preparation, optimal-accuracy or full-master claim.
