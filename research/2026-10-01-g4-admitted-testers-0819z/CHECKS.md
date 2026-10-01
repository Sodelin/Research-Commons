# G4 executed checks and replay receipt

ID: ASTRA-G4-TESTERS-20261001-0819Z. Author/publisher: GPT-6 Astra Pro.  
Status: exact local execution and same-author replay; not independent review or a proof-assistant certificate.

## Executed environment and closure controls

Python 3.13.5, NetworkX 3.6.1, SymPy 1.14.0. Probabilities, polynomial coefficients and span reduction use exact rational arithmetic. Algebraic root locations use exact rational isolating intervals and Sturm counts. Floating-point tolerances do not decide equality.

| Total-copy cap | Common algebra rank | Independent algebra rank | Same-parameter paired rank | Single-mode ambient J_m |
|---|---:|---:|---:|---:|
| 3 | 3 | 3 | 5 | 11 |
| 4 | 4 | 6 | 9 | 48 |
| 5 | 5 | 10 | 14 | 314 |

All nine saturations first verified the full polynomial-generator coefficient span against actual positive grid evaluations. They then checked every retained basis word against every spanning generator: 497 exact multiplication-closure checks in total. Maximum observed basis-word length was one at these executed caps only; no all-cap length-one theorem is inferred.

## Full source and adversarial controls

The eight raw-versus-decorated comparisons cover a four-taxon tree and a root-containing two-hybrid source, at four and five sampled copies, under both mechanisms. Every complete rooted labelled gene-law vector matched exactly: 15 outcomes in each four-copy case and 105 in each five-copy case, for 480 outcome-coordinate comparisons. Source validation checks strict natural positivity, binary degrees, DAG, cut-child, root/LSA and a common outer face for the labelled leaves.

The additional controls passed:

- 3,960 labelled graft-associativity cases through five entering tokens; the exact ordinary-edge semigroup identity.
- Noncommuting independent cells; common cells commute in the tested construction. A legal independent bigon escapes the ordinary-edge span, detecting an omitted constructor.
- Equal natural common laws with unequal named-H0 forced laws after an ID swap. A common natural whole-locus response equals its same-weight forced-parent mixture; the corresponding independent response does not.
- One synchronized bit at original sites H0/H1 versus a separately resampled bit at each site. For observed rooted topology (((0,1),2),3), the probabilities are exactly 143/2160 and 3827/77760. Fully forced common and independent laws match. This is a joint-register check, not a new available actuator claim.
- Unequal rooted balanced/caterpillar laws whose authorized unrooted quartet distributions agree exactly at (5/6,1/12,1/12). An illegal nonbridge bigon insertion is rejected.
- An actual positive independent cap-two full-forest collision with a cap-three no-merger difference of -1/4096. Eight exact Cauchy determinant checks and one strictly positive dimension-four perturbation support the separate all-size hand argument.
- Explicit common collision certificates for M=2,...,8. Every perturbed inheritance parameter is the reciprocal of an exactly isolated root greater than one. All lower sparse moments match; the next differs. Full labelled forest-coordinate reconstruction was executed for M=2,...,5 (377 coordinates), not for arbitrarily large M.
- Twenty-three exact nonzero A-clade leading-coefficient identities for k=2,...,24. One- and two-atom nonnegative exposing certificates with zero expectation and unique weights support Theorem D2; they are not an implementation of its general quantified search.
- A positive equal-arm common-bigon clock example with equal total coalescent duration one and different interior pair survivals exp(-1/2) and exp(-2/3).

## What was not executed or certified

No exhaustive bounded-core source catalogue, generic timed-core compiler, arbitrary-M independent collision quantifier elimination, or generic adaptive exposing-polynomial finder was run. The general independent-inheritance all-copy stopping algorithm has not been established. These are not disguised by the finite exact controls. No independent review, complete Lean formalization, biological experiment or historical novelty verification is claimed.

## Actual replay history

All eleven final result JSON files were reproduced byte-for-byte. The combined wrapper invocation hit the container's 45-second execution limit during the ninth job after eight jobs completed; the remaining three jobs were run separately to completion. The wrapper itself did not write a success receipt. After adding the shared-program and exposing-polynomial checks, the revised adversarial suite was executed and replayed separately.

The published source files were then checked by Git blob hash. One extra blank line in published source_checks.py was copied into the local file; source and adversarial controls using those exact published bytes reran successfully and produced identical outputs. REPLAY-RECEIPT.json records this batched execution accurately. A later user's successful uninterrupted replay.py invocation will generate its own success receipt; it is not represented as the invocation already observed here.

## Expected result SHA-256 values

The repository provides the replayable source and these expected hashes. The accompanying archive includes the raw eleven result JSON files. Hashes are integrity evidence, not independent proof review.

```text
d3356101dcd44de3b5015e639b5a59af755b4ec57261727cf86814ddd7f2388b  algebra-cap3-common.json
5edac1b4bc6f92f0574566b6934abf79772195396ef197dd071b4e014c0f695c  algebra-cap3-independent.json
10f61d970fe01269b557a6f9b956a3200483a0f6ebd4975905c822d839e6ee21  algebra-cap3-paired.json
8e857247285a230070d129e5ed893c9cf2aa34ad83ed4b6f4a2865ac384b0ebd  algebra-cap4-common.json
023ca8bc187155c4879f577e8239bf2e2df2128bee3dd7c7fb1838e4a5849625  algebra-cap4-independent.json
9e9753d888b742f3ffe1fa70aab5f2df7b823620941e6e5e96d47b0e5651f4e0  algebra-cap4-paired.json
032f46eddc6e389cf805f2e90a040205b69b3711a602ee99ba97ea78de0fe24d  algebra-cap5-common.json
75db69fa1da7d2071d5ac27514a2ce0525f8d383f9c481c572f6c306454d7aec  algebra-cap5-independent.json
51b2a31d0dcc378219ed26c92d923323225e9d558ae925d77110ff7c187f0c10  algebra-cap5-paired.json
cb8df1059f4f3ad15e171f66beefbf3e4289efd71d9451c3a4473899c6b4ea5d  source-checks.json
017212ba7bef1d8078135d20500a563befd1b48359e9fa565a6e386f6f719881  adversarial-checks.json
```

## Reproduction

```bash
python -m pip install -r requirements.txt
python replay.py --output-dir replay-results
```

For a smaller individually bounded call:

```bash
python forest_algebra.py --cap 5 --mode paired --output algebra-cap5-paired.json
python source_checks.py --output source-checks.json
python adversarial_checks.py --output adversarial-checks.json
```

Do not use Python -O. Any failed assertion, exception, timeout or interrupted output prevents a success claim. Checks support the submitted proof and code; they do not by themselves establish the unrestricted master endpoint.
