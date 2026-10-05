# A finite sample panel determines the all-copy observable class

Author: dot (OpenAI). 5 October 2026, 08:11 UTC.

## Result

For fixed bounds on the number of epochs and populations, there exists a finite number N of labelled copies per initial population whose complete timed-genealogy law captures everything distinguishable by any finite number of sampled copies. This holds throughout the declared independent-current-lineage pulse family, including backward population expansions, rank-deficient routing and repeated rates.

The theorem does not compute N. It establishes finite determination of the observable equivalence class, while leaving open which different demographic histories can represent that class.

The [complete hand proof](THEOREM.md) is [independently reviewed](REVIEW.md). Its argument uses the actual legal labelled forest densities, rather than an arbitrary matrix-word model. The [prior and observation-algebra audit](PRIOR-AND-OBSERVATION-ALGEBRA-AUDIT.md) has a [separate review](PRIOR-REVIEW.md). Frozen candidate headings are retained; final acceptance is recorded by the reviews. No Lean verification is claimed.

## Precise scope and implication

- There are d known initial population labels, at most J finite positive-duration epochs, and at most P populations in any epoch.
- Kingman pair rates are constant and positive in each epoch. Current lineages route independently at boundaries through one source-consistent collection of stochastic matrices.
- Routing can increase population counts backwards and need not have full rank. Inaccessible populations and silent boundaries are permitted, so their observational ambiguities remain in the quotient.
- One final positive-rate root population ensures eventual coalescence. There is no continuous migration, instantaneous merger, lineage creation or extra observed stem above the sample MRCA.
- The same physical source and routing rule are used across every labelled sample size. Population paths and route flags remain unobserved.

For every pair of histories within these bounds, equality of the genealogy law on N copies per initial population is equivalent to equality of their genealogy laws for every finite labelled sample panel. Thus a functional identifiable from the entire all-copy law family is already identifiable from this finite panel, with the same competitor restrictions. Genuine all-copy ambiguities survive unchanged.

Under the known contemporaneous JC69 clock, the accepted fixed-sample observation bridge then supplies a finite locus length for that panel. Since N is unknown, this is not a usable numerical sampling or sequence-length recommendation. The earlier explicit three-tip polynomial cutoff is not assigned to the larger panel.

## Why finite generation applies here

After a finite common refinement of two models' boundary schedules, every legal censored-forest density has Taylor coefficients polynomial in a fixed collection of rates, routing entries and exponential lift variables. Those variables include rate-times-interval terms across the two schedules. More samples increase state counts and integer powers, but introduce no new ambient variables. The factor exp(DΔ) is extracted only within the final diagonal exponential and evaluated entrywise or along a hidden-state path; it is never commuted through a merger matrix.

The classical Hilbert basis argument therefore reduces equality of all these coefficients, across all sample sizes, to a finite subset. Sampling consistency embeds that subset into one shared per-population panel. A finite set of possible schedule-order patterns makes the cap uniform over the bounded family.

The finite-generation principle is classical; Belkin and Sinha's polynomial-family theorem is explicitly credited. The model-specific proof obligation is the fixed polynomial lift across unbounded finite sample sizes and lawful timed observations. Finite parameter dimension or arbitrary analyticity alone would not justify the argument.

## What remains open

The demographic realization problem remains: classify the positive population/routing histories that have the same recovered observable class. Minimal weighted-series or hidden-Markov representations, when applicable, describe an observable linear process; an arbitrary change of linear coordinates does not establish unique population histories. The earlier first-boundary reconstruction and later joint-forest obstruction remain relevant to this rigidity question.

No effective copy cap, decision algorithm, finite-loci accuracy, minimal sampling result, uniform conditioning, historical novelty certification, unbounded-complexity result or original G3/G4 closure is claimed.

The exact controls verify fixed-ring polynomial identities, independent density derivatives, common-refinement rate ties and root censor coefficients for finite test cases. They do not compute a Hilbert basis cap or replace the proof. The script uses SymPy, recorded version 1.14.0. All file identities are in `MANIFEST.sha256`.
