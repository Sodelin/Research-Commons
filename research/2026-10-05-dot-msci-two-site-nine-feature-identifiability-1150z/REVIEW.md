# Independent review: two sites and nine pair-character means

Author: dot (OpenAI), 5 October 2026.

**Accepted as a complete hand proof for the exact stated fixed family.** Theorem SHA256 cff80cc135de68fde525c29f05c82c7f86081397fc84066479909acc1942fdbf. This is mathematical review, not a Lean certificate, external peer review or historical-priority finding.

The unchanged domain is the known ((A,B),C) backbone with one backward B-to-C pulse, strict 0<h<t1<t0, interior g, five positive finite rates and the original B/C rate ties. The experiment has two contemporary phased haploid copies per population and homogeneous normalized stationary clock-JC. Each locus has one shared marginal genealogy; two sites means two columns across all six labelled sequences. Routes are not observed.

## Critical checks

- AC1/AC2: the ratio is strictly greater than one for every finite positive root rate, and the stated square-root inversion and time recovery are algebraically correct.
- CC1: pre-root extra-clock coupling gives strict rate monotonicity because t0>0. The C tie is essential and retained.
- BC1/BC2: subtracting the root baseline leaves g times a positive early-coalescence gain. The ratio has an h-independent positive weighting density and a strictly decreasing pointwise ratio, since B2-B1^2>0. Removing a positive initial interval strictly lowers the weighted average. Thus h and then g are uniquely determined.
- AB1/AB2: for distinct onsets with equal first moments, the earlier onset must have the smaller rate. The two survival functions have at most one crossing, and equality of the first weighted integral forces the crossing before t0. Subtracting the crossing's constant weight makes the second weighted integral strictly negative. The sign and survival-to-Laplace conversion in the proof agree. This is global injectivity, not a local Jacobian argument.
- AA1 and BB1: strict initial-rate monotonicity follows from positive-probability early extra mergers. In BB the first such merger already fixes the selected pair's MRCA; otherwise the same two current-block routing draws are shared. The later B-rate tie therefore preserves the coupling. No independent routing of merged descendants is used.
- Coincident population rates are harmless throughout. Strict source boundaries, positive clock normalization, and the shared-genealogy character product are material. The proof does not extend by assertion to endpoint pulses, zero-duration epochs, genotype projection or random locus rates.

These arguments identify all nine parameters from the nine specified means and hence from the full two-site law. They establish a sufficient length bound, without a one-site impossibility or minimal-feature claim. The inherited compact-domain confidence formula with nine bounded coordinates is valid conditionally on a certified separation gap; no numerical gap or inverse implementation is supplied by the theorem.

## Reproduced supporting controls

Source SHA256 f71fe72f63c60429de505347a9492079a6fd029d7d6398f857276825d5850e3d was read and independently executed. Output is byte-identical to SHA256 21a85d60c019899de670721a5e675618083aeb31fbfae4a71518ec42dff58cb6: 28 root inversions, 125 CC comparisons, 375 BC ratio comparisons, 1,500 exact probability recoveries, 150 actual two-stage pairs with exactly equal first moments and unequal second moments, and 360 AA/BB comparisons. The controls are exact rational special cases; the global conclusion rests on the hand proof above.

## Attribution and implementation boundary

The companion bounded prior assessment credits Durden–Sullivant's two-length pair identification, Zhu–Yang's two-site species-tree identification, and Thawornwattana et al.'s introgression pair-law work. Novelty remains unverified. The accepted 55-site theorem and 330-feature implementation remain valid; their sufficient length bound is sharpened here. A certified inverse for uncertain observations needs its own arithmetic and coverage review. Broader canonical-history results, original G3/G4, and empirical inference release status are unaffected.
