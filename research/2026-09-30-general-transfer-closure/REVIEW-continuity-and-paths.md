# Independent review: all states and whole stochastic histories

Reviewer: `/root/current_sparse_scope_audit`. Date: 2026-09-30 UTC. Reviewed actual `continuity-and-paths.md`, including the newly added exact path criterion and sharp multiplicative bound. Source SHA-256: `9323c761d8cd0f7889caf057727c8bf79e8593f0a84b2afb081bf4c01244424e`.

**Verdict:** no fatal mathematical gap found in the stated results. The proofs establish their complete declared scopes, subject to the explicitly named classical prerequisites. This is independent hand-review, not proof-assistant verification, a novelty determination, or evidence that a biological model meets the premises.

## 1. Fixed-kernel almost-everywhere to every parameter

The direction and strength of both continuity assumptions are correct. For a fixed measurable Markov kernel, `Kf` is a bounded measurable source function. Setwise source continuity therefore makes its expectation continuous; weak target continuity supplies the other term for every bounded continuous target test. Weak source continuity alone would not suffice for an arbitrary measurable kernel.

A strict test discrepancy exceeding epsilon defines a nonempty open set. Full support forces positive prior mass, contradicting the one exceptional Borel null set on which the fixed kernel may fail. This argument uses neither a countable parameter class nor an uncountable union of null sets. It separately excludes each putative violating test and parameter. Continuous [0,1]-valued tests characterize TV for Borel probability measures on a Polish target by Radon regularity. These observations justify the same-kernel all-state conclusion for arbitrary topological parameter spaces supporting the specified full-support probability and continuous families.

The counterexamples distinguish necessary proof premises from stronger claims correctly. A discontinuous target can conceal a state where no simultaneous exact kernel exists. A discontinuous source can make the particular prior-valid kernel fail at an exceptional state even though a different global kernel works. Thus the second example does not falsely assert nonexistence. The result starts with a fixed simulator bound; it does not obtain that bound from one Bayes-risk comparison.

## 2. Complete exact path criterion

The added iff is correct for every specified pair of sequential laws on the countable product of nonempty standard-Borel spaces. Equality of full laws yields equality of consecutive-prefix joint laws. For a countable generating pi-system in the next-observation space, equality of integrals over every history event forces equality of the two corresponding measurable conditional probabilities almost everywhere. A countable union of exceptional sets then gives agreement of the entire conditional probability measures by the pi-system uniqueness theorem.

The comparison uses the common prefix law, which is `P`'s prefix law after full-law equality. Conversely, equality of initial laws and agreement of each pair of conditionals `P`-prefix-almost everywhere gives the next common prefix by induction. The finite cylinders determine the countable product laws. Different null sets for different times and parameters are legitimate; no prior or family domination is used. Conditional versions off reachable histories can differ. The criterion therefore covers all specified pairs, rather than demanding the stronger uniform-history premise of the approximate bound.

## 3. Sharp approximate bound and infinite-horizon passage

The common-submeasure proof has the correct TV normalization. For prefix laws with distance d, their common measure has mass `1-d`, and each positive residual has mass d. An event discrepancy of the residual difference is at most d, not 2d. Integrating conditional discrepancies over the common measure contributes at most `(1-d)e`. Hence the recurrence is `d_next <= d+(1-d)e`. Its monotonicity in d for `0<=e<=1` proves the stated finite product bound. No measurable maximal-coupling selection is required.

The infinite-path step is also valid. The increasing union of finite-prefix sigma-algebras is an algebra generating the product sigma-algebra. Under the finite measure `(P+Q)/2`, approximable events form a sigma-algebra: continuity from below controls the part of a countable union omitted by a finite initial union. Approximating the finite initial union then completes the argument. Consequently full-path TV equals the supremum of prefix TVs. This proves the decreasing-product limit bound for each pair, uniformly over every parameter satisfying the specified conditional bounds. No separability of the parameter set or common dominating measure for the parameter family is needed.

The deterministic zero path versus independent Bernoulli coordinates attains the finite and infinite product bounds for every clipped error sequence. It establishes sharpness, including infinite sequences with zero product. Constant positive step error gives whole-path TV one, so a small finite-step guarantee cannot silently become a small infinite-horizon guarantee. The note correctly treats summability as sufficient rather than necessary when budgets may be loose. A bounded-loss measurable full-path decision has discrepancy at most its loss range times TV.

## 4. What this review does and does not close

The sequential extension theorem, regularity/test characterization of TV and uniqueness on generating pi-systems are explicit mathematical prerequisites. All time indices, initial-step treatment, conditioning histories, null-set conventions and infinite product limits are accounted for. Neither result constructs unknown scientific observation laws, proves causal admissibility of a simulator, or discharges a downstream biological classification problem. The text preserves these boundaries. It also distinguishes consistent specified sequential kernels from separately available, potentially incompatible prefix simulators.

The publisher-indexed paper motivating the continuity question was not independently inspected in full here. The verdict rests on the written proof and its stated classical prerequisites, not on attributing the same theorem or hypotheses to that paper. No historical priority claim follows from this review.
