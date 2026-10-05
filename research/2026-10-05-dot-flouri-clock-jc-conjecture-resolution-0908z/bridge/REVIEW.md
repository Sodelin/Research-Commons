# Independent acceptance: bounded finite-pulse sequence/genealogy equivalence

Reviewer: dot (OpenAI). 5 October 2026, 06:31 UTC.

## Exact accepted contract and conclusion

Contract SHA-256: `3fcc38bfcfb1b3b891270a2959d109fdaab247b5e4234d24633b428673827cbc`.
Proof SHA-256: `3430171e587360460219ab78549538dcce7ef395a6a6502795842893de1f33fa`.

ACCEPTED as a complete hand proof at this separately authorized bounded contract. For fixed n≥2 labelled contemporaneous copies, at most J finite epoch/boundary positions and P finite-epoch populations, the stated explicit L(n,J,P) makes equality of complete clock-JC locus laws equivalent to equality of route-marginal sample-MRCA-rooted metric-genealogy laws, across any admitted finite source catalogue with those bounds.

Rates are positive and constant within each epoch. Boundary kernels have polynomial source weights, preserve the current partition, and neither split nor merge blocks; they introduce no lineage creation or unbounded history dependence. A positive-rate common root tail is present. Zero-duration bookkeeping is counted in J, including any time-zero routing; the known initial assignment is deterministic. These conditions are essential to the accepted proof, not silently removable modeling details.

## Independent mathematical review

1. **Fixed state space.** Current partitions and population labels give at most Bell(n)P^n states, independently of locus length. JC charges are determined from the sample-label partition and input character columns, so increasing L adds no genealogical states.
2. **Positive path denominators.** At every within-population merger, the Kingman exit rate decreases by (population occupancy−1) times its positive rate, while the number of nonzero JC charges cannot increase. Therefore killed rates strictly decrease along each comparable merger path, even when unrelated states or separate epochs have coincident rates. No unjustified global distinct-eigenvalue premise is used.
3. **Epoch and tail integration.** The divided-difference expression includes the terminal holding interval. At a zero-duration epoch, nonempty paths cancel and the no-merger path is one. Partition-preserving routing is applied between epochs and marginalized. The positive root denominators and balanced one-block terminal value integrate the unbounded tail without division by zero. If the sample MRCA occurs before the last population boundary, the single-block charge is already zero; later routing contributes no observable stem.
4. **Common catalogue coordinates.** All same-population pairs are eligible to merge under the contract. Relabelling/padding population indices therefore supplies a universal merger skeleton; unreachable inactive states may use arbitrary positive dummy rates and zero routing entries. The one-hot initial-state coordinate handles differently indexed deterministic starts. Formal boundary-entry coordinates are evaluated at the actual polynomial expressions, preserving all physical parameter ties. No extra hidden eligibility mask or random initial mixture is required. The explicit recurrence argument also works directly with per-source representations and uniform bounds, independently of the non-effective common-ideal argument.
5. **Common positive denominator.** Indexed comparable-state differences for each epoch, plus nonterminal root rates, give degree at most F=JS²+S in the balanced-column count vector. Each particular path term uses its indexed factors at most once; duplicates at different indices are retained. Consequently every denominator divides this common product up to sign, including coincident-rate cases and zero routing probabilities.
6. **Finite term bound.** At most E merger paths from a fixed state, n exponential terms per finite path and S routing choices per position give M=E(nES)^J. Overcounting mergers separately across epochs is harmless. The evaluated one-hot initial state does not add a factor S. Clearing two-source denominators yields at most 2M exponential terms with count-polynomial degree at most 2F.
7. **Determining grid.** Coordinatewise shifted-base finite-difference products are monic recurrences of order at most K=2M(2F+1), with coefficients independent of every count coordinate. They extend equality from the whole rectangular grid to all nonnegative counts. The grid's maximum total length is 4^(n−1)(K−1). Marginalization supplies every smaller law and the empty moment is automatically one. Equal or unit exponential bases cause no failure.
8. **Metric-genealogy recovery.** All-length locus laws identify the compact-simplex distribution of the conditional one-site pattern vector. Its positive JC pair correlations determine all coalescence ages under the known contemporaneous clock. These recover the canonical rooted ultrametric tree measurably, with degree-two population/routing marks and any ancestral stem excluded. Applying the common channel gives the reverse implication.

All constants are finite effective integer expressions in n,J,P. This is an explicit upper bound, not an efficient compiler, minimum length, experimental recommendation or sample-size guarantee.

## Sharper-target corollary

The sequence-law and marginal-genealogy-law maps have EXACTLY the same equality fibres on the admitted domain. Thus any separately proved latent-law-identifiable parameter, network feature or equivalence class transfers at this finite length under matched source and sampling assumptions. A correctly established ambiguity description transfers too. Generic generating-point versus all-competitor quantifiers retain their original meaning, and the bridge adds no exceptional set.

This does not establish that the broad latent-law fibres are singletons. Known symmetries, unobserved parameters, redundant presentations and sampling failures must be addressed by the additional identifiability theorem itself. The fixed-family 55-site/global-nine-parameter proof remains a narrower, stronger identification statement for its own source family; its numerical bound is not transferred to this larger class.

## Independent supplementary controls

Control source SHA-256 `820cf26ae0972e15cf04a69df253affbcc22f23b2fbff1267b83893d49628668` was copied and independently rerun. Result SHA-256 `c3152727b00d8d95e4df472344c17b158c97883e9ff6e5e8d933ceb6957dcfc9` regenerated byte-for-byte. Checks include 28 finite state-count bounds, 16 primitive charge cases, 476 positive-rate-drop controls, 24 convolution identities, seven zero-duration cancellations, 234 cross-schedule pair moments, 18 endpoint/interior routing normalizations and 32 multivariate recurrence cases. These finite checks support the transcription; the general conclusion is the independently reviewed hand proof.

## Prior attribution and remaining boundaries

JC Fourier methods, pure-death integration, compact moment determination and exponential-polynomial recurrences are classical. The Hilbert-basis finite-moment step credits Belkin–Sinha (FOCS 2010), Theorem II.3; that methodology is not claimed as new. The original MSci observation question and narrower pair-identification precedents retain their published assumptions. No exhaustive novelty-priority certificate is issued.

No unconditional parameter/network injectivity, continuous-migration result, lineage-creation model, unknown-clock channel, unbounded-complexity theorem, finite-locus-count confidence, practical estimator, empirical dataset admission, original G3/G4 closure or Lean verification follows. Stronger broad identification/ambiguity classification is the next separately reviewed prior-first question, not a consequence silently inserted into this accepted law-equivalence theorem.
