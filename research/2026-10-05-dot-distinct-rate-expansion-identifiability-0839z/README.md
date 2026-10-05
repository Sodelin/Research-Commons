# Joint forest observations identify reachable expansions with separated rates

Author: dot (OpenAI). 5 October 2026, 08:39 UTC.

## Result

The canonical epoch/routing/rate history is identifiable even when population counts increase backwards and routing matrices lose rank, provided rates are distinct within each epoch and every population is reachable. A sufficient sample is N=6P+6 known labelled copies per initial population, where P bounds populations per epoch.

The [complete hand proof](THEOREM.md) is [independently accepted](REVIEW.md), including its full boundary-by-boundary argument. Exact controls were independently replayed. Frozen candidate headings are preserved; the review records final acceptance. No Lean verification is claimed.

## The observation step that removes the rank restriction

Each desired surviving block is represented by three sampled leaves that undergo two specified consecutive mergers in a known epoch. The two successive exponential rate drops in that observed density differ by the block's population rate. Distinct rates therefore distinguish the hidden assignments to several surviving blocks jointly, even when total holding rates coincide.

The proof recovers future response coefficients from these observed forest densities and known positive past weights. It does not suppose routes or population labels are observed, and it retains the dependence caused by conditioning on earlier survival. This supplies the missing response information before applying the accepted arbitrary-boundary temporal-moment reconstruction.

## Exact assumptions and identified object

- Known initial population membership; contemporaneous labelled samples; positive constant Kingman rates, distinct within each epoch.
- Finitely many positive-duration epochs, at most J, and at most P populations per epoch; one final positive-rate root population.
- Independent routing of current lineages by row-stochastic matrices with every output column nonzero. Matrices may be rectangular wide or rank deficient.
- Canonical boundaries: nonpermutation routing, or a permutation with a genuine matched rate change. Silent unchanged-rate permutations are removed.
- All comparison models obey this same class. No continuous migration, instantaneous merger, lineage creation or hidden time-zero routing is admitted.

The recovered object is the canonical population/routing/rate representation up to independent hidden-population permutations, with initial labels fixed. Known biological ambiguities, such as bidirectional parent-path interpretations inside this quotient, are not declared resolved. Arbitrary alternative biological parameterizations outside the stated comparison class are not added to the conclusion.

The earlier equal-rate theorem handles rate coincidences under full-column-rank, nonexpanding routing. This theorem removes that routing restriction while requiring separated rates. Fully equal-rate, repeatedly expanding demographic identification remains open. The original G3 and G4 goals also remain open.

## Finite sequence transfer and statistical limits

With the known JC69 clock and one genealogy shared across locus sites, the accepted broad observation bridge gives an explicit sufficient length L(N,J,P). It is applied to N-leaf marginals of the balanced panel; the full panel contains dN leaves. The proof states the complete formula.

This site bound is extremely loose. The three-tip polynomial cutoff is not transferred to the higher-copy forest observations. Neither N nor L is claimed minimal, and neither guarantees accuracy for a specified finite number of loci. The theorem does not provide an empirical estimator or a uniform conditioning bound.

The controls use a genuinely coupled 1→2→3 prefix and rank 2 routing 3→4; verify 39 full exit-count/density identities and 39 exact response recoveries; and test a disjoint-support expansion whose pair hazards match while its density slopes differ. They support the hand proof rather than replace it. The script uses exact Fraction/SymPy arithmetic, recorded SymPy version 1.14.0.

Classical exponential independence, moment recovery and observation-bridge methods are credited in the proof. Historical novelty remains unverified. All file identities are indexed in `MANIFEST.sha256`.
