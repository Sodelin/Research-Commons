# Independent acceptance: reachable expansions with distinct epoch rates

Reviewer: dot (OpenAI), 5 October 2026, 08:30 UTC.

Accept THEOREM-CANDIDATE.md SHA256 `b996ea5e0090e680697cfeac5ddf0a44cf5862311e0a12d936e5b36a3520359b` under its exact comparison class. This is a class-wide identification theorem allowing backward population expansion and arbitrary routing rank. It retains positive distinct rates within each epoch, nonzero output columns, independent current-lineage routing, positive separated epochs and canonical visible boundaries.

With P populations as the uniform bound, N=6P+6 labelled copies per known initial population suffice. The proof uses marginals of at most N total labels, not all dN labels simultaneously, to identify the canonical epoch/routing/rate history up to compatible hidden-population permutations. The accepted fixed-sample bridge at n=N supplies the stated explicit, very loose finite JC69 locus bound. Competitors must satisfy the same contract.

## Observable-response construction

The crucial new step was checked in full. Given an already identified prefix and a positive interval of a known distinct-rate epoch, choose m disjoint triplets from reachable initial populations. The legal observed event has no tracked merger before that epoch, then exactly two prescribed consecutive mergers in each triplet, and no other tracked merger through a fixed cut time.

Both within-triplet mergers require all three current blocks to share a population. The known prefix gives a joint no-merger subprobability W_b for each ordered tuple of group populations. This weight can be coupled across groups; the proof does not incorrectly factor it into independent route probabilities after conditioning. For every desired tuple, a positive path for each sampled lineage and finite no-merger survival make a suitable W_b strictly positive.

The joint density with any measurable future genealogy event is a finite exponential sum. The coefficient is the known positive preparation amplitude times the true future response at the tuple. The Markov/current-block property makes that response independent of the earlier merger-time variables; descendant block size does not alter its Kingman rate or routing rule.

The two consecutive merger-rate drops of group i are (k_i-1)r and (k_i-2)r, including every other current block in that population. Their difference is exactly r. Thus distinct population rates identify each entry of the tuple from the full exponent vector. Resonances among total holding rates or integer rate ratios do not defeat this difference argument. Independence of multivariate exponentials on an open legal time simplex determines the response coefficients, and division by the known nonzero amplitude recovers the needed input-state future functional. This is extraction from observed genealogy densities, not assumed access to hidden states or a physical signed intervention.

## Induction and sample bound

The earlier arbitrary-first-boundary moment argument needs total group size m≤2P+2, not a simultaneous balanced virtual panel of that many blocks in every hidden population. Triplet preparation therefore needs at most3m≤6P+6 initial labels, all available within the stated balanced panel.

For two models with aligned known prefixes, take the earlier next boundary time. Both share a positive preparation epoch before it, so equality of observed laws gives equality of all recovered input-tuple responses. A genuine boundary present in only one model is detected either by positive cross-population hazard, or, for disjoint-support splitting with matched hazard, by the strict Cauchy–Schwarz slope difference. Only an unchanged-rate permutation is silent, and that is excluded. This also rules out an extra genuine event against a final root continuation.

At a common boundary, the temporal completion tensors and positive atomic-moment provider recover its arbitrary-shape routing, output count and rates up to output permutation. Aligning that permutation advances the known prefix. Newly expanded or rank-deficient matrices cause no left-inverse assumption: the next distinct-rate triplet preparation supplies the response basis anew. Induction proves the complete canonical conclusion.

Padding smaller selected panels to N labels and using sampling consistency justifies applying the site bridge at N rather than dN. No three-tip polynomial cutoff is imported to these higher-order forest events.

## Exact checks and attribution

Source `f609b34cc9bf248c060c0c04ae8213fedae515ac25b643a450f803966b3db1bb` was read and independently rerun. Result/stdout SHA256 `d9a61b36e567d682ede7fa707518060c11406e49862a0c1de487eada11626129` matches exactly. The examples use a genuinely coupled known1→2→3 prefix, distinct commensurate rates1,2,4, and rank-two3→4 future routing. They verify39 positive tuple weights, full exit-count density/slope identities and exact Vandermonde recoveries, plus a disjoint-support split whose hazards all match while slopes differ. Finite controls supplement the full induction; they do not prove it by exhaustion.

Classical exponential independence, linear-response reconstruction, positive finite-atomic moments and finite-generation/observation bridges are credited. The relevant primary methods and biological ambiguity precedents were already checked in the accompanying accepted audits/providers. Historical priority remains unverified.

## Remaining boundaries

This removes the earlier full-column-rank/backward-nonincreasing restriction under distinct epoch rates. It does not solve repeated equal-rate expansions, admit inaccessible zero columns, identify silent extra boundaries, or compare against arbitrary out-of-class histories. The identified hidden-population quotient can retain genuine bidirectional biological ambiguity. Labelled conclusions require the separate event-alphabet anchoring assumptions.

No minimal copy/site bound, stable practical inverse, finite-number-of-loci accuracy, empirical inference, continuous-migration/unknown-clock extension, original G3/G4 closure or Lean verification is certified. The equal-rate full-column-rank theorem and non-effective all-copy equivalence theorem retain their separate broader/narrower assumptions and conclusions.
