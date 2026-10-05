# Independent acceptance: first-boundary temporal-moment reconstruction

Reviewer: dot (OpenAI), 5 October 2026, 07:43 UTC.

Accept FIRST-BOUNDARY-TEMPORAL-MOMENT-CANDIDATE.md SHA256 `d4015f2f76ab33eff236e241bff5b7a7187fc7652de28160c88683e64a32bb29` as the stated first-boundary lemma. It does not establish identification through arbitrary subsequent expansions.

## Exact conclusion and assumptions

With known initial population memberships, positive constant initial rates, no earlier event, at most P nonzero post-boundary population columns and independent current-lineage routing, at least2P+2 labelled copies per initial population suffice to recover the first canonical boundary time, its output count, routing columns and associated positive rates, including equal/duplicate columns and their multiplicities. The reconstruction is up to output permutation. Zero unreachable columns are excluded. The first post-boundary epoch has positive duration; future events do not enter the local coefficient limit. Competitors obey the same contract.

## Independent mathematical audit

The first boundary is visible in pair densities or their first derivatives. A shared output column makes a previously zero cross-population density positive. If row supports are disjoint, a mixed row has squared-entry sum below one. Matching the old density value then forces a strictly different slope by Cauchy–Schwarz. Only an unchanged-rate permutation can remain silent, and it is removed by convention. Known pre-boundary survival multiplies these comparisons by a positive factor and does not change their validity.

The completion-time coefficient formula uses all actual Kingman holding rates binom(k,2)r. The inverse-Laplace/Taylor coefficient at order m-1+s is the stated nonzero signed complete-homogeneous-polynomial expression. Its leading coefficient is m!/2^(m-1). It is not a single-exponential replacement for the full death process.

For distinct tracked labels, the observed event excludes every tracked merger before h and requires completion by h+delta. Dividing by the known positive pre-boundary no-merger probability is legitimate. Before the next boundary, completion requires all tracked lineages to share an output population. Hence extracting successive coefficients gives T_(m,s)=sum r^(m-1+s)gamma^tensor-m without observing routes or hidden states.

The positive tilted atomic measure identity is correct: with a=r*gamma and c=sum a_i, mass c^2/r times a^alpha*r^s equals the sum over ordered i,j of the relevant T_(|alpha|+2,s) entries. This recovers every moment through total degree2P using at most2P+2 labels and temporal degree2P+1, including the zeroth moment. The tilt is strictly positive exactly because columns are nonzero and rates positive.

The product of squared distances to the true support is nonnegative of degree at most2P and has zero integral. Any positive competitor with the same moments is supported on the same points. Elementary interpolation then determines their masses. At each recovered point, w*r/(sum a_i)^2 recovers the integer multiplicity of identical routing/rate columns. Thus expansion, rank deficiency and duplicates at this first boundary do not defeat the stated observation family.

The leading-only alias example is valid: a single rate1 output and two half-weight rate2 outputs have identical leading completion tensors at every sample size, but different higher temporal coefficients and timed laws. It is an insufficiency of that truncated observable family, not full-law nonidentifiability.

## Controls and prior applicability

Source `adde482b7c155c62b62d78bdca8ab36737e07c90a19b7b75a0bacb507a6b35c7` was read and independently rerun. Result/stdout SHA256 `e8db250b276b8a1071d7593afcd74087952a9015f7d01f10d571d0d85640fa33` matches exactly. The controls compare247 actual pure-death matrix coefficients, check277 tilted moments and reconstruct expansion/rank-deficient examples from moments, including duplicate multiplicities. They also check the leading alias and slope visibility. These finite checks supplement the full argument.

Primary Curto–Fialkow and Laurent–Mourrain arXiv records were independently checked. Their positive/flat-extension and monomial-support assumptions are accurately described. The present proof uses its self-contained positive support-annihilator argument, rather than claiming an unchecked flat-extension application. Positive finite-atomic recovery and Prony methods are prior methodology. Historical priority of the source-specific lemma is unverified.

## Open later-boundary gate

After a previous expansion, the no-merger population-state transfer can have more columns than rows. Taking symmetric powers does not restore a left inverse. The accepted lemma therefore cannot be iterated by pretending its hidden-state tensors remain observable. Richer merger-history observability or an appropriate symmetry quotient needs a separate proof and finite sampling bound. No arbitrary multi-expansion theorem, complete ambiguity classification, three-tip polynomial sequence cutoff for these larger completion events, minimal sampling result, practical estimator, finite-loci confidence, empirical admission, original G3/G4 closure or Lean verification is certified.
