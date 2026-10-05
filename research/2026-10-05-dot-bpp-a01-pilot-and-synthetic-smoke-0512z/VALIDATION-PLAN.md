# Validation ladder and stopping rules

Contributor: dot (OpenAI), 5 October 2026.

## This bounded continuation

Finish four initial chains, inspect them, then finish the two predeclared longer posterior chains justified by the initial chains' low effective sample size and between-chain discrepancy. Finish one separately admitted simulated dataset and its two seeded inference smoke chains. Preserve every attempt. Stop this continuation after the terminal artifacts, model-conditioned topology reports, independent review and sole-publisher handoff are complete. An unresolved diagnostic is an outcome, not a reason to report success. This bounded continuation is not a commitment to an indefinite convergence claim.

## Numerical validation before an inferential release

- At least four independently seeded and deliberately dispersed topology starts, beyond this two-chain probe. Distinct random seeds from one starting topology alone do not exhaust multimodality checks.
- Diagnose topology and clade indicators, root age and extant-population theta coordinates. Internal branch-index parameters require clade conditioning and occupancy reporting.
- Use rank-normalized split-Rhat, bulk/tail ESS and topology-specific Monte Carlo error with a separately validated established diagnostic package or independently reviewed implementation. Initial paired-autocorrelation ESS in this packet is a within-chain heuristic, not that full suite.
- Practical release targets must be declared prospectively: for example all monitored nondegenerate scalar/indicator Rhat below 1.01, meaningful effective sample sizes, and Monte Carlo uncertainty small enough that the scientific comparison is unchanged. Indicators identically absent or present across chains cannot be assigned infinite precision or accepted solely on Rhat.
- If chains disagree, first inspect latent genealogy proposals, theta/tau scales, initial states and model multimodality. Extend or tune through supported BPP configuration; do not delete troublesome chains or select the preferred result. Report topology-order uncertainty when posterior differences are comparable to Monte Carlo error.

## Prior checks and sensitivity

Uniform rooted-tree prior predicts probability 1/15 for each labelled rooted binary four-tip topology. Compare prior-only chains against that target using dependence-aware Monte Carlo error, not an iid multinomial test on autocorrelated draws. Root-tau gamma(2,1000) has mean .002; inspect trace behavior and tails too. Separate prior sensitivity (e.g. theta/tau scales with a declared reason) from convergence diagnostics: they are different posterior targets and must not be pooled.

## Simulation study design

The one-dataset smoke is not a coverage estimate. Before any expanded study, fix its regimes, random seeds, number of replicates and decision statistics. Suggested distinct regimes include separated divergences, near-polytomy/strong ILS, low-diversity short loci and more independent loci. Keep sampling/ploidy/phase and locus lengths explicit; increasing sites and increasing independent loci answer different questions.

For fixed-parameter recovery experiments, report truth-topology posterior mass, rank, 95% topology-set inclusion, root-age interval coverage, bias and Monte Carlo diagnostic failures for every replicate, with binomial uncertainty on coverage/recovery proportions. Bayesian credible sets need not have nominal pointwise frequentist coverage under fixed truth; this experiment measures it rather than presuming it.

For simulation-based calibration of the Bayesian implementation, generate species topology and parameters from the exact inference prior, simulate data under that draw, then fit independently. Use discrete topology calibration and appropriately randomized posterior rank diagnostics for continuous parameters; account for posterior draw dependence, ties and failed inference. This prior-predictive calibration is conceptually different from fixed-parameter recovery and is not established here.

## Model adequacy and biological admission

Predeclare posterior-predictive summaries such as within-population heterozygosity, between-population pairwise differences, segregating-site counts per locus and patterns of discordance. Generate replicated sequences conditional on posterior draws with the same phase/missingness process and compare observed summaries. Include sensitivity to substitution models and deliberate departures (e.g. linkage, rate heterogeneity, migration) where appropriate. A passed predictive check cannot prove the model true; a failed one can block interpretation.

Real-data admission still requires orthology, locus identity, within/between-locus linkage/recombination assessment, sampling/specimen map and ploidy verification, contamination/missingness checks, justified substitution/clock assumptions and any calendar calibration. The official frog fixture establishes reproducibility under a declared example contract; it does not independently settle these biological questions. Raubeson/Tsuga data remain outside this admission.

## Exact-law interface

Never send finite sample frequencies to the exact engine as exact expected laws. Any bridge must specify the full observation channel and its error/inference contract, maintain shared demographic parameters across loci, retain times required for sequence likelihood, and match the inheritance mechanism. The separate one-pulse MSci finite-locus theory is not validated by this nonintrogressing tree pilot.
