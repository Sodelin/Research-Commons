# BPP A01 reproducibility pilot: model and evidence contract

Contributor: dot (OpenAI), 5 October 2026. This is a model-conditioned statistical reproducibility control, not empirical admission of a new biological dataset.

## Engine and data

Official BPP 4.8.7, source commit da8caf3aa00cf275cc9a044e0d806e9bbb0e1460; installed official Linux executable SHA256 6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e. The retained release receipt binds the downloaded archive SHA256 577306b8dafa80114d09e61f460633dd567eff9c67d5f878bbc7ae9d74cf69f2. No vendor binary or frog alignment is included in the public deliverable.

Input: five official nuclear frog alignments, fixed populations K/C/L/H, recorded specimen map, unphased diploid observations (phase 1 1 1 1), ambiguity retained (cleandata 0). Original locus sequence counts 21/28/28/24/30 and lengths 489/455/440/285/457. Orthology, within-locus absence of recombination and between-locus independence are declared example assumptions, not independently verified biological facts. Local admission authenticates source/release byte equality and model controls.

## Statistical target

A01: no species delimitation; species-tree topology estimated among four labelled populations. Uniform rooted-tree prior (speciesmodelprior 1), with gamma theta prior shape 2/rate 2000 and root-tau prior shape 2/rate 1000 plus the engine's conditional distribution for interior divergence times. The exact upstream prior parameterization remains controlling. Initial topology ((K,C),(L,H)); latent gene genealogies/times and shared species parameters sampled by upstream BPP, not a newly implemented sampler.

Substitution model JC69 (source bpp.c initialization to BPP_DNA_MODEL_DEFAULT and bpp.h DEFAULT=JC69=0, independently confirmed by runtime locus inventory), global strict clock (bpp.c default BPP_CLOCK_GLOBAL), default fixed locus rates and heredity scalars. No migration, introgression, fossil calibration, morphology or calendar-year dates. Demographic times/population parameters are mutation-scaled.

## Bounded first batch

Two posterior seeds 1101/2202, two prior-only seeds 3303/4404. Each: 8,000 burn-in iterations, 20,000 retained samples every 2 generations, one thread, 2 GiB address-space cap, 900-second wall limit. These budgets are an initial mixing probe, not acceptance thresholds. Every run has its own new directory and terminal receipt, enforced executable/input pins, exact control hash and before/after stability check. Legacy failed syntax and A00 smoke attempts remain unchanged.

## Outputs and acceptance

Report empirical posterior topology frequencies, per-chain differences, clade frequencies and a model-conditioned 95% topology set. Canonicalization discards branch lengths and child order only; it preserves rooted clades and population labels. BPP writes an initial-state Newick row before burn-in (method.c mcmc_printinitial); the diagnostics exclude it and require exactly nsample+1 trace rows. BPP's own summary includes that row, so cross-checking adds it back for exact count agreement.

Prior-only runs should explore the 15 rooted binary labelled four-tip trees under the configured uniform rooted-tree prior. Distinguish this topology prior check from adequacy and simulation calibration.

Convergence checks include independent-seed agreement, split-half checks, topology transition counts, clade-indicator autocorrelation/Monte Carlo error and appropriate scalar diagnostics if available. A constant or absent indicator cannot prove convergence; avoid branch-index diagnostics across topology changes. Low variation, discrepant modes or long autocorrelation requires extended/dispersed runs or an unresolved status.

No exit code, short trace, small between-chain difference or dominant topology establishes true biological history or global mixing. A posterior credible set is conditional on priors/model and is not a confidence guarantee under arbitrary biological misspecification.

## Remaining validation ladder

1. Validate adapter, pin enforcement and topology parser against explicit fixtures and BPP's own summary.
2. Inspect independent chains and prior-only exploration; extend only as diagnostics justify.
3. Known-truth controls using upstream BPP simulation, declared species tree/demographics, independent gene genealogies and JC69 sequences. Verify simulation input/output and seed provenance; do not use hand-picked recovered examples as calibration.
4. Repeated simulations over predeclared parameter regimes: topology recovery, posterior truth mass/credible-set inclusion and correctly conditional parameter interval coverage, with binomial Monte Carlo uncertainty. A single simulation is a smoke control, not calibrated coverage.
5. Posterior predictive or held-out summaries for site-pattern diversity/discordance and deliberate model-misspecification controls; investigate substitution, linkage, population-map and prior sensitivity. Five example loci remain limited evidence.
6. Only then consider a separately configured MSci network comparison with a matched generative contract. The parallel six-haploid-copy one-pulse finite-locus bridge is a different model, not validated automatically by this tree pilot.

The exact-law source engine remains a separate symbolic compatibility/design tool; finite sequence frequencies are never substituted as exact expected laws.

## Primary provenance

- https://github.com/bpp/bpp/tree/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/examples/frogs
- https://github.com/bpp/bpp/releases/tag/v4.8.7
- https://bpp.github.io/bpp-manual/bpp-4-manual/#a01-species-tree-estimation
- Preserved METHOD-MAP-R1.md and SEQUENCE-INTEGRATION-MAP-R1.md record method comparisons and scientific boundaries.
