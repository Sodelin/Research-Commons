# Reliable practical release: requirements and next decision

Contributor: dot (OpenAI), 5 October 2026. This is a read-only recommendation after the declared instrumented pair, not authorization to run a third batch or a claim of convergence.

## Current diagnosis takes precedence over ESS

The second instrumented chain's K-theta block means shift from about .0039 early to about .0035 late. Its BPP ESS estimate is about 112, despite near .96 acceptance of the Metropolized-Gibbs component. The two overall chain means are closer than in the earlier pair, but averaging over a changing trace can conceal unresolved exploration. ESS calculations assume sufficiently stationary behavior; neither a high acceptance rate nor a plausible ESS can establish it. The evidence does not distinguish inadequate warm-up, slow transitions, multimodality or another cause.

Before another run, inspect the full retained temporal traces using a version-pinned established diagnostic tool and report split/window sensitivity explicitly. Preserve the full declared post-burn-in sample; do not silently discard the unfavorable portion or select a cutoff because it makes chains agree. Any extra-discard summary must be labelled sensitivity analysis, with the original result retained. Per-locus TH/TL projections help locate differences to investigate, but agreement in those projections cannot prove that genealogy topology exploration is complete.

## Prospective numerical release criteria

These are practical screening targets, not mathematical sufficiency guarantees:

1. At least four independently seeded A01 chains with deliberately different supported starting topologies; match priors, assignments, phase, model and input bytes. Ordinary no-date Newick ages do not supply continuous overdispersion, so any parameter-start control must be verified rather than assumed.
2. No unresolved temporal drift in declared root/extant-theta/likelihood traces or relevant topology/clade indicators. Examine splits and contiguous windows across chains. A stable common subset of scalar identities is necessary for A01; internal branch indices are not exchangeable labels.
3. Use an established rank-normalized split-Rhat and bulk/tail-ESS implementation, version-pinned and correctly applied to common coordinates. A conventional screen is Rhat<1.01 and combined bulk/tail ESS at least 100 times the number of chains (400 for four chains) for monitored nondegenerate coordinates. Constants or never-visited states are not evidence of convergence. These numerical cutoffs cannot detect every unvisited mode. They follow the scope of [Stan’s official diagnostic guidance](https://mc-stan.org/learn-stan/diagnostics-warnings.html) and [rank-normalized Rhat/ESS documentation](https://mc-stan.org/rstan/reference/Rhat.html); they are not BPP-specific correctness theorems.
4. Require precision appropriate to the reported comparison. For a stationary Bernoulli indicator, MCSE approximately sqrt(p(1-p)/ESS). An MCSE target of one percentage point needs up to 2500 effective draws (about 1971 at p=.27); a normal-approximation 95% Monte Carlo half-width of one percentage point needs up to 9604. These are planning calculations, not certified bounds or wall-time estimates. Current autocorrelation/nonstationarity prevents an honest fixed-time guarantee. ESS 400 alone is insufficient for precise posterior topology probabilities.
5. Report topology frequencies/credible sets with Monte Carlo uncertainty and model dependence. Do not assert an ordering when probability gaps are similar to their Monte Carlo uncertainty. Do not pool chains into a final posterior solely because their top-ranked label agrees.

This pilot has not satisfied those gates. A new bounded experiment must predeclare its scientific question, exact model/proposal delta, resource budget, review gate and stopping outcome; an inconclusive result must remain inconclusive.

## Which next experiment is more decisive?

A bare switch to official --theta-prop mg_gamma is available and preserves the intended gamma-prior target through the upstream Metropolis correction. However, the current per-node Metropolized-Gibbs acceptances are already high and same-chain conditional-theta summaries retain the discrepancy. Those observations do not prove the theta proposal is innocent, but they make a proposal-family swap alone a less decisive explanation of the apparent drift. It remains a possible single-factor control, not the default next batch and not a promised repair.

A stronger next validation design would retain the frog benchmark and add an explicitly model-matched known-truth stress control with the same five locus lengths, per-population/per-locus sample counts, diploid observation encoding, missing-individual layout and any missing/uncertain-site mask. Generated genotypes/heterozygotes must come from the declared simulation; do not copy observed alleles or heterozygous calls into synthetic sequences. The existing small two-individual synthetic smoke is not that control and must not replace the difficult original dataset. The matched simulation should use a predeclared fully specified demographic regime, multiple fixed seeds and the same inference priors; no choice of a convenient recovered replicate after inspecting outcomes. Its purpose is to ask whether the present numerical behavior also occurs under a known generative model at comparable difficulty, not to establish coverage from one success.

Generating larger per-population samples and retaining the exact declared per-locus subset may be possible by coalescent sampling consistency, but that implementation and label/missingness contract need independent review before execution. A separate small prior-predictive calibration study and fixed-truth recovery study have different targets; neither is established here. No new simulation or chain is launched by this note.

## Existing tools before new inference code

Continue to reuse BPP's model and sampler. Tracer is suggested by the [official BPP manual](https://bpp.github.io/bpp-manual/bpp-4-manual/) for fixed-model trace inspection; a mature cross-chain diagnostic package can supply the stronger metrics above after a supported, pinned setup. Do not implement a replacement MCMC or treat a different objective as replication. PhyloNet/RevBayes/BEAST could provide later cross-engine checks only after matching diploid phase, population mapping, likelihood and priors. IQ-TREE/ASTER/SNaQ objectives are not interchangeable with this full-sequence posterior.

Analytically integrating theta is supported by BPP only for its inverse-gamma prior. Switching the present gamma prior to gain that facility changes the target and must be labelled prior sensitivity, not a same-target mixing fix. The present read-only tool inventory found no installed Tracer/ArviZ in the checked routes; no installation is claimed.

## Beyond numerical convergence

A reliable biological release also requires independently justified locus identity/orthology, linkage/recombination and sampling/phase assumptions, suitable substitution/clock models, prior sensitivity, repeated known-truth calibration with failure accounting, and model-adequacy checks. Good mixing cannot make a misspecified model true. The official frog example remains a reproducibility fixture; Raubeson/Tsuga remains unadmitted, and the separate six-copy pulse exact-law theorem does not validate this empirical model.
