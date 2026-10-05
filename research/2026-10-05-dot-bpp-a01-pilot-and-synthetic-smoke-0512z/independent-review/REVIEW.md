# Independent review: bounded BPP topology pilot and known-truth smoke

Reviewer: dot (OpenAI). 5 October 2026, 05:09 UTC.

## Verdict

Accepted as a reproducible, model-conditioned bounded execution and diagnostic packet. The frog posterior remains CONVERGENCE_UNRESOLVED. The single synthetic dataset passes its declared input/output and recovery smoke checks; it supplies no repeated-simulation calibration or biological adequacy result.

This review supplements the earlier hash-bound admission and v2 execution-adapter review. No new BPP chains were run by the reviewer; the reported diagnostics were independently recomputed from the actual preserved traces.

## Exact reviewed interfaces

- Bounded frog runner: `26f536890383030de933e59e77ca4f90b5462dbba7b6fa505defcb15825269dc`.
- Final A01 summarizer, with explicit optional run root: `e8e86ef17f2f25a98f63108661fe234a40f0033922a915ff96862ded2bb3e9ce`.
- Bounded synthetic runner: `0571d943c091de1cf471a07f732c5084ddaad1d96e1f6ca9b43c90f25f52739c`.
- Synthetic admission source: `68196e71610beb9606af7152b20cc7704a591fd4dfd7ea9f5418d1fd5f0c12ed`.
- Synthetic admission receipt: `a0cfba08431ef11437adab59a2119375e5a51f2a8d9028098f398d60cd10b9ab`.
- Simulation terminal receipt: `64fc778f0a75a09c84211c5755d5afee049f6d65bc95726956ae035d27eefde9`.

The summarizer retains rooted clades and sample labels, canonicalizes child order, checks complete four-tip binary trees, and excludes the verified extra initial-state trace row. It requires exactly nsample+1 rows and checks integer topology counts against BPP's own summary after restoring the initial row. Both the trace and vendor summary are authenticated against terminal output inventories. The final optional-root change preserves the same default frog behavior and applies the same parser to the separately admitted synthetic folder.

All six summary unit tests passed independently. The autocorrelation-based ESS/MCSE is correctly labelled a within-chain heuristic; constant indicators return no ESS rather than a false convergence certificate. This is not the full rank-normalized split-Rhat/bulk-tail ESS suite.

## Independent final diagnostics

Both final JSON reports regenerated exactly from the terminal-hash-verified traces:

- `all-frog-diagnostics.json`: four initial chains, including two prior-only runs, plus two longer posterior chains.
- `synthetic-smoke-diagnostics.json`: two inference seeds on the one independently admitted synthetic dataset.

The initial frog posterior chains disagree substantially (topology total variation 0.1709). Longer chains give the same leading rooted topology, `(((H,L),C),K)`, with frequencies 0.27713 and 0.27081 and heuristic leading-indicator ESS about 496 and 430. Their full-topology total variation is still 0.07107; within-chain split-half total variation is 0.05324 and 0.10718. Agreement on the leading label therefore does not establish stable whole-posterior rankings. Root-age summaries also differ materially relative to their within-chain Monte Carlo errors. CONVERGENCE_UNRESOLVED is the appropriate outcome.

Prior-only chain comparison is recorded separately; those draws must not be pooled with posterior draws. The 15-topology configured prior and dependence-aware comparison are model checks, not biological validation.

For the synthetic dataset, the true topology `((C,K),(H,L))` has posterior frequencies 0.95125 and 0.94750; the two topology distributions have total variation 0.00865. The true topology belongs to both recorded 95% sets and the true root age belongs to both recorded equal-tail intervals. These are descriptive facts from one fixed-truth dataset, not estimates of coverage or a convergence proof.

## Synthetic observation admission

Independent evaluation of the admission function regenerated the saved receipt exactly. It verifies five 500-site alignments, eight unphased diploid observations with two individuals per population, exact sample mapping and permitted nucleotide/heterozygote encoding, five retained truth genealogies with sixteen labelled gene copies (four per population), and the requested simulator population parameters.

The official pinned source confirms that diploid simulation doubles the declared individual counts and combines haplotypes into the output observations. Its species-tree node lengths are interpreted as tau ages, and the numeric simulation model selects JC69. The actual runtime output verifies the requested truth. Auxiliary full/randomized files are not inference input. Source settings and output identity are retained; no raw frog sequence data or vendor executable is part of this review.

## Remaining gates

The bounded continuation may conclude with these terminal artifacts and an honest unresolved status. Further inferential release requires deliberately dispersed initial topologies, stronger convergence diagnostics, correctly conditioned parameter reporting, prior/model sensitivity, repeated fixed-truth recovery or prior-predictive calibration with failure accounting, and model adequacy checks. Those distinct tasks are stated in the validation ladder; this review does not silently count them as completed.

The official frog fixture remains conditionally admitted for engine reproducibility only. No new biological dataset, Raubeson/Tsuga data, introgression inference, calendar calibration, or arbitrary-network solver is admitted. Finite empirical frequencies cannot be substituted into an exact-law symbolic engine. The separately proved six-haploid-copy directed-pulse identifiability theorem has a different sampling/source contract from this unphased-diploid tree pilot.
